use crate::{
    Address, ArgumentType, Bindings, CallBinding, Compiled, Error, MAX_RANGE_VALUES, Result,
};
use cedar_policy::PolicySet;
use rule_eval::{AuthRoot, Cap, Cond, Functions, Rule, Val};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn compile(source: &str, bindings: Bindings) -> Result<Compiled> {
    bindings.validate()?;
    if source.len() > 16_384 {
        return Err(Error("Cedar source exceeds 16384 bytes".into()));
    }
    let parsed: PolicySet = source
        .parse()
        .map_err(|e| Error(format!("Cedar parse: {e}")))?;
    if parsed.templates().next().is_some() {
        return Err(Error("templates/slots are unsupported".into()));
    }
    let mut policies: Vec<_> = parsed.policies().collect();
    policies.sort_by_key(|p| p.id().to_string());
    let ids: Vec<_> = policies.iter().map(|p| p.id().to_string()).collect();
    if ids.iter().collect::<BTreeSet<_>>()
        != bindings
            .policies
            .iter()
            .map(|p| &p.id)
            .collect::<BTreeSet<_>>()
    {
        return Err(Error("policy IDs must exactly match bindings.policies; extra/missing policies reject the entire set".into()));
    }
    let mut rules = Vec::new();
    for policy in policies {
        let id = policy.id().to_string();
        let result = (|| {
            if policy.annotations().next().is_some() {
                return Err(Error(
                    "annotations are unsupported (none are silently discarded)".into(),
                ));
            }
            let est = policy
                .to_json()
                .map_err(|e| Error(format!("Cedar EST conversion: {e}")))?;
            if est["effect"] != "permit" {
                return Err(Error(
                    "only permit is supported; forbid cannot be dropped".into(),
                ));
            }
            let principal = head(&est["principal"])?;
            let action = head(&est["action"])?;
            let resource = head(&est["resource"])?;
            let signer = bindings
                .principals
                .iter()
                .find(|p| p.uid == principal)
                .ok_or_else(|| Error(format!("missing principal binding for {principal}")))?;
            let call = bindings
                .calls
                .iter()
                .find(|c| c.action == action && c.resource == resource)
                .ok_or_else(|| Error(format!("missing call binding for {action} on {resource}")))?;
            let options = bindings.policies.iter().find(|p| p.id == id).unwrap();
            let mut lowering = Lowering {
                bindings: &bindings,
                call,
                conds: Vec::new(),
                ranges: BTreeMap::new(),
                guarded: BTreeSet::new(),
                root_contract: None,
                root_function: None,
                nodes: 0,
            };
            let conditions = est["conditions"]
                .as_array()
                .ok_or_else(|| Error("missing Cedar conditions".into()))?;
            if conditions.len() > 1 {
                return Err(Error("at most one when clause is supported".into()));
            }
            for clause in conditions {
                if clause["kind"] != "when" {
                    return Err(Error("unless is unsupported".into()));
                }
                lowering.expression(&clause["body"], 0)?;
            }
            let (conds, auth_root) = lowering.finish()?;
            let cap = options
                .cap
                .as_ref()
                .map(|c| {
                    let index = call
                        .arguments
                        .iter()
                        .position(|a| a.name == c.amount && a.kind == ArgumentType::Integer)
                        .ok_or_else(|| {
                            Error(format!(
                                "cap amount {} must bind an integer argument",
                                c.amount
                            ))
                        })?;
                    Ok(Cap {
                        amount_arg: index as u32,
                        limit: i128::from(c.limit),
                        period: c.period,
                    })
                })
                .transpose()?;
            Ok(Rule {
                contract: bindings.entity(&resource)?.address.xdr(),
                functions: Functions::Only(vec![call.function.as_bytes().to_vec()]),
                conds,
                signers: vec![signer.signer.to_signer()],
                threshold: 1,
                cap,
                valid_until: options.valid_until,
                generation: options.generation,
                auth_root,
            })
        })();
        rules.push(result.map_err(|e: Error| Error(format!("{id}: {e}")))?);
    }
    Ok(Compiled {
        source: parsed,
        bindings,
        ids,
        rules,
    })
}
fn entity(v: &Value) -> Result<String> {
    let t = v["type"]
        .as_str()
        .ok_or_else(|| Error("expected an entity literal".into()))?;
    let id = v["id"]
        .as_str()
        .ok_or_else(|| Error("expected an entity literal ID".into()))?;
    Ok(format!("{t}::{}", serde_json::to_string(id).unwrap()))
}
fn head(v: &Value) -> Result<String> {
    if v["op"] != "==" || v.as_object().map(|m| m.len()) != Some(2) {
        return Err(Error("heads require explicit principal/action/resource == Entity literals; no wildcard, hierarchy, is or slots".into()));
    }
    entity(&v["entity"])
}
fn attribute(v: &Value) -> Result<&str> {
    if v["."]["left"] != serde_json::json!({"Var":"context"}) {
        return Err(Error(
            "left operand must be a direct context.field binding".into(),
        ));
    }
    v["."]["attr"]
        .as_str()
        .ok_or_else(|| Error("expected context.field".into()))
}
fn integer(v: &Value) -> Result<i64> {
    if let Some(n) = v["Value"].as_i64() {
        return Ok(n);
    }
    // Cedar EST preserves a textual negative literal as neg(Value); do not
    // accept general arithmetic. i128 intermediate handles -2^63 exactly.
    if let Some(n) = v["neg"]["arg"]["Value"].as_u64() {
        return i64::try_from(-i128::from(n))
            .map_err(|_| Error("integer literal outside Cedar i64".into()));
    }
    Err(Error(
        "expected a literal Cedar i64 integer (no arithmetic/extensions)".into(),
    ))
}
struct Lowering<'a> {
    bindings: &'a Bindings,
    call: &'a CallBinding,
    conds: Vec<Cond>,
    ranges: BTreeMap<usize, (i128, i128)>,
    guarded: BTreeSet<usize>,
    root_contract: Option<Vec<u8>>,
    root_function: Option<Vec<u8>>,
    nodes: usize,
}
impl Lowering<'_> {
    fn expression(&mut self, value: &Value, depth: usize) -> Result<()> {
        self.nodes += 1;
        if depth > 32 || self.nodes > 127 {
            return Err(Error(
                "condition exceeds depth 32 / 127 expression nodes".into(),
            ));
        }
        let map = value
            .as_object()
            .ok_or_else(|| Error("unsupported condition".into()))?;
        if map.len() != 1 {
            return Err(Error("unsupported expression shape".into()));
        }
        let (op, args) = map.iter().next().unwrap();
        if op == "&&" {
            self.expression(&args["left"], depth + 1)?;
            return self.expression(&args["right"], depth + 1);
        }
        if !["==", "<=", ">=", "<", ">"].contains(&op.as_str()) {
            return Err(Error(format!(
                "unsupported operator {op}; only conjunction and literal comparisons are accepted"
            )));
        }
        let name = attribute(&args["left"])?;
        let right = &args["right"];
        if name == "authRootContract" {
            if op != "==" || self.root_contract.is_some() {
                return Err(Error("root contract requires one exact equality".into()));
            }
            let e = self
                .bindings
                .entity(&entity(&right["Value"]["__entity"])?)?;
            if !matches!(e.address, Address::Contract(_)) {
                return Err(Error("root must name a contract".into()));
            }
            self.root_contract = Some(e.address.xdr());
            return Ok(());
        }
        if name == "authRootFunction" {
            let function = right["Value"]
                .as_str()
                .ok_or_else(|| Error("root function must be a literal string".into()))?;
            if op != "==" || self.root_function.is_some() || !crate::bindings::symbol(function) {
                return Err(Error(
                    "root function requires one exact symbol equality".into(),
                ));
            }
            self.root_function = Some(function.as_bytes().to_vec());
            return Ok(());
        }
        let (index, arg) = self
            .call
            .arguments
            .iter()
            .enumerate()
            .find(|(_, a)| a.name == name)
            .ok_or_else(|| Error(format!("context.{name} has no argument binding")))?;
        self.guarded.insert(index);
        if arg.kind == ArgumentType::Integer {
            let n = i128::from(integer(right)?);
            let range = self
                .ranges
                .entry(index)
                .or_insert((i128::from(i64::MIN), i128::from(i64::MAX)));
            match op.as_str() {
                "==" => {
                    range.0 = range.0.max(n);
                    range.1 = range.1.min(n);
                }
                "<=" => range.1 = range.1.min(n),
                ">=" => range.0 = range.0.max(n),
                "<" => range.1 = range.1.min(n - 1),
                ">" => range.0 = range.0.max(n + 1),
                _ => unreachable!(),
            }
        } else {
            if op != "==" {
                return Err(Error(format!(
                    "context.{name}: non-integers require exact equality"
                )));
            }
            let val = match arg.kind {
                ArgumentType::Address => Val::Address(
                    self.bindings
                        .entity(&entity(&right["Value"]["__entity"])?)?
                        .address
                        .xdr(),
                ),
                ArgumentType::String => Val::String(
                    right["Value"]
                        .as_str()
                        .filter(|s| s.len() <= 256)
                        .ok_or_else(|| Error("expected string literal <=256 bytes".into()))?
                        .as_bytes()
                        .to_vec(),
                ),
                ArgumentType::Bool => Val::Bool(
                    right["Value"]
                        .as_bool()
                        .ok_or_else(|| Error("expected bool literal".into()))?,
                ),
                ArgumentType::Integer => unreachable!(),
            };
            self.conds.push(Cond::ArgEq(index as u32, val));
        }
        Ok(())
    }
    fn finish(mut self) -> Result<(Vec<Cond>, Option<AuthRoot>)> {
        if self.guarded.len() != self.call.arguments.len() {
            return Err(Error("every declared argument must have a guard; no unchecked argument may widen the emitted rule".into()));
        }
        for (index, (lo, hi)) in self.ranges {
            if lo > hi || hi - lo + 1 > MAX_RANGE_VALUES {
                return Err(Error(format!(
                    "context.{}: require a nonempty closed i64 range of at most {MAX_RANGE_VALUES} values; wider/unbounded ranges cannot be represented faithfully",
                    self.call.arguments[index].name
                )));
            }
            if lo == hi {
                self.conds.push(Cond::ArgEq(index as u32, Val::I128(lo)));
            } else {
                self.conds.push(Cond::ArgIn(
                    index as u32,
                    (lo..=hi).map(Val::I128).collect(),
                ));
            }
        }
        let root = match (self.root_contract, self.root_function) {
            (None, None) => None,
            (Some(contract), Some(function)) => Some(AuthRoot { contract, function }),
            _ => {
                return Err(Error(
                    "root restriction requires BOTH authRootContract and authRootFunction".into(),
                ));
            }
        };
        Ok((self.conds, root))
    }
}
