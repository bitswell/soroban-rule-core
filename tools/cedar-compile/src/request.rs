use crate::{ArgumentType, Compiled, Error, Result};
use cedar_policy::{Authorizer, Context as CedarContext, Decision, Entities, EntityUid, Request};
use rule_eval::{Context, Signer, Val};
use serde_json::{Value, json};

#[derive(Debug, PartialEq, Eq)]
pub struct Comparison {
    pub cedar: bool,
    pub rule_core: bool,
}
fn entity_json(uid: &str) -> Value {
    let parsed: EntityUid = uid.parse().expect("validated binding");
    let id: &str = parsed.id().as_ref();
    json!({"__entity":{"type":parsed.type_name().to_string(),"id":id}})
}
impl Compiled {
    /// Checked, single-principal eligibility comparison, NOT account authorization.
    /// `entry` MUST be the current account's host-authenticated entry, root first;
    /// `signer` MUST already be authenticated. Neither fact is established here.
    /// There is deliberately no caller-supplied root/context JSON parameter.
    /// Call rule_eval::authorize separately for selected rules, caps and state.
    pub fn compare(&self, entry: &[Context], index: usize, signer: &Signer) -> Result<Comparison> {
        let request = self.request(entry, index, signer)?;
        let response = Authorizer::new().is_authorized(&request, &self.source, &Entities::empty());
        if response.diagnostics().errors().next().is_some() {
            return Err(Error(
                "reference Cedar evaluation errored inside the checked domain".into(),
            ));
        }
        let ctx = &entry[index];
        Ok(Comparison {
            cedar: response.decision() == Decision::Allow,
            rule_core: self.rules.iter().any(|r| {
                rule_eval::rule_allows_in(r, entry.first(), ctx, std::slice::from_ref(signer))
            }),
        })
    }
    /// Builds reference facts from the same typed call and entry root consumed by
    /// rule-core. Err is an input-domain refusal, not a Cedar evaluation result.
    pub fn request(&self, entry: &[Context], index: usize, signer: &Signer) -> Result<Request> {
        if entry.is_empty() || entry.len() > 32 {
            return Err(Error(
                "request requires 1..32 contexts in ONE authenticated entry".into(),
            ));
        }
        let Context::Call {
            contract: root_contract,
            function: root_function,
            ..
        } = &entry[0]
        else {
            return Err(Error(
                "creation root is outside the checked request domain".into(),
            ));
        };
        let root_entity = self
            .bindings
            .entities
            .iter()
            .find(|e| e.address.xdr() == *root_contract)
            .ok_or_else(|| Error("entry root address has no entity binding".into()))?;
        if !matches!(root_entity.address, crate::Address::Contract(_)) {
            return Err(Error("entry root must be a contract address".into()));
        }
        let root_function = std::str::from_utf8(root_function)
            .ok()
            .filter(|s| crate::bindings::symbol(s))
            .ok_or_else(|| Error("entry root function is not a valid symbol".into()))?;
        let Some(Context::Call {
            contract,
            function,
            args,
        }) = entry.get(index)
        else {
            return Err(Error("current context missing or a creation".into()));
        };
        let call = self
            .bindings
            .calls
            .iter()
            .find(|c| {
                self.bindings
                    .entity(&c.resource)
                    .expect("validated binding")
                    .address
                    .xdr()
                    == *contract
                    && c.function.as_bytes() == function
            })
            .ok_or_else(|| Error("current contract/function has no call binding".into()))?;
        let principal = self
            .bindings
            .principals
            .iter()
            .find(|p| rule_eval::signer_eq(&p.signer.to_signer(), signer))
            .ok_or_else(|| Error("authenticated signer has no principal binding".into()))?;
        if args.len() != call.arguments.len() {
            return Err(Error(
                "argument arity differs from the typed call binding".into(),
            ));
        }
        let mut context = serde_json::Map::new();
        for (arg, binding) in args.iter().zip(&call.arguments) {
            let value = match (arg, binding.kind) {
                (Val::I128(n), ArgumentType::Integer) => {
                    json!(i64::try_from(*n).map_err(|_| Error(format!(
                        "{}: i128 outside checked Cedar i64 domain",
                        binding.name
                    )))?)
                }
                (Val::Address(a), ArgumentType::Address) => {
                    let e = self
                        .bindings
                        .entities
                        .iter()
                        .find(|e| e.address.xdr() == *a)
                        .ok_or_else(|| {
                            Error(format!("{}: address has no entity binding", binding.name))
                        })?;
                    entity_json(&e.uid)
                }
                (Val::String(s), ArgumentType::String) => json!(
                    std::str::from_utf8(s)
                        .ok()
                        .filter(|s| s.len() <= 256)
                        .ok_or_else(|| Error(format!(
                            "{}: expected UTF-8 string <=256 bytes",
                            binding.name
                        )))?
                ),
                (Val::Bool(b), ArgumentType::Bool) => json!(b),
                _ => {
                    return Err(Error(format!(
                        "{}: wrong Soroban value constructor",
                        binding.name
                    )));
                }
            };
            context.insert(binding.name.clone(), value);
        }
        context.insert("authRootContract".into(), entity_json(&root_entity.uid));
        context.insert("authRootFunction".into(), json!(root_function));
        let context = CedarContext::from_json_value(Value::Object(context), None)
            .map_err(|e| Error(format!("Cedar request context: {e}")))?;
        Request::new(
            principal.uid.parse().unwrap(),
            call.action.parse().unwrap(),
            call.resource.parse().unwrap(),
            context,
            None,
        )
        .map_err(|e| Error(format!("Cedar request: {e}")))
    }
}
