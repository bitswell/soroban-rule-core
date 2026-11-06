mod common;
use cedar_policy::{Authorizer, Context, Decision, Entities, PolicySet, Request};
use cedar_to_rule_core::{ArgumentType, Bindings, PolicyBinding, compile};
use common::*;
use serde_json::json;

fn rejects(source: &str, needle: &str) {
    let err = compile(source, bindings())
        .err()
        .expect("unsupported source was accepted");
    assert!(err.0.contains(needle), "expected {needle:?}, got {err}");
}
#[test]
fn unsupported_constructs_reject_the_whole_set() {
    let cases = [
        (
            "context.amount >= 0",
            "context.amount != 0",
            "unsupported operator !=",
        ),
        (
            "context.amount >= 0",
            "context.amount in [0, 1]",
            "unsupported operator in",
        ),
        (
            "context.amount >= 0",
            "context.amount + 1 >= 0",
            "direct context.field",
        ),
        (
            "context.amount >= 0",
            "context.amount >= decimal(\"0\")",
            "literal Cedar i64",
        ),
        (
            "context.amount >= 0",
            "context has amount",
            "unsupported operator has",
        ),
        (
            "context.amount >= 0",
            "!(context.amount < 0)",
            "unsupported operator !",
        ),
        (
            "context.amount >= 0 && context.amount <= 100",
            "context.amount == 1 || context.amount == 2",
            "unsupported operator ||",
        ),
        (
            "context.amount >= 0",
            "context.missing == 0",
            "no argument binding",
        ),
        (
            "context.amount >= 0",
            "principal.age >= 0",
            "direct context.field",
        ),
        (
            "context.amount >= 0",
            "context.amount >= 9223372036854775808",
            "Cedar parse",
        ),
        (
            "context.amount >= 0",
            "context.amount >= -9223372036854775809",
            "Cedar parse",
        ),
        (
            "context.amount >= 0",
            "context.amount >= true",
            "literal Cedar i64",
        ),
        (
            "context.amount >= 0",
            "context.amount >= 101",
            "nonempty closed i64 range",
        ),
        (
            "context.amount <= 100",
            "context.amount <= 256",
            "at most 256 values",
        ),
        ("context.amount >= 0 && ", "", "at most 256 values"),
        (
            "context.authRootFunction == \"guess\"",
            "context.authRootFunction == \"\"",
            "exact symbol equality",
        ),
        (
            "context.authRootContract == Contract::\"game\" &&",
            "",
            "BOTH",
        ),
        (
            "context.from == Account::\"alice\" &&",
            "",
            "every declared argument",
        ),
        (
            "resource == Contract::\"xlm\"",
            "resource in Contract::\"xlm\"",
            "heads require explicit",
        ),
        (
            "action == Action::\"transfer\"",
            "action in [Action::\"transfer\"]",
            "heads require explicit",
        ),
        (
            "principal == Signer::\"session\"",
            "principal",
            "heads require explicit",
        ),
        ("when { context.guess", "unless { context.guess", "unless"),
    ];
    for (before, after, needle) in cases {
        rejects(&SOURCE.replace(before, after), needle);
    }
    rejects(&format!("@audit(\"do not drop\")\n{SOURCE}"), "annotations");
    rejects(
        &SOURCE.replace(
            "principal == Signer::\"session\"",
            "principal == ?principal",
        ),
        "templates/slots",
    );
    rejects("not Cedar", "Cedar parse");
    rejects("", "policy IDs");
    rejects(
        &format!("{SOURCE}\npermit(principal,action,resource);"),
        "extra/missing policies",
    );
    rejects(
        &SOURCE.replace("Contract::\"xlm\"", "Contract::\"unbound\""),
        "missing call binding",
    );
    let supported = SOURCE.replace("context.amount <= 100", "context.amount <= 255");
    assert!(compile(&supported, bindings()).is_ok());
    println!("source rejection cases: 28; maximum accepted interval: 256 values");
}

#[test]
fn bindings_are_explicit_injective_typed_and_complete() {
    let mut variants = Vec::new();
    let mut b = bindings();
    b.principals.clear();
    variants.push(b);
    let mut b = bindings();
    b.principals.push(b.principals[0].clone());
    variants.push(b);
    let mut b = bindings();
    b.principals[1].signer = b.principals[0].signer.clone();
    variants.push(b);
    let mut b = bindings();
    b.entities[1].address = b.entities[0].address.clone();
    variants.push(b);
    let mut b = bindings();
    b.entities.remove(0);
    variants.push(b);
    let mut b = bindings();
    b.calls.push(b.calls[0].clone());
    variants.push(b);
    let mut b = bindings();
    b.calls[1].arguments[2].name = "from".into();
    variants.push(b);
    let mut b = bindings();
    b.calls[1].arguments[2].name = "authRootFunction".into();
    variants.push(b);
    let mut b = bindings();
    b.calls[1].arguments[2].kind = ArgumentType::String;
    variants.push(b);
    let mut b = bindings();
    b.calls[1].resource = "Account::\"alice\"".into();
    variants.push(b);
    let mut b = bindings();
    b.policies.pop();
    variants.push(b);
    let mut b = bindings();
    b.policies[1].id = "policy0".into();
    variants.push(b);
    let mut b = bindings();
    b.policies[1].cap.as_mut().unwrap().amount = "missing".into();
    variants.push(b);
    let mut b = bindings();
    b.policies[1].cap.as_mut().unwrap().limit = 0;
    variants.push(b);
    let mut b = bindings();
    b.policies[1].cap.as_mut().unwrap().period = 0;
    variants.push(b);
    let mut b = bindings();
    b.version = 2;
    variants.push(b);
    for b in variants {
        assert!(compile(SOURCE, b).is_err());
    }
    let mut json: serde_json::Value = serde_json::from_str(BINDINGS).unwrap();
    json["root_from_client"] = json!("game.guess");
    assert!(Bindings::from_json(&json.to_string()).is_err());
    assert!(
        Bindings::from_json(&BINDINGS.replacen(
            "\"version\": 1",
            "\"version\": 1, \"version\": 1",
            1
        ))
        .is_err()
    );
    println!("binding rejection cases: 18");
}

#[test]
fn skip_on_error_forbid_cannot_become_a_compiled_grant() {
    let source = format!("{SOURCE}\nforbid(principal,action,resource) when {{ context.missing }};");
    let policies: PolicySet = source.parse().unwrap();
    let request = Request::new(
        "Signer::\"session\"".parse().unwrap(),
        "Action::\"guess\"".parse().unwrap(),
        "Contract::\"game\"".parse().unwrap(),
        Context::from_json_value(json!({"guess":4}), None).unwrap(),
        None,
    )
    .unwrap();
    let response = Authorizer::new().is_authorized(&request, &policies, &Entities::empty());
    assert_eq!(response.decision(), Decision::Allow);
    assert_eq!(response.diagnostics().errors().count(), 1);
    let mut b = bindings();
    b.policies.push(PolicyBinding {
        id: "policy2".into(),
        cap: None,
        valid_until: None,
        generation: None,
    });
    let err = compile(&source, b).err().unwrap();
    assert!(err.0.contains("forbid cannot be dropped"));
}

#[test]
fn raw_cedar_missing_wrong_type_and_overflow_contexts_are_not_silently_skipped() {
    let policies: PolicySet = SOURCE.parse().unwrap();
    for context in [json!({}), json!({"guess":true}), json!({"guess":"4"})] {
        let request = Request::new(
            "Signer::\"session\"".parse().unwrap(),
            "Action::\"guess\"".parse().unwrap(),
            "Contract::\"game\"".parse().unwrap(),
            Context::from_json_value(context, None).unwrap(),
            None,
        )
        .unwrap();
        let response = Authorizer::new().is_authorized(&request, &policies, &Entities::empty());
        assert_eq!(response.decision(), Decision::Deny);
        assert_eq!(response.diagnostics().errors().count(), 1);
    }
    assert!(Context::from_json_value(json!({"guess":9223372036854775808_u64}), None).is_err());
    let c = compiled();
    // Even bypassing the request mapper cannot truncate a huge i128 into an allowed enumerated value.
    for amount in [
        i128::MIN,
        i128::MAX,
        i128::from(i64::MAX) + 1,
        i128::from(i64::MIN) - 1,
    ] {
        assert!(!rule_eval::rule_allows_in(
            &c.rules()[1],
            Some(&guess(4)),
            &transfer(amount),
            &[signer(1)]
        ));
    }
}
