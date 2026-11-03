//! Reading `__check_auth`'s contexts, and what `rule-eval` reads of them.

use soroban_facade::xdr::address_xdr;
use soroban_facade::{
    Address, AuthContext, Executable, Val, auth_contexts, contexts_to_rule_eval, to_rule_eval,
};

fn call() -> AuthContext {
    AuthContext::Contract {
        contract: Address::Contract([1; 32]),
        fn_name: b"transfer".to_vec(),
        args: vec![Val::Address(Address::Account([2; 32])), Val::I128(10)],
    }
}

fn external_ref() -> Executable {
    Executable::ExternalRef {
        owner: Address::Contract([7; 32]),
        tag: b"v1".to_vec(),
    }
}

fn creations() -> [AuthContext; 3] {
    [
        AuthContext::CreateContract {
            executable: Executable::Wasm([3; 32]),
            salt: [4; 32],
            constructor_args: vec![],
        },
        AuthContext::CreateContract {
            executable: Executable::Wasm([5; 32]),
            salt: [6; 32],
            constructor_args: vec![Val::U32(1)],
        },
        AuthContext::CreateContract {
            executable: external_ref(),
            salt: [8; 32],
            constructor_args: vec![],
        },
    ]
}

#[test]
fn every_context_reads_back_as_itself() {
    let all: Vec<AuthContext> = [vec![call()], creations().to_vec()].concat();
    let v = Val::Vec(all.iter().map(AuthContext::to_val).collect());
    assert_eq!(auth_contexts(&v), Some(all));
}

#[test]
fn one_unreadable_context_refuses_the_batch() {
    let unknown = Val::Vec(vec![
        Val::Symbol(b"CreateContractHostFn".to_vec()),
        Val::Map(vec![
            (
                Val::Symbol(b"executable".to_vec()),
                Val::Vec(vec![Val::Symbol(b"StellarAsset".to_vec())]),
            ),
            (Val::Symbol(b"salt".to_vec()), Val::Bytes(vec![2; 32])),
        ]),
    ]);
    let v = Val::Vec(vec![call().to_val(), unknown]);
    assert_eq!(auth_contexts(&v), None);
    assert_eq!(
        auth_contexts(&call().to_val()),
        None,
        "a context outside a vector"
    );
}

#[test]
fn a_call_reaches_rule_eval_with_scaddress_xdr() {
    let rule_eval::Context::Call {
        contract,
        function,
        args,
    } = to_rule_eval(&call())
    else {
        panic!("a call")
    };
    assert_eq!(contract, address_xdr(&Address::Contract([1; 32])));
    assert_eq!(function, b"transfer");
    assert!(
        matches!(&args[0], rule_eval::Val::Address(a) if *a == address_xdr(&Address::Account([2; 32])))
    );
    assert!(matches!(args[1], rule_eval::Val::I128(10)));
}

/// An external reference reaches `rule-eval` as the `ScVal` XDR of the
/// reference, longer than any Wasm hash.
#[test]
fn an_external_reference_reaches_rule_eval_as_its_xdr() {
    let id = external_ref().id();
    assert_eq!(id, soroban_facade::xdr::encode(&external_ref().to_val()));
    assert!(id.len() > 32);
    assert_eq!(Executable::Wasm([3; 32]).id(), vec![3; 32]);
}

/// A creation reaches `rule-eval` as a creation, which no rule allows.
#[test]
fn creations_reach_rule_eval_as_creations() {
    let rule = rule_eval::Rule {
        contract: address_xdr(&Address::Contract([1; 32])),
        functions: rule_eval::Functions::AnyExcept(vec![]),
        conds: vec![],
        signers: vec![],
        threshold: 0,
        cap: None,
        valid_until: None,
        generation: None,
    };
    let contexts = contexts_to_rule_eval(&creations());
    for c in &contexts {
        assert!(matches!(c, rule_eval::Context::Create { .. }));
        assert!(!rule_eval::allows(std::slice::from_ref(&rule), c, &[]));
    }
    assert!(rule_eval::allows(
        std::slice::from_ref(&rule),
        &to_rule_eval(&call()),
        &[]
    ));
}
