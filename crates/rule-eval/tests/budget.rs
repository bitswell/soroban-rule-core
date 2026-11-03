//! Budgets on the delegation tree: charging the chain, the refusal naming the
//! nearest overdrawn node, oversubscription, checked sums, malformed trees,
//! delegation and refills, an exhaustive comparison with a plain reading of
//! the operations over small trees, and the budget bound over random runs.

use rule_eval::{BudgetError, MAX_NODES, Node, delegate, refill, spend, tree_valid};

type Parts = Vec<(Option<u32>, i128, i128)>;

/// The tree after an operation, as its nodes' fields, or the refusal.
type Outcome = Result<Parts, Refused>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Refused {
    Malformed,
    NoSuchNode(u32),
    NegativeAmount,
    Overdrawn(u32),
    Overflow,
    TreeFull,
}

fn tree(nodes: &[(Option<u32>, i128, i128)]) -> Vec<Node> {
    nodes
        .iter()
        .map(|&(parent, allowance, spent)| Node {
            parent,
            allowance,
            spent,
        })
        .collect()
}

fn parts(t: &[Node]) -> Parts {
    t.iter().map(|n| (n.parent, n.allowance, n.spent)).collect()
}

fn refused(e: &BudgetError) -> Refused {
    match e {
        BudgetError::Malformed => Refused::Malformed,
        BudgetError::NoSuchNode(i) => Refused::NoSuchNode(*i),
        BudgetError::NegativeAmount => Refused::NegativeAmount,
        BudgetError::Overdrawn(i) => Refused::Overdrawn(*i),
        BudgetError::Overflow => Refused::Overflow,
        BudgetError::TreeFull => Refused::TreeFull,
    }
}

fn outcome(r: Result<Vec<Node>, BudgetError>) -> Outcome {
    match r {
        Ok(t) => Ok(parts(&t)),
        Err(e) => Err(refused(&e)),
    }
}

fn spend_at(t: &[Node], node: u32, amount: i128) -> Outcome {
    outcome(spend(t, node, amount))
}

fn delegate_at(t: &[Node], parent: u32, allowance: i128) -> Outcome {
    outcome(delegate(t, parent, allowance))
}

fn refill_at(t: &[Node], node: u32, amount: i128) -> Outcome {
    outcome(refill(t, node, amount))
}

/// A tree of allowance 10 at the root and 8 at each of two children.
fn siblings() -> Vec<Node> {
    tree(&[(None, 10, 0), (Some(0), 8, 0), (Some(0), 8, 0)])
}

#[test]
fn a_spend_charges_the_spender_and_every_ancestor() {
    let t = tree(&[
        (None, 100, 0),
        (Some(0), 50, 0),
        (Some(1), 20, 0),
        (Some(0), 50, 0),
    ]);
    assert_eq!(
        spend_at(&t, 2, 5),
        Ok(vec![
            (None, 100, 5),
            (Some(0), 50, 5),
            (Some(1), 20, 5),
            (Some(0), 50, 0),
        ])
    );
    assert_eq!(
        spend_at(&t, 0, 7),
        Ok(vec![
            (None, 100, 7),
            (Some(0), 50, 0),
            (Some(1), 20, 0),
            (Some(0), 50, 0),
        ])
    );
}

#[test]
fn oversubscribed_siblings_share_their_parent() {
    let t = siblings();
    let after = spend(&t, 1, 8).ok().unwrap();
    assert_eq!(spend_at(&after, 2, 3), Err(Refused::Overdrawn(0)));
    assert_eq!(
        spend_at(&after, 2, 2),
        Ok(vec![(None, 10, 10), (Some(0), 8, 8), (Some(0), 8, 2)])
    );
}

#[test]
fn the_refusal_names_the_nearest_overdrawn_node() {
    let t = tree(&[(None, 5, 0), (Some(0), 3, 0), (Some(1), 1, 0)]);
    assert_eq!(spend_at(&t, 2, 6), Err(Refused::Overdrawn(2)));
    assert_eq!(spend_at(&t, 1, 6), Err(Refused::Overdrawn(1)));
    assert_eq!(spend_at(&t, 1, 4), Err(Refused::Overdrawn(1)));
    let t = tree(&[(None, 5, 0), (Some(0), 30, 0), (Some(1), 10, 0)]);
    assert_eq!(spend_at(&t, 2, 6), Err(Refused::Overdrawn(0)));
}

#[test]
fn a_middle_ancestor_bounds_everything_under_it() {
    let t = tree(&[
        (None, 100, 0),
        (Some(0), 10, 0),
        (Some(1), 50, 0),
        (Some(1), 50, 0),
    ]);
    let after = spend(&t, 2, 10).ok().unwrap();
    assert_eq!(spend_at(&after, 3, 1), Err(Refused::Overdrawn(1)));
    assert_eq!(spend_at(&after, 2, 1), Err(Refused::Overdrawn(1)));
    assert!(spend(&after, 0, 90).is_ok());
}

#[test]
fn an_overflowing_sum_counts_as_overdrawn() {
    let t = tree(&[(None, i128::MAX, i128::MAX - 1), (Some(0), i128::MAX, 0)]);
    assert_eq!(spend_at(&t, 1, 2), Err(Refused::Overdrawn(0)));
    let t = tree(&[(None, i128::MAX, 0), (Some(0), i128::MAX, i128::MAX)]);
    assert_eq!(spend_at(&t, 1, 1), Err(Refused::Overdrawn(1)));
    assert_eq!(spend_at(&t, 1, i128::MAX), Err(Refused::Overdrawn(1)));
    assert!(spend(&t, 1, 0).is_ok());
}

#[test]
fn every_operation_refuses_a_malformed_tree() {
    let malformed = [
        tree(&[(Some(0), 10, 0)]),
        tree(&[(None, 10, 0), (Some(1), 10, 0)]),
        tree(&[(Some(1), 10, 0), (None, 10, 0)]),
        tree(&[(None, -1, 0)]),
        tree(&[(None, 10, -1)]),
        tree(&[(None, 10, 0), (Some(0), i128::MIN, 0)]),
    ];
    for t in &malformed {
        assert!(!tree_valid(t));
        for node in [0, 1, 5] {
            assert_eq!(spend_at(t, node, 1), Err(Refused::Malformed));
            assert_eq!(spend_at(t, node, -1), Err(Refused::Malformed));
            assert_eq!(delegate_at(t, node, 1), Err(Refused::Malformed));
            assert_eq!(refill_at(t, node, 1), Err(Refused::Malformed));
        }
    }
    assert!(tree_valid(&[]));
    assert!(tree_valid(&siblings()));
}

#[test]
fn a_spend_refuses_in_order() {
    let t = siblings();
    assert_eq!(spend_at(&t, 3, -1), Err(Refused::NoSuchNode(3)));
    assert_eq!(
        spend_at(&t, u32::MAX, 1),
        Err(Refused::NoSuchNode(u32::MAX))
    );
    assert_eq!(spend_at(&t, 0, -1), Err(Refused::NegativeAmount));
    assert_eq!(spend_at(&t, 0, i128::MIN), Err(Refused::NegativeAmount));
    assert_eq!(spend_at(&[], 0, 0), Err(Refused::NoSuchNode(0)));
}

#[test]
fn a_zero_spend_charges_nothing() {
    let t = tree(&[(None, 3, 3), (Some(0), 3, 0)]);
    assert_eq!(spend_at(&t, 1, 0), Ok(parts(&t)));
    let t = tree(&[(None, 3, 4), (Some(0), 3, 0)]);
    assert_eq!(spend_at(&t, 1, 0), Err(Refused::Overdrawn(0)));
}

#[test]
fn a_delegation_appends_a_child_with_any_allowance() {
    let t = siblings();
    assert_eq!(
        delegate_at(&t, 1, 20),
        Ok(vec![
            (None, 10, 0),
            (Some(0), 8, 0),
            (Some(0), 8, 0),
            (Some(1), 20, 0),
        ])
    );
    assert_eq!(
        delegate_at(&t, 2, i128::MAX).map(|p| p[3]),
        Ok((Some(2), i128::MAX, 0))
    );
    assert_eq!(delegate_at(&t, 0, 0).map(|p| p.len()), Ok(4));
    assert_eq!(delegate_at(&t, 3, 1), Err(Refused::NoSuchNode(3)));
    assert_eq!(delegate_at(&t, 0, -1), Err(Refused::NegativeAmount));
    assert_eq!(delegate_at(&[], 0, 1), Err(Refused::NoSuchNode(0)));
    assert_eq!(MAX_NODES, u32::MAX as usize);
}

#[test]
fn a_delegated_node_is_bounded_by_its_ancestors() {
    let t = delegate(&siblings(), 1, 20).ok().unwrap();
    assert_eq!(spend_at(&t, 3, 9), Err(Refused::Overdrawn(1)));
    assert_eq!(
        spend_at(&t, 3, 8),
        Ok(vec![
            (None, 10, 8),
            (Some(0), 8, 8),
            (Some(0), 8, 0),
            (Some(1), 20, 8),
        ])
    );
}

#[test]
fn a_refill_raises_one_allowance() {
    let t = tree(&[(None, 10, 4), (Some(0), 4, 4)]);
    assert_eq!(spend_at(&t, 1, 1), Err(Refused::Overdrawn(1)));
    let raised = refill(&t, 1, 2).ok().unwrap();
    assert_eq!(parts(&raised), vec![(None, 10, 4), (Some(0), 6, 4)]);
    assert!(spend(&raised, 1, 2).is_ok());
    assert_eq!(refill_at(&t, 1, 0), Ok(parts(&t)));
    assert_eq!(refill_at(&t, 1, -1), Err(Refused::NegativeAmount));
    assert_eq!(refill_at(&t, 2, -1), Err(Refused::NoSuchNode(2)));
    let t = tree(&[(None, i128::MAX - 1, 0)]);
    assert_eq!(refill_at(&t, 0, 2), Err(Refused::Overflow));
    assert_eq!(refill_at(&t, 0, 1), Ok(vec![(None, i128::MAX, 0)]));
}

#[test]
fn a_refusal_leaves_the_tree_as_it_was() {
    let t = siblings();
    let before = parts(&t);
    let _ = spend(&t, 1, 9);
    let _ = delegate(&t, 7, 1);
    let _ = refill(&t, 0, -1);
    assert_eq!(parts(&t), before);
}

/// A plain reading of the operations, written without the restrictions the
/// evaluator follows.
mod reference {
    use super::{Outcome, Parts, Refused};

    pub fn valid(t: &Parts) -> bool {
        t.iter()
            .enumerate()
            .all(|(i, &(parent, allowance, spent))| {
                parent.is_none_or(|p| (p as usize) < i) && allowance >= 0 && spent >= 0
            })
    }

    /// The spender and its ancestors, the spender first.
    fn chain(t: &Parts, node: usize) -> Vec<usize> {
        let mut out = vec![node];
        let mut current = node;
        while let Some(p) = t[current].0 {
            current = p as usize;
            out.push(current);
        }
        out
    }

    pub fn spend(t: &Parts, node: u32, amount: i128) -> Outcome {
        if !valid(t) {
            return Err(Refused::Malformed);
        }
        if node as usize >= t.len() {
            return Err(Refused::NoSuchNode(node));
        }
        if amount < 0 {
            return Err(Refused::NegativeAmount);
        }
        let chain = chain(t, node as usize);
        for &j in &chain {
            let (_, allowance, spent) = t[j];
            if spent.checked_add(amount).is_none_or(|s| s > allowance) {
                return Err(Refused::Overdrawn(u32::try_from(j).unwrap()));
            }
        }
        let mut out = t.clone();
        for &j in &chain {
            out[j].2 += amount;
        }
        Ok(out)
    }

    pub fn delegate(t: &Parts, parent: u32, allowance: i128) -> Outcome {
        if !valid(t) {
            return Err(Refused::Malformed);
        }
        if parent as usize >= t.len() {
            return Err(Refused::NoSuchNode(parent));
        }
        if allowance < 0 {
            return Err(Refused::NegativeAmount);
        }
        let mut out = t.clone();
        out.push((Some(parent), allowance, 0));
        Ok(out)
    }

    pub fn refill(t: &Parts, node: u32, amount: i128) -> Outcome {
        if !valid(t) {
            return Err(Refused::Malformed);
        }
        let Some(&(_, allowance, _)) = t.get(node as usize) else {
            return Err(Refused::NoSuchNode(node));
        };
        if amount < 0 {
            return Err(Refused::NegativeAmount);
        }
        let Some(raised) = allowance.checked_add(amount) else {
            return Err(Refused::Overflow);
        };
        let mut out = t.clone();
        out[node as usize].1 = raised;
        Ok(out)
    }
}

/// Every tree of up to three nodes whose fields come from small universes,
/// well formed or not.
fn small_trees() -> Vec<Parts> {
    let parents = [None, Some(0), Some(1), Some(2)];
    let amounts = [-1, 0, 1, 2, i128::MAX];
    let mut nodes = Vec::new();
    for parent in parents {
        for allowance in amounts {
            for spent in amounts {
                nodes.push((parent, allowance, spent));
            }
        }
    }
    let mut trees = vec![Vec::new()];
    for &a in &nodes {
        trees.push(vec![a]);
    }
    let few: Vec<_> = nodes.iter().copied().step_by(7).collect();
    for &a in &few {
        for &b in &few {
            trees.push(vec![a, b]);
            for &c in few.iter().step_by(3) {
                trees.push(vec![a, b, c]);
            }
        }
    }
    trees
}

#[test]
fn every_operation_agrees_with_a_plain_reading_on_small_trees() {
    let indices = [0, 1, 2, 3, u32::MAX];
    let amounts = [i128::MIN, -1, 0, 1, 2, 3, i128::MAX];
    for t in small_trees() {
        let rt = tree(&t);
        assert_eq!(tree_valid(&rt), reference::valid(&t), "{t:?}");
        for node in indices {
            for amount in amounts {
                assert_eq!(
                    spend_at(&rt, node, amount),
                    reference::spend(&t, node, amount),
                    "spend {node} {amount} on {t:?}"
                );
                assert_eq!(
                    delegate_at(&rt, node, amount),
                    reference::delegate(&t, node, amount),
                    "delegate {node} {amount} on {t:?}"
                );
                assert_eq!(
                    refill_at(&rt, node, amount),
                    reference::refill(&t, node, amount),
                    "refill {node} {amount} on {t:?}"
                );
            }
        }
    }
}

/// A small deterministic generator for the random runs.
struct Lcg(u64);

impl Lcg {
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % n
    }
}

/// Whether `a` is `i` or one of its ancestors.
fn at_or_above(t: &Parts, i: usize, a: usize) -> bool {
    let mut current = i;
    loop {
        if current == a {
            return true;
        }
        match t[current].0 {
            Some(p) => current = p as usize,
            None => return false,
        }
    }
}

#[test]
fn spent_under_a_node_stays_within_its_allowance_over_random_runs() {
    let mut g = Lcg(20_261_103);
    for _ in 0..300 {
        let mut t: Vec<Node> = vec![Node {
            parent: None,
            allowance: i128::from(g.below(40)),
            spent: 0,
        }];
        let mut log: Vec<(usize, i128)> = Vec::new();
        for _ in 0..40 {
            let len = u64::try_from(t.len()).unwrap();
            let node = u32::try_from(g.below(len + 1)).unwrap();
            let amount = i128::from(g.below(12));
            let result = match g.below(6) {
                0..=2 => {
                    let r = spend(&t, node, amount);
                    if r.is_ok() {
                        log.push((node as usize, amount));
                    }
                    r
                }
                3 | 4 => delegate(&t, node, i128::from(g.below(30))),
                _ => refill(&t, node, amount),
            };
            if let Ok(next) = result {
                t = next;
            }
            let p = parts(&t);
            for (a, n) in t.iter().enumerate() {
                let under: i128 = log
                    .iter()
                    .filter(|&&(i, _)| at_or_above(&p, i, a))
                    .map(|&(_, x)| x)
                    .sum();
                assert_eq!(under, n.spent, "node {a} of {p:?}");
                assert!(n.spent <= n.allowance, "node {a} of {p:?}");
            }
        }
    }
}
