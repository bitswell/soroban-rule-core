//! Budgets: allowances on the delegation tree.
//!
//! A tree is a slice of [`Node`]s. Each node holds its parent's index, or
//! `None` for a root, its allowance, and what has been spent at or under it.
//! A node's parent index is below its own, so the tree has no cycle and the
//! walk from a node to its root visits at most as many nodes as the slice
//! holds. A tree is well formed ([`tree_valid`]) when every parent index is
//! below its node's index and no allowance or spent amount is negative. Every
//! operation refuses a tree that is not well formed with
//! [`BudgetError::Malformed`].
//!
//! - [`spend`] charges the spender and every ancestor up to its root by the
//!   amount, or refuses. It first walks the chain and checks every node on
//!   it, and builds the new tree only if every node can take the amount, so a
//!   refusal leaves the input as it was. A refused spend names the first node
//!   on the chain, counting from the spender, that would be overdrawn: the
//!   node a refill request goes to.
//! - [`delegate`] appends a child with an allowance and nothing spent. The
//!   allowance is not checked against the parent's: children's allowances may
//!   sum to more than their parent's. A spend under an oversubscribed node is
//!   still refused when that node, or any node above it, would be overdrawn.
//! - [`refill`] raises one node's allowance. It is the owner's action, not a
//!   holder's: the shell accepts a refill only on the owner's authority.
//!
//! The functions are pure. The shell stores the tree, passes it in and stores
//! what an operation returns only on `Ok`. Which node an authorization spends
//! from, and how much, is also the shell's choice.
//!
//! The readable Lean model is `formal/RuleCore/Model/Budget.lean`.

use alloc::vec::Vec;

/// The most nodes a tree reaches through [`delegate`]: every node's index is
/// below `u32::MAX`, so it fits in a `u32`.
pub const MAX_NODES: usize = u32::MAX as usize;

/// One node of the delegation tree.
pub struct Node {
    /// The parent's index, or `None` for a root.
    pub parent: Option<u32>,
    /// The most that may be spent at or under this node.
    pub allowance: i128,
    /// What has been spent at or under this node.
    pub spent: i128,
}

/// Why an operation on the tree was refused. The tree is unchanged.
pub enum BudgetError {
    /// A node's parent index is not below its own index, or an allowance or
    /// a spent amount is negative.
    Malformed,
    /// No node has this index.
    NoSuchNode(u32),
    /// The amount, or the allowance, is negative.
    NegativeAmount,
    /// Charging this node would take its spent amount above its allowance,
    /// or past the largest `i128`.
    Overdrawn(u32),
    /// The raised allowance does not fit in an `i128`.
    Overflow,
    /// The tree already holds [`MAX_NODES`] nodes.
    TreeFull,
}

/// Whether `n`, at position `index`, is well formed: its parent index is below
/// `index`, and its allowance and spent amount are not negative.
fn node_valid(n: &Node, index: usize) -> bool {
    let parent_below = match n.parent {
        Some(p) => (p as usize) < index,
        None => true,
    };
    parent_below && n.allowance >= 0 && n.spent >= 0
}

/// Whether every node of `tree` is well formed.
#[must_use]
pub fn tree_valid(tree: &[Node]) -> bool {
    let mut i = 0;
    while i < tree.len() {
        if !node_valid(&tree[i], i) {
            return false;
        }
        i += 1;
    }
    true
}

/// Whether `n` can take `amount`: `spent + amount` fits in an `i128` and is at
/// most the allowance.
fn fits(n: &Node, amount: i128) -> bool {
    match n.spent.checked_add(amount) {
        Some(total) => total <= n.allowance,
        None => false,
    }
}

/// Walks from `node` to its root and refuses at the first node that cannot
/// take `amount`.
fn check_chain(tree: &[Node], node: u32, amount: i128) -> Result<(), BudgetError> {
    let mut current = node;
    let mut step = 0;
    while step < tree.len() {
        let n = match tree.get(current as usize) {
            Some(n) => n,
            None => return Err(BudgetError::Malformed),
        };
        if !fits(n, amount) {
            return Err(BudgetError::Overdrawn(current));
        }
        match n.parent {
            None => return Ok(()),
            Some(p) => {
                if p >= current {
                    return Err(BudgetError::Malformed);
                }
                current = p;
            }
        }
        step += 1;
    }
    Err(BudgetError::Malformed)
}

/// A fresh copy of `n`.
fn node_copy(n: &Node) -> Node {
    Node {
        parent: n.parent,
        allowance: n.allowance,
        spent: n.spent,
    }
}

/// A fresh copy of `tree`.
fn nodes_copy(tree: &[Node]) -> Vec<Node> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < tree.len() {
        out.push(node_copy(&tree[i]));
        i += 1;
    }
    out
}

/// A copy of `tree` with `amount` added to the spent amount of `node` and of
/// every ancestor. On a well-formed tree that [`check_chain`] accepted for the
/// same node and amount, every step succeeds and the walk ends at the root.
fn charged(tree: &[Node], node: u32, amount: i128) -> Result<Vec<Node>, BudgetError> {
    let mut out = nodes_copy(tree);
    let mut current = node;
    let mut step = 0;
    while step < tree.len() {
        let n = match tree.get(current as usize) {
            Some(n) => n,
            None => return Err(BudgetError::Malformed),
        };
        let spent = match n.spent.checked_add(amount) {
            Some(spent) => spent,
            None => return Err(BudgetError::Overdrawn(current)),
        };
        match out.get_mut(current as usize) {
            Some(m) => m.spent = spent,
            None => return Err(BudgetError::Malformed),
        }
        match n.parent {
            None => return Ok(out),
            Some(p) => {
                if p >= current {
                    return Err(BudgetError::Malformed);
                }
                current = p;
            }
        }
        step += 1;
    }
    Err(BudgetError::Malformed)
}

/// The tree after a spend of `amount` at `node`, which charges `node` and
/// every ancestor up to its root; or why the spend is refused.
///
/// # Errors
///
/// In order:
///
/// - [`BudgetError::Malformed`] if `tree` is not well formed;
/// - [`BudgetError::NoSuchNode`] if `node` is out of range;
/// - [`BudgetError::NegativeAmount`] if `amount` is negative;
/// - [`BudgetError::Overdrawn`] naming the first node on the chain, counting
///   from `node`, whose spent amount plus `amount` exceeds its allowance or
///   does not fit in an `i128`.
pub fn spend(tree: &[Node], node: u32, amount: i128) -> Result<Vec<Node>, BudgetError> {
    if !tree_valid(tree) {
        return Err(BudgetError::Malformed);
    }
    if node as usize >= tree.len() {
        return Err(BudgetError::NoSuchNode(node));
    }
    if amount < 0 {
        return Err(BudgetError::NegativeAmount);
    }
    match check_chain(tree, node, amount) {
        Ok(()) => charged(tree, node, amount),
        Err(e) => Err(e),
    }
}

/// The tree with a new child of `parent` appended, with `allowance` and
/// nothing spent; or why the delegation is refused. The new node's index is
/// `tree.len()`.
///
/// # Errors
///
/// In order:
///
/// - [`BudgetError::Malformed`] if `tree` is not well formed;
/// - [`BudgetError::NoSuchNode`] if `parent` is out of range;
/// - [`BudgetError::NegativeAmount`] if `allowance` is negative;
/// - [`BudgetError::TreeFull`] if `tree` already holds [`MAX_NODES`] nodes.
pub fn delegate(tree: &[Node], parent: u32, allowance: i128) -> Result<Vec<Node>, BudgetError> {
    if !tree_valid(tree) {
        return Err(BudgetError::Malformed);
    }
    if parent as usize >= tree.len() {
        return Err(BudgetError::NoSuchNode(parent));
    }
    if allowance < 0 {
        return Err(BudgetError::NegativeAmount);
    }
    if tree.len() >= MAX_NODES {
        return Err(BudgetError::TreeFull);
    }
    let mut out = nodes_copy(tree);
    out.push(Node {
        parent: Some(parent),
        allowance,
        spent: 0,
    });
    Ok(out)
}

/// The tree with `node`'s allowance raised by `amount`; or why the refill is
/// refused. A refill is the owner's action: the shell accepts one only on the
/// owner's authority.
///
/// # Errors
///
/// In order:
///
/// - [`BudgetError::Malformed`] if `tree` is not well formed;
/// - [`BudgetError::NoSuchNode`] if `node` is out of range;
/// - [`BudgetError::NegativeAmount`] if `amount` is negative, which would
///   lower the allowance;
/// - [`BudgetError::Overflow`] if the raised allowance does not fit in an
///   `i128`.
pub fn refill(tree: &[Node], node: u32, amount: i128) -> Result<Vec<Node>, BudgetError> {
    if !tree_valid(tree) {
        return Err(BudgetError::Malformed);
    }
    let index = node as usize;
    let allowance = match tree.get(index) {
        Some(n) => {
            if amount < 0 {
                return Err(BudgetError::NegativeAmount);
            }
            match n.allowance.checked_add(amount) {
                Some(allowance) => allowance,
                None => return Err(BudgetError::Overflow),
            }
        }
        None => return Err(BudgetError::NoSuchNode(node)),
    };
    let mut out = Vec::new();
    let mut i = 0;
    while i < tree.len() {
        let mut n = node_copy(&tree[i]);
        if i == index {
            n.allowance = allowance;
        }
        out.push(n);
        i += 1;
    }
    Ok(out)
}
