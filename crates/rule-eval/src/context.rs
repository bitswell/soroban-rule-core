//! Authorization contexts.

use alloc::vec::Vec;

use crate::val::Val;

/// One context of a Soroban authorization tree.
pub enum Context {
    /// A contract function call.
    Call {
        contract: Vec<u8>,
        function: Vec<u8>,
        args: Vec<Val>,
    },
    /// A contract creation.
    Create { wasm_hash: Vec<u8> },
}

/// This entry's root. The pinned extraction models `get`, while `first`
/// currently translates to an unchecked external declaration.
#[allow(clippy::get_first)]
pub(crate) fn entry_root(contexts: &[Context]) -> Option<&Context> {
    contexts.get(0)
}
