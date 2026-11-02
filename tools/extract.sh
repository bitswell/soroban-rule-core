#!/usr/bin/env bash
# Regenerate formal/RuleCore/Extracted/RuleEval.lean from crates/rule-eval:
# Charon translates the crate to LLBC, Aeneas translates the LLBC to Lean.
#
# Charon and Aeneas come from this repository's flake. flake.nix pins one
# Aeneas commit, which fixes the Charon commit and the Rust nightly Charon
# reads MIR with; formal/lakefile.toml requires Aeneas's Lean library at the
# same commit, so the generated code and the library it is written against
# come from the same Aeneas. Aeneas runs with -warnings-as-errors and Charon
# with --error-on-warnings: a construct either tool cannot translate exactly
# fails the extraction.
#
# Needs Nix with flakes; Aeneas's binary cache (hacl.cachix.org, named in
# flake.nix) serves prebuilt Charon and Aeneas. Without Nix, run it in the
# nixos/nix image from a copy of the repository:
#
#   docker run --rm -v "$PWD":/src -w /src nixos/nix:2.28.3 tools/extract.sh
#
# Usage: tools/extract.sh [--check]
#
# With --check it regenerates into a temporary directory and fails if the
# result differs from the committed file.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
generated="formal/RuleCore/Extracted/RuleEval.lean"

check=
case "${1:-}" in
  "") ;;
  --check) check=1 ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac

# Re-run under `nix shell` with the flake's Aeneas (and the Charon it ships)
# on PATH.
if [[ -z "${RULE_EVAL_EXTRACT_PINNED:-}" ]]; then
  export NIX_CONFIG="${NIX_CONFIG:+$NIX_CONFIG
}experimental-features = nix-command flakes
extra-substituters = https://hacl.cachix.org
extra-trusted-public-keys = hacl.cachix.org-1:FzsZ2xsByOwKwIWNPII7yMOelJNDZ12mDAj3d1eGX0c="
  RULE_EVAL_EXTRACT_PINNED=1 exec nix shell "$root#aeneas" --command bash "$0" "$@"
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

(
  cd "$root/crates/rule-eval"
  CARGO_TARGET_DIR="$tmp/target" charon cargo \
    --preset=aeneas --error-on-warnings \
    --dest-file "$tmp/rule_eval.llbc"
)

aeneas -backend lean -warnings-as-errors -abort-on-error \
  -dest "$tmp/lean" "$tmp/rule_eval.llbc"

# The crate translates to exactly one Lean file.
produced="$(cd "$tmp/lean" && find . -type f | sort)"
if [[ "$produced" != "./RuleEval.lean" ]]; then
  echo "expected Aeneas to produce RuleEval.lean alone, got:" >&2
  echo "$produced" >&2
  exit 1
fi

if [[ -n "$check" ]]; then
  # `git diff --no-index` compares plain files; run it outside any repository.
  cd "$tmp"
  if ! git diff --no-index --exit-code -- "$root/$generated" "$tmp/lean/RuleEval.lean"; then
    echo "$generated is stale: run tools/extract.sh" >&2
    exit 1
  fi
  echo "$generated matches a fresh extraction"
else
  mkdir -p "$(dirname "$root/$generated")"
  cp "$tmp/lean/RuleEval.lean" "$root/$generated"
  echo "wrote $generated"
fi
