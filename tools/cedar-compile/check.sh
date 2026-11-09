#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/cedar-to-rule-core.XXXXXX")}"
# The directory is intentionally retained for inspection; no source cleanup.
toolchain="${CEDAR_TOOLCHAIN:-1.99.0}"
manifest=tools/cedar-compile/Cargo.toml
cargo "+$toolchain" run --locked --manifest-path "$manifest" -- \
  tools/cedar-compile/fixtures/guess-transfer.cedar tools/cedar-compile/fixtures/bindings.json
cargo "+$toolchain" test --locked --manifest-path "$manifest" -- --nocapture
for fixture in reject-forbid reject-wide-range; do
  if cargo "+$toolchain" run --locked --manifest-path "$manifest" -- \
    "tools/cedar-compile/fixtures/$fixture.cedar" tools/cedar-compile/fixtures/bindings.json; then
    echo "ERROR: unsupported fixture $fixture compiled" >&2
    exit 1
  fi
done
