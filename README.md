# soroban-rule-core
Verified rule evaluator for Soroban authorization: a restricted-Rust evaluator, its Lean model and proofs, and a Charon/Aeneas equivalence

## Layout

- `crates/rule-eval/`: the rule-set evaluator and its attenuation steps; `no_std`, no dependencies.
- `flake.nix`: pins Aeneas, Charon, the Rust toolchain they use, and Lean.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT), at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this repository, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
