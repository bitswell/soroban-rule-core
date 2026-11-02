{
  description = "soroban-rule-core: the pinned Rust, Charon, Aeneas and Lean toolchain";

  # Aeneas's binary cache serves prebuilt Charon and Aeneas.
  nixConfig = {
    extra-substituters = [ "https://hacl.cachix.org" ];
    extra-trusted-public-keys = [ "hacl.cachix.org-1:FzsZ2xsByOwKwIWNPII7yMOelJNDZ12mDAj3d1eGX0c=" ];
  };

  # One Aeneas commit fixes the whole toolchain. Its flake.lock pins Charon at
  # the commit its `charon-pin` file names, Charon's `rust-toolchain` file pins
  # the Rust nightly Charon is built against, and its
  # `backends/lean/lean-toolchain` names the Lean release its Lean library
  # builds with. Every other input follows Aeneas's lock.
  inputs = {
    aeneas.url = "github:AeneasVerif/aeneas/ab34bd28458a08c150b7cbf1873e59af74588138";
    charon.follows = "aeneas/charon";
    flake-utils.follows = "aeneas/flake-utils";
    nixpkgs.follows = "aeneas/charon/nixpkgs";
    rust-overlay.follows = "aeneas/charon/rust-overlay";
  };

  outputs = { self, aeneas, charon, flake-utils, nixpkgs, rust-overlay }:
    flake-utils.lib.eachSystem [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ] (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (import rust-overlay) ];
        };
        lib = pkgs.lib;

        leanToolchain = "leanprover/lean4:v4.35.0";

        # The evaluator's toolchain: Charon's nightly, with clippy, rustfmt
        # and the wasm32v1-none standard library.
        rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;

        trim = s: lib.removeSuffix "\n" s;
        lastLine = s: lib.last (lib.filter (l: l != "") (lib.splitString "\n" s));

        charonPin = lastLine (builtins.readFile "${aeneas}/charon-pin");
        charonChannel = (builtins.fromTOML (builtins.readFile "${charon}/rust-toolchain")).toolchain.channel;
        ourChannel = (builtins.fromTOML (builtins.readFile ./rust-toolchain.toml)).toolchain.channel;
        aeneasLean = trim (builtins.readFile "${aeneas}/backends/lean/lean-toolchain");
        formalLean = ./formal/lean-toolchain;

        # Fails evaluation when the pins disagree with each other.
        pinsAgree =
          lib.assertMsg (charon.rev == charonPin)
            "Charon input ${charon.rev} differs from Aeneas's charon-pin ${charonPin}"
          && lib.assertMsg (ourChannel == charonChannel)
            "rust-toolchain.toml channel ${ourChannel} differs from Charon's ${charonChannel}"
          && lib.assertMsg (leanToolchain == aeneasLean)
            "Lean ${leanToolchain} differs from Aeneas's Lean backend ${aeneasLean}"
          && lib.assertMsg
            (!builtins.pathExists formalLean || trim (builtins.readFile formalLean) == leanToolchain)
            "formal/lean-toolchain differs from ${leanToolchain}";
      in
      assert pinsAgree;
      {
        packages = {
          aeneas = aeneas.packages.${system}.aeneas;
          charon = aeneas.packages.${system}.charon;
          rust = rustToolchain;
        };

        # Rust for the evaluator, Charon and Aeneas for the extraction, and
        # elan, which installs the Lean release formal/lean-toolchain names.
        devShells.default = pkgs.mkShell {
          packages = [
            rustToolchain
            aeneas.packages.${system}.aeneas
            pkgs.elan
          ];
          LEAN_TOOLCHAIN = leanToolchain;
        };

        checks.pins = pkgs.runCommand "pins-agree" { } ''
          echo "aeneas ${aeneas.rev}"
          echo "charon ${charon.rev}"
          echo "rust ${ourChannel}"
          echo "lean ${leanToolchain}"
          touch $out
        '';
      });
}
