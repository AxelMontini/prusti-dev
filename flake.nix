{
  description = "A static verifier for Rust, based on the Viper verification infrastructure.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
    crane.url = "github:ipetkov/crane";
    utils.url = "github:numtide/flake-utils";
    self.submodules = true;
  };

  outputs =
    {
      self,
      nixpkgs,
      crane,
      rust-overlay,
      utils,
    }:
    utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlays.default ];
        };
        inherit (pkgs) lib stdenv;

        # Viper and prusti
        prustiVersion = "${self.tag or "${self.lastModifiedDate}.${self.shortRev or "dirty"}"}";
        viperVersion = (lib.trim (builtins.readFile ./viper-toolchain));
        viperToolchain = stdenv.mkDerivation rec {
          pname = "viper";
          version = viperVersion;

          src = pkgs.fetchzip {
            url = "https://github.com/viperproject/viper-ide/releases/download/${viperVersion}/ViperToolsLinux.zip";
            name = "viper";
            stripRoot = false;
            hash = "sha256-GyQ7LBOimr3eEfgMTMc9ZphV3LYYbkBRcS9UbM39+Qs=";
          };

          buildInputs = [
            # For basically all
            stdenv.cc.cc.lib
            # For Boogie
            pkgs.zlib
            pkgs.lttng-ust
            pkgs.icu.dev
            pkgs.openssl
            pkgs.icu77
            pkgs.openssl_3
          ];

          # Cannot find this, most likely not needed anyway, right?
          autoPatchelfIgnoreMissingDeps = [ "liblttng-ust.so.0" ];

          nativeBuildInputs = with pkgs; [ autoPatchelfHook ];

          installPhase = ''
            runHook preInstall
            mkdir -p $out
            cp -r ${src}/* $out
            chmod 755 $out/z3/bin/z3
            runHook postInstall
          '';

          preFixup = ''
            echo $LD_LIBRARY_PATH
            patchelf --add-needed libicuuc.so.77 $out/boogie/Binaries/Boogie
            patchelf --add-needed libssl.so.3 $out/boogie/Binaries/Boogie
          '';
        };
        ow2Asm = pkgs.stdenv.mkDerivation rec {
          name = "asm";
          version = "3.3.1";
          src = pkgs.fetchurl {
            url = "https://repo.maven.apache.org/maven2/${name}/${name}/${version}/${name}-${version}.jar";
            hash = "sha256-wrOSdfjpUbx0dQCAoSZs2rw5OZvF4T1kK/LTRkSd9/M=";
          };
          dontUnpack = true;
          dontBuild = true;
          installPhase = ''
            mkdir $out
            cp ${src} $out/asm.jar
          '';
        };
        jdk = pkgs.jdk11;

        # Rust setup
        rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain;
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
        src = craneLib.cleanCargoSource ./.;
        # Common arguments can be set here to avoid repeating them later
        commonArgs = {
          inherit src;
          strictDeps = true;

          buildInputs = [
            pkgs.wget
            pkgs.gcc
            pkgs.openssl
            viperToolchain
            ow2Asm
            rustToolchain
            jdk
          ];

          nativeBuildInputs = [
            pkgs.autoPatchelfHook
            pkgs.makeWrapper
            pkgs.pkg-config
          ];

          LD_LIBRARY_PATH = "${jdk}/lib/openjdk/lib/server";
          VIPER_HOME = "${viperToolchain}/backends";
          Z3_EXE = "${viperToolchain}/z3/bin/z3";
          ASM_JAR = "${ow2Asm}/asm.jar";
          RUST_SYSROOT = "${rustToolchain}";
          JAVA_HOME = "${jdk}/lib/openjdk";

          # libjvm.so is not found otherwise
          preBuild = ''
            addAutoPatchelfSearchPath ${jdk}/lib/openjdk/lib/server
          '';
        };

        # Build *just* the cargo dependencies (of the entire workspace),
        # so we can reuse all of that work (e.g. via cachix) when running in CI
        # It is *highly* recommended to use something like cargo-hakari to avoid
        # cache misses when building individual top-level-crates
        cargoArtifacts = craneLib.buildDepsOnly commonArgs;

        individualCrateArgs = commonArgs // {
          inherit cargoArtifacts;
          inherit (craneLib.crateNameFromCargoToml { inherit src; }) version;
          # NB: we disable tests since we'll run them all via cargo-nextest
          doCheck = false;
        };

        fileSetForCrate =
          crate:
          lib.fileset.toSource {
            root = ./.;
            fileset = lib.fileset.unions [
              ./Cargo.toml
              ./Cargo.lock
              # (craneLib.fileset.commonCargoSources ./prusti-contracts)
              ./rust-toolchain
              (craneLib.fileset.commonCargoSources crate)
            ];
          };
        prusti_driver = craneLib.buildPackage (
          individualCrateArgs
          // {
            pname = "prusti";
            cargoExtraArgs = "-p prusti";
            src = fileSetForCrate ./.;
          }
        );
        prusti_launch = craneLib.buildPackage (
          individualCrateArgs
          // {
            pname = "prusti-launch";
            cargoExtraArgs = "-p prusti-launch";
            src = fileSetForCrate ./.;
          }
        );
      in
      rec {
        packages = {
          inherit prusti_driver prusti_launch;
        };

        checks = {
          # prusti-test = naersk-lib.buildPackage {
          #   name = "prusti-test";
          #   version = "${prusti-version}";
          #   root = ./.;
          #   checkInputs = [
          #     pkgs.pkg-config
          #     pkgs.wget
          #     pkgs.gcc
          #     pkgs.openssl
          #     pkgs.jdk11
          #     packages.viper
          #     packages.ow2_asm
          #   ];

          #   doCheck = true;

          #   override = _: {
          #     preBuild = ''
          #       export LD_LIBRARY_PATH="${pkgs.jdk11}/lib/openjdk/lib/server"
          #       export VIPER_HOME="${packages.viper}/backends"
          #       export Z3_EXE="${packages.viper}/z3/bin/z3"
          #       export ASM_JAR="${packages.ow2_asm}/asm.jar"
          #     '';
          #     preCheck = ''
          #       export RUST_SYSROOT="${rust}"
          #       export JAVA_HOME="${pkgs.jdk11}/lib/openjdk"
          #       export LD_LIBRARY_PATH="${pkgs.jdk11}/lib/openjdk/lib/server"
          #       export VIPER_HOME="${packages.viper}/backends"
          #       export Z3_EXE="${packages.viper}/z3/bin/z3"
          #     '';
          #   };
          # };

          prusti-simple-test =
            pkgs.runCommand "prusti-simple-test"
              {
                buildInputs = [
                  defaultPackage
                  rustToolchain
                ];
              }
              ''
                cargo new --name example $out/example
                sed -i '1s/^/use prusti_contracts::*;\n/;s/println.*$/assert!(true);/' $out/example/src/main.rs
                cargo-prusti --manifest-path=$out/example/Cargo.toml
              '';
        };

        defaultPackage = packages.prusti_driver;

        # devShells.default = craneLib.devShell {
        #   # Inherit inputs from checks.
        #   checks = self.checks.${system};
        #
        #   # Extra inputs can be added here; cargo and rustc are provided by default
        #   # from the toolchain that was specified earlier.
        #   packages = [
        #     viperToolchain
        #     ow2Asm
        #   ];
        # };
        devShells.default =
          with pkgs;
          mkShell {
            buildInputs = [
              pkg-config
              rustToolchain
              viperToolchain
              ow2Asm
              rust-analyzer
            ];

            nativeBuildInputs = [
              autoPatchelfHook
            ];

            shellHook = ''
              export RUST_SYSROOT="${rustToolchain}"
              export JAVA_HOME="${jdk}/lib/openjdk"
              export LD_LIBRARY_PATH="${jdk}/lib/openjdk/lib/server:${pkgs.icu77}/lib"
              export VIPER_HOME="${viperToolchain}/backends"
              export Z3_EXE="${viperToolchain}/z3/bin/z3"
              export ASM_JAR="${ow2Asm}/asm.jar"
            '';
          };
      }
    );
}
