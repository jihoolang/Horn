{
  description = "Horn: a small checker for many-sorted Horn derivation certificates";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/e7439b6b14ad3cc35d05608ebca9bce01a25f5f8";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      eachSystem = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      packages = eachSystem (pkgs: {
        default = pkgs.rustPlatform.buildRustPackage {
          pname = "horn";
          version = "0.3.0";
          src = self;
          cargoLock.lockFile = ./Cargo.lock;
        };
      });

      devShells = eachSystem (pkgs: {
        default = pkgs.mkShell {
          packages = with pkgs; [ cargo rustc rustfmt clippy agda ];
        };
      });

      checks = eachSystem (pkgs: {
        rust = self.packages.${pkgs.stdenv.hostPlatform.system}.default;
        # The soundness proof uses no libraries; --safe rejects postulates.
        agda = pkgs.runCommand "horn-agda-soundness" { nativeBuildInputs = [ pkgs.agda ]; } ''
          # Agda's messages contain Unicode.
          export LC_ALL=C.UTF-8
          cp -R ${self}/agda agda
          chmod -R u+w agda
          agda --safe --no-libraries -i agda agda/Soundness.agda
          agda --safe --no-libraries -i agda agda/Schematic.agda
          agda --safe --no-libraries -i agda agda/Implication.agda
          agda --safe --no-libraries -i agda agda/Unify.agda
          agda --safe --no-libraries -i agda agda/LevelsCertificate.agda
          agda --safe --no-libraries -i agda agda/NatLang.agda
          agda --safe --no-libraries -i agda agda/ImplicationCheck.agda
          agda --safe --no-libraries -i agda agda/LeTransCertificate.agda
          # Agda itself rejects the certificate for a goal without one of
          # its hypotheses.
          sed 's/^module LeTransCertificate/module Dropped/; s/^goals = (\(g[0-9]*\) ∷ g[0-9]* ∷ \[\]/goals = (\1 ∷ []/' \
            agda/LeTransCertificate.agda > agda/Dropped.agda
          if agda --safe --no-libraries -i agda agda/Dropped.agda > dropped.log 2>&1; then
            echo "Agda accepted a goal without a hypothesis" >&2
            exit 1
          fi
          grep -q 'nothing != just tt' dropped.log
          touch "$out"
        '';
      });
    };
}
