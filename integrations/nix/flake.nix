{
  description = "Thiele Machine - Self-verifying computational proofs";
  
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        python = pkgs.python312;
      in
      {
        packages.default = pkgs.stdenv.mkDerivation {
          pname = "thiele-replay";
          version = "1.0.0";
          
          src = ./.;
          
          buildInputs = [ python ];
          
          installPhase = ''
            mkdir -p $out/bin $out/lib/thiele-replay
            
            # Install verifier
            cp -r verifier/* $out/lib/thiele-replay/
            
            # Create wrapper
            cat > $out/bin/thiele-replay << EOF
            #!${pkgs.bash}/bin/bash
            exec ${python}/bin/python3 $out/lib/thiele-replay/replay.py "\$@"
            EOF
            
            chmod +x $out/bin/thiele-replay
            
            # Self-verify on build
            $out/bin/thiele-replay bootstrap_receipts
          '';
          
          meta = with pkgs.lib; {
            description = "Cryptographic receipt verifier for Thiele Machine";
            homepage = "https://github.com/sethirus/The-Thiele-Machine";
            license = licenses.asl20;
            maintainers = with maintainers; [ ];
            platforms = platforms.all;
          };
        };
        
        apps.default = flake-utils.lib.mkApp {
          drv = self.packages.${system}.default;
        };
        
        devShells.default = pkgs.mkShell {
          buildInputs = [
            python
            pkgs.python312Packages.pytest
            pkgs.python312Packages.pynacl
          ];
        };
      }
    );
}
