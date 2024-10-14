{
  description = "category";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-unstable;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib; eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.lib;
        coq = pkgs.coq_8_19;
        coqPkgs = pkgs.coqPackages_8_19;
        # coq = pkgs.coq_8_20;
        # coqPkgs = pkgs.coqPackages_8_20;
        # ocamlPkgs = coq.ocamlPackages;
        # stdpp-dev = coqPkgs.mkCoqDerivation
        #   {
        #     pname = "stdpp";
        #     domain = "gitlab.mpi-sws.org";
        #     owner = "iris";
        #     defaultVersion = "1.10.0";
        #     release."1.10.0".sha256 = "sha256-bfynevIKxAltvt76lsqVxBmifFkzEhyX8lRgTKxr21I=";
        #     releaseRev = v: "coq-stdpp-${v}";
        #     propagatedBuildInputs = [];
        #     preBuild = ''
        #       if [[ -f coq-lint.sh ]]
        #       then patchShebangs coq-lint.sh
        #       fi
        #     '';
        #   };
      in {
        packages = {
          coq-artifact = coqPkgs.mkCoqDerivation {
            pname = "coq-artifact";
            version = ".";
            src = ./.;
            buildPhase = ''
              make
            '';
            propagatedBuildInputs = [
              coqPkgs.stdpp
            ];
          };
        };
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            coq
            coqPkgs.stdpp
          ];
          inputsFrom = [ self.packages.${system}.coq-artifact ];
        };
      });
}
