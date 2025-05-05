{
  description = "Synthetic domains";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-unstable;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib; eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.lib;
        coq = pkgs.coq_9_0;
        coqPkgs = pkgs.coqPackages_9_0;
      in {
        packages = {
          coq-artifact = coqPkgs.mkCoqDerivation {
            pname = "rocq-artifact";
            version = "main";
            src = ./.;
            buildPhase = "make";
            propagatedBuildInputs = [
              coqPkgs.stdpp
            ];
          };
        };
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            coq
          ];
          inputsFrom = [ self.packages.${system}.coq-artifact ];
        };
      });
}
