{
  description = "category";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-24.11;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib; eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.lib;
        # coq = pkgs.coq_8_18;
        # coqPkgs = pkgs.coqPackages_8_18;
        # coq = pkgs.coq_8_19;
        # coqPkgs = pkgs.coqPackages_8_19;
        coq = pkgs.coq_8_20;
        coqPkgs = pkgs.coqPackages_8_20;
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
