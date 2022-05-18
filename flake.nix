{
  description = "Software Foundations";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
      in
      {
        devShell = with pkgs; mkShell {
          buildInputs = [
            coq
            gnumake
          ];

          shellHook = ''
            echo "-Q src sf" > _CoqProject
            echo "-arg -w -arg -notation-overridden" >> _CoqProject
            echo "" >> _CoqProject

            find src -iname '*.v' >> _CoqProject

            make all
          '';
        };
      }
    );
}