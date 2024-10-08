{
  description = "Coq programming flake";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem ( system:
    let
      pkgs = import nixpkgs { inherit system; };

      ncoq = pkgs.coq_8_18;
      ncoqPackages = pkgs.coqPackages_8_18;
      coq-hahn = ncoqPackages.callPackage (
        { coq, stdenv, fetchFromGitHub }:
        stdenv.mkDerivation {
          name = "coq${coq.coq-version}-hahn";

          src = fetchFromGitHub {
            owner = "vafeiadis";
            repo = "hahn";
            rev = "b7c2ab4407af9edb5394d3d2c598c0db70c94a30";
            sha256 = "GHX4qC0qFHAt4YxA6EG6ldY7QNcpN4t+ANOJwzHP3E8=";
          };

          buildInputs = with coq.ocamlPackages; [ ocaml camlp5 ];
          propagatedBuildInputs = [ coq ];
          enableParallelBuilding = true;

          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
        }) {};

    in {
      devShell = pkgs.mkShell {
        name = "coq";

        buildInputs = [
          ncoq
          coq-hahn
        ];

      };
    });
}

