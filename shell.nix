
{ pkgs ? import <nixpkgs> {} }:

let
  hp = pkgs.haskell.packages.ghc910;
in

pkgs.mkShell {
  buildInputs = [
    (hp.ghcWithPackages (ps: with ps; [ z3 ]))
    pkgs.cabal-install
  ];
}
