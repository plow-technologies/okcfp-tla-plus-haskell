{ nixpkgs ? import <nixpkgs> {} }:
let
  inherit (nixpkgs) pkgs ghc cabal-install ormolu hlint;
  haskell-language-server = pkgs.haskell-language-server.override { supportedGhcVersions = [ "902" ]; };
in
pkgs.mkShell {
  nativeBuildInputs = [ ghc cabal-install haskell-language-server ormolu hlint];
}
