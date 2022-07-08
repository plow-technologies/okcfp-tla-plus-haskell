{ sources ? import ./sources.nix}:
let overlay = _: pkgs: {
      niv = (import sources.niv {}).niv;
    };
    nixpkgs = import sources.nixpkgs { overlays = [ overlay ]; config = {}; };
in nixpkgs  
