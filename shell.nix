let

  sources = import ./nix/sources.nix;
  packages = import sources.nixpkgs {};
  derivation = packages.haskellPackages.callPackage ./default.nix {};

in

  derivation.env.overrideAttrs (oldAttrs: {
    buildInputs = oldAttrs.buildInputs ++ [
      packages.cabal-install
      packages.haskellPackages.Agda
      (packages.haskellPackages.callPackage
        /data/code/agda-unused/default.nix {})
    ];
  })

