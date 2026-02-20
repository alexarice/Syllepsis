{
  description = "Agda flake";

  inputs = {
    all-agda.url = "github:alexarice/all-agda";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, all-agda, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs {
        inherit system;
      };
      agdaPackages = all-agda.legacyPackages."x86_64-linux".agdaPackages-2_6_4;
    in {
      packages = rec {
        page = agdaPackages.callPackage ./page.nix { };
        default = page;
      };
    }
  );
}
