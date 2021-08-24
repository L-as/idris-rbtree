{
  description = "Well-typed containers for Idris 2";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.idris = {
    url = "github:L-as/Idris2";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, nixpkgs, idris, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let pkgs = nixpkgs.legacyPackages.${system}; in
    rec {
      packages = idris.buildIdris.${system} {
        projectName = "typed-containers";
        src = "${self}";
        idrisLibraries = [];
      };
      defaultPackage = packages.build;
      devShell = pkgs.mkShell {
        buildInputs = [ idris.packages.${system}.idris2 pkgs.rlwrap ];
        shellHook = ''
          alias idris2="rlwrap -s 1000 idris2 --no-banner"
        '';
      };
    }
  );
}
