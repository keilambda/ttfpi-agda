{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs = inputs@{ nixpkgs, flake-parts, ... }: flake-parts.lib.mkFlake { inherit inputs; } {
    systems = [
      "x86_64-linux"
      "aarch64-darwin"
    ];

    perSystem = { pkgs, ... }: {
      devShells.default = pkgs.mkShell {
        buildInputs = [
          (pkgs.agda.withPackages (ps: [
            ps.standard-library
          ]))
        ];
      };
    };
  };
}
