{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/master";
  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in
    { devShell.${system} = pkgs.stdenv.mkDerivation rec {
      name = "env";
      buildInputs = with pkgs; [
        #elan # Should be installed manually
        python3
        poppler_utils
      ];
   };};
}
