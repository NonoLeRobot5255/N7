{ pkgs ? import <nixpkgs> { config.permittedInsecurePackages = [ "python-2.7.18.12" ]; } }:
pkgs.mkShell {
  packages = [ pkgs.python2 pkgs.curl ];
  LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [
    pkgs.stdenv.cc.cc.lib
    pkgs.zlib
  ];
  shellHook = ''
    unset PYTHONNOUSERSITE
  '';
}
