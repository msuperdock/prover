{ mkDerivation, base, brick, ieee754, stdenv, text, vty }:
mkDerivation {
  pname = "prover";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [ base brick ieee754 text vty ];
  license = stdenv.lib.licenses.mit;
}
