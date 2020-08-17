{ mkDerivation, aeson, base, brick, bytestring, directory, ieee754
, scientific, stdenv, text, vector, vty
}:
mkDerivation {
  pname = "prover";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    aeson base brick bytestring directory ieee754 scientific text
    vector vty
  ];
  description = "A simple interactive theorem prover";
  license = stdenv.lib.licenses.mit;
}
