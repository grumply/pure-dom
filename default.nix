{ mkDerivation, base, containers, pure-core, pure-default
, pure-json, pure-lifted, pure-queue, pure-txt, stdenv
}:
mkDerivation {
  pname = "pure-dom";
  version = "0.7.0.0";
  src = ./.;
  libraryHaskellDepends = [
    base containers pure-core pure-default pure-json pure-lifted
    pure-queue pure-txt
  ];
  homepage = "github.com/grumply/pure-dom";
  license = stdenv.lib.licenses.bsd3;
}
