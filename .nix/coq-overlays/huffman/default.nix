{ lib, mkCoqDerivation, version ? null, coq }:
with lib; mkCoqDerivation {
  pname = "huffman";
  inherit version;

  useDune = true;

  meta = {
    description = "Coq proof of the correctness of the Huffman coding algorithm";
    license = lib.licenses.lgpl21Plus;
  };
}
