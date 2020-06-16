EBinOp (ENumLiteral 1, OpPlus, EEmptyHole 2)

EBinOp ((EBinOp (ENumLiteral 5, OpPlus, EEmptyHole 9)), OpPlus, EEmptyHole 2)

ELamAnn ("x", THole 10, EBinOp (ENumLiteral 1, OpPlus, EVar "x"))

ELamAnn ("x", THole 10,  EVar "x")