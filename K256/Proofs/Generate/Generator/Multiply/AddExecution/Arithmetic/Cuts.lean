import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Graph
import K256.Proofs.Common.Point.AddWords.Raw

namespace K256.Proofs.Generate.Generator.Multiply.AddGraph

open K256.Proofs.Common.Field K256.Proofs.Common.Point K256.Proofs.Common.Point.AddWords
open K256.Proofs.Common.Field.Multiply X86Proofs

def leftInput (k : ProductKind) (p q : PointWords) : Limbs :=
  match k with
  | .xx => #v[w9 p q, w10 p q, w11 p q, w12 p q, w13 p q]
  | .yy => #v[w14 p q, w15 p q, w16 p q, w17 p q, w18 p q]
  | .zz => #v[w19 p q, w20 p q, w21 p q, w22 p q, w23 p q]
  | .xy => #v[w744 p q, w752 p q, w762 p q, w770 p q, w778 p q]
  | .yz => #v[w1007 p q, w1009 p q, w1011 p q, w1013 p q, w1015 p q]
  | .xz => #v[w1249 p q, w1251 p q, w1253 p q, w1255 p q, w1257 p q]
  | .xLeft => #v[w998 p q, w1001 p q, w1003 p q, w1005 p q, w1041 p q]
  | .xRight => #v[w1685 p q, w1686 p q, w1687 p q, w1688 p q, w1629 p q]
  | .yLeft => #v[w1550 p q, w1557 p q, w1562 p q, w1567 p q, w1573 p q]
  | .yRight => #v[w1689 p q, w1694 p q, w1701 p q, w1705 p q, w1683 p q]
  | .zLeft => #v[w1269 p q, w1271 p q, w1277 p q, w1285 p q, w1290 p q]
  | .zRight => #v[w2832 p q, w2834 p q, w2836 p q, w2838 p q, w2845 p q]

def rightInput (k : ProductKind) (p q : PointWords) : Limbs :=
  match k with
  | .xx => #v[w24 p q, w25 p q, w26 p q, w27 p q, w28 p q]
  | .yy => #v[w29 p q, w30 p q, w31 p q, w32 p q, w33 p q]
  | .zz => #v[w34 p q, w35 p q, w36 p q, w37 p q, w38 p q]
  | .xy => #v[w772 p q, w764 p q, w753 p q, w746 p q, w780 p q]
  | .yz => #v[w1017 p q, w1019 p q, w1021 p q, w1023 p q, w1029 p q]
  | .xz => #v[w1259 p q, w1261 p q, w1263 p q, w1265 p q, w1267 p q]
  | .xLeft => #v[w1549 p q, w1556 p q, w1561 p q, w1566 p q, w1572 p q]
  | .xRight => #v[w1485 p q, w1497 p q, w1499 p q, w1501 p q, w1505 p q]
  | .yLeft => #v[w1549 p q, w1556 p q, w1561 p q, w1566 p q, w1572 p q]
  | .yRight => #v[w1485 p q, w1497 p q, w1499 p q, w1501 p q, w1505 p q]
  | .zLeft => #v[w1550 p q, w1557 p q, w1562 p q, w1567 p q, w1573 p q]
  | .zRight => #v[w998 p q, w1001 p q, w1003 p q, w1005 p q, w1041 p q]

def outputLimbs (k : ProductKind) (p q : PointWords) : Limbs :=
  match k with
  | .xx => #v[w195 p q, w236 p q, w270 p q, w320 p q, w315 p q]
  | .yy => #v[w424 p q, w465 p q, w500 p q, w548 p q, w543 p q]
  | .zz => #v[w653 p q, w694 p q, w728 p q, w789 p q, w784 p q]
  | .xy => #v[w891 p q, w931 p q, w967 p q, w990 p q, w979 p q]
  | .yz => #v[w1143 p q, w1183 p q, w1217 p q, w1242 p q, w1231 p q]
  | .xz => #v[w1392 p q, w1432 p q, w1466 p q, w1493 p q, w1480 p q]
  | .xLeft => #v[w1814 p q, w1856 p q, w1892 p q, w1909 p q, w1907 p q]
  | .xRight => #v[w2025 p q, w2069 p q, w2105 p q, w2146 p q, w2120 p q]
  | .yLeft => #v[w2277 p q, w2321 p q, w2357 p q, w2387 p q, w2382 p q]
  | .yRight => #v[w2490 p q, w2534 p q, w2570 p q, w2584 p q, w2588 p q]
  | .zLeft => #v[w2740 p q, w2782 p q, w2818 p q, w2852 p q, w2856 p q + w2839 p q]
  | .zRight => #v[w2965 p q, w3007 p q, w3046 p q, w3057 p q, w3061 p q]

end K256.Proofs.Generate.Generator.Multiply.AddGraph
