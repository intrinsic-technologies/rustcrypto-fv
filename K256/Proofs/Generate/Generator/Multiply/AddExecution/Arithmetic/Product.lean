import K256.Proofs.Generate.Generator.Multiply.AddExecution.Arithmetic.Cuts
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddGraph

open K256.Proofs.Common.Field K256.Proofs.Common.Point K256.Proofs.Common.Point.AddWords
open K256.Proofs.Common.Field.Multiply X86Proofs

open Lean Meta Elab Tactic

private theorem carry_sum_swap (a b c d e : Word) :
    a + b + c + d + e = b + a + 0 + c + d + e := by
  exact congrArg (fun t : Word => t + c + d + e) ((BitVec.add_comm a b).trans (BitVec.add_zero _).symm)

private def isGraphWord (n : Name) : Bool :=
  n.getPrefix == `K256.Proofs.Generate.Generator.Multiply.AddGraph && n.getString!.startsWith "w" &&
    ((n.getString!.drop 1).toString.toNat?).isSome

private partial def collectWordSteps (words : Array Name) (known : Std.HashMap Name Name)
    (seen : Std.HashSet Name := {}) (steps : Array Name := #[]) : MetaM (Array Name) := do
  let mut seen := seen
  let mut steps := steps
  let mut todo := words
  while let some word := todo.back? do
    todo := todo.pop
    if !isGraphWord word || seen.contains word then continue
    seen := seen.insert word
    if let some eqn := known[word]? then
      steps := steps.push eqn
    else
      let .defnInfo wordDef ← getConstInfo word | throwError "expected a graph word definition"
      steps := steps.push word
      todo := todo ++ wordDef.value.getUsedConstants
  return steps

elab "product_word" "[" stage:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let some (_, lhs, _) := (← getMainTarget).eq? | throwError "expected a word equality"
  let mut known : Std.HashMap Name Name := {}
  for d in ← getLCtx do
    if let some (_, l, _) := d.type.eq? then
      if let some n := l.getAppFn.constName? then
        if isGraphWord n then known := known.insert n d.userName
  let steps ← collectWordSteps lhs.getUsedConstants known
  let rules ← (steps.map mkIdent).mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  let rules := rules ++ stage.getElems
  evalTactic (← `(tactic|
    (simp only [$rules,*, wideMul, wideAdd, wideAddRev, high52, low52, low48, combine56,
        ofWord, Product.shiftWide, Product.scaleWide, SqrtSchedule.scaleHigh, BitVec.add_zero,
        BitVec.zero_add, BitVec.reduceSetWidth]
     all_goals first | rfl | exact carry_sum_swap _ _ _ _ _)))

private def nodeTerm (i : Nat) : TacticM Term := do
  let word := mkIdent (`K256.Proofs.Generate.Generator.Multiply.AddGraph ++ Name.mkSimple s!"w{i}")
  `($word $(mkIdent `p) $(mkIdent `q))

private def productStages : Array (Name × List Name) := #[
  (`c8, [`a, `b]), (`d3, [`a, `b, `c8]), (`d4, [`a, `b, `c8, `d3]), (`d5, [`a, `b, `d4]),
  (`r0, [`a, `b, `d4, `d5]), (`d6, [`a, `b, `d5]), (`r1, [`a, `b, `r0, `d6]),
  (`d7, [`a, `b, `d6]), (`r2, [`a, `b, `r1, `d7]), (`r3, [`d3, `d7, `r2])]

local elab "match_add_product " k:term:max s:term:max
    " left " "[" ls:num,* "]" " right " "[" rs:num,* "]"
    " columns " "[" ws:num,* "]" " output " "[" os:num,* "]" : tactic => do
  let a := mkIdent `a
  let b := mkIdent `b
  let p := mkIdent `p
  let q := mkIdent `q
  evalTactic (← `(tactic| let $a := rightInput $k $p $q))
  evalTactic (← `(tactic| let $b := leftInput $k $p $q))
  for (vector, indices) in #[(a, rs.getElems), (b, ls.getElems)] do
    for j in [:indices.size] do
      let i := indices[j]!.getNat
      let node ← nodeTerm i
      let fact := mkIdent (.mkSimple s!"h{i}")
      let idx := Syntax.mkNumLit (toString j)
      evalTactic (← `(tactic| have $fact : $node = $vector[$idx] := rfl))
  let ws := ws.getElems
  unless ws.size == 2 * productStages.size do throwError "expected ten pairs of low and high word indices"
  for j in [:productStages.size] do
    let (n, args) := productStages[j]!
    let stage := mkIdent n
    let f := mkIdent (`K256.Proofs.Common.Point.AddWords.Product ++ n)
    let args := args.toArray.map mkIdent
    evalTactic (← `(tactic| let $stage := $f $s $args*))
    for part in [:2] do
      let i := ws[2*j+part]!.getNat
      let node ← nodeTerm i
      let fact := mkIdent (.mkSimple s!"h{i}")
      let rhs ← if part == 0 then `(Prod.fst $stage) else `(Prod.snd $stage)
      evalTactic (← `(tactic| have $fact : $node = $rhs := by product_word [$stage:ident, $f:ident]))
  let os := os.getElems
  unless os.size == 5 || os.size == 6 do throwError "expected five output words or six words with a split top limb"
  let mut outputs ← (os.extract 0 5).mapM fun i => nodeTerm i.getNat
  if os.size == 6 then
    outputs := outputs.set! 4 (← `($(outputs[4]!) + $(← nodeTerm os[5]!.getNat)))
  let mut limbs := #[]
  let mut facts := #[]
  for j in [:5] do
    let stage := mkIdent (.mkSimple s!"r{min j 3}")
    let rhs ← if j < 4 then `(low52 $stage) else `(low48 $(mkIdent `d4) + high52 $stage)
    limbs := limbs.push rhs
    let fact := mkIdent (.mkSimple s!"limb{j}")
    evalTactic (← `(tactic| have $fact : $(outputs[j]!) = $rhs := by product_word []))
    facts := facts.push (← `(Lean.Parser.Tactic.rwRule| $fact:ident))
  evalTactic (← `(tactic| change #v[$outputs,*] = #v[$limbs,*]))
  evalTactic (← `(tactic| rw [$facts,*]))

theorem xx_product (p q : PointWords) :
    outputLimbs .xx p q = Raw.product .xx (leftInput .xx p q) (rightInput .xx p q) := by
  match_add_product .xx .diagonal
    left [9, 10, 11, 12, 13] right [24, 25, 26, 27, 28]
    columns [78, 77, 97, 101, 137, 142, 170, 173, 183, 186, 209, 212, 225, 228, 245, 248, 264, 267, 279, 282]
    output [195, 236, 270, 320, 315]

theorem yy_product (p q : PointWords) :
    outputLimbs .yy p q = Raw.product .yy (leftInput .yy p q) (rightInput .yy p q) := by
  match_add_product .yy .reverseCarry
    left [14, 15, 16, 17, 18] right [29, 30, 31, 32, 33]
    columns [313, 312, 333, 336, 373, 377, 403, 406, 413, 416, 438, 441, 454, 457, 475, 478, 494, 497, 509, 512]
    output [424, 465, 500, 548, 543]

theorem zz_product (p q : PointWords) :
    outputLimbs .zz p q = Raw.product .zz (leftInput .zz p q) (rightInput .zz p q) := by
  match_add_product .zz .diagonal
    left [19, 20, 21, 22, 23] right [34, 35, 36, 37, 38]
    columns [541, 540, 562, 566, 601, 605, 631, 634, 641, 644, 667, 670, 683, 686, 703, 706, 722, 725, 737, 740]
    output [653, 694, 728, 789, 784]

theorem xy_product (p q : PointWords) :
    outputLimbs .xy p q = Raw.product .xy (leftInput .xy p q) (rightInput .xy p q) := by
  match_add_product .xy .reverseCarry
    left [744, 752, 762, 770, 778] right [772, 764, 753, 746, 780]
    columns [783, 782, 802, 805, 840, 843, 870, 873, 880, 883, 904, 907, 920, 923, 940, 943, 959, 962, 973, 976]
    output [891, 931, 967, 990, 979]

theorem yz_product (p q : PointWords) :
    outputLimbs .yz p q = Raw.product .yz (leftInput .yz p q) (rightInput .yz p q) := by
  match_add_product .yz .diagonal
    left [1007, 1009, 1011, 1013, 1015] right [1017, 1019, 1021, 1023, 1029]
    columns [1036, 1035, 1055, 1058, 1093, 1096, 1122, 1125, 1132, 1135, 1156, 1159, 1172, 1175, 1192, 1195, 1211, 1214, 1225, 1228]
    output [1143, 1183, 1217, 1242, 1231]

theorem xz_product (p q : PointWords) :
    outputLimbs .xz p q = Raw.product .xz (leftInput .xz p q) (rightInput .xz p q) := by
  match_add_product .xz .diagonal
    left [1249, 1251, 1253, 1255, 1257] right [1259, 1261, 1263, 1265, 1267]
    columns [1284, 1283, 1304, 1307, 1342, 1345, 1371, 1374, 1381, 1384, 1405, 1408, 1421, 1424, 1441, 1444, 1460, 1463, 1474, 1477]
    output [1392, 1432, 1466, 1493, 1480]

theorem xLeft_product (p q : PointWords) :
    outputLimbs .xLeft p q = Raw.product .xLeft (leftInput .xLeft p q) (rightInput .xLeft p q) := by
  match_add_product .xLeft .fullCarry
    left [998, 1001, 1003, 1005, 1041] right [1549, 1556, 1561, 1566, 1572]
    columns [1700, 1699, 1718, 1721, 1761, 1764, 1791, 1794, 1802, 1805, 1827, 1830, 1842, 1845, 1865, 1868, 1884, 1887, 1901, 1904]
    output [1814, 1856, 1892, 1909, 1907]

theorem xRight_product (p q : PointWords) :
    outputLimbs .xRight p q = Raw.product .xRight (leftInput .xRight p q) (rightInput .xRight p q) := by
  match_add_product .xRight .xRight
    left [1685, 1686, 1687, 1688, 1629] right [1485, 1497, 1499, 1501, 1505]
    columns [1931, 1930, 1936, 1939, 1974, 1977, 2004, 2007, 2015, 2018, 2040, 2043, 2055, 2058, 2078, 2081, 2097, 2100, 2114, 2117]
    output [2025, 2069, 2105, 2146, 2120]

theorem yLeft_product (p q : PointWords) :
    outputLimbs .yLeft p q = Raw.product .yLeft (leftInput .yLeft p q) (rightInput .yLeft p q) := by
  match_add_product .yLeft .yLeft
    left [1550, 1557, 1562, 1567, 1573] right [1549, 1556, 1561, 1566, 1572]
    columns [2166, 2165, 2184, 2187, 2227, 2230, 2257, 2260, 2268, 2271, 2292, 2295, 2307, 2310, 2330, 2333, 2349, 2352, 2366, 2369]
    output [2277, 2321, 2357, 2387, 2382]

theorem yRight_product (p q : PointWords) :
    outputLimbs .yRight p q = Raw.product .yRight (leftInput .yRight p q) (rightInput .yRight p q) := by
  match_add_product .yRight .yRight
    left [1689, 1694, 1701, 1705, 1683] right [1485, 1497, 1499, 1501, 1505]
    columns [2381, 2380, 2400, 2403, 2439, 2442, 2469, 2472, 2480, 2483, 2505, 2508, 2520, 2523, 2543, 2546, 2562, 2565, 2579, 2582]
    output [2490, 2534, 2570, 2584, 2588]

theorem zLeft_product (p q : PointWords) :
    outputLimbs .zLeft p q = Raw.product .zLeft (leftInput .zLeft p q) (rightInput .zLeft p q) := by
  match_add_product .zLeft .fullCarry
    left [1269, 1271, 1277, 1285, 1290] right [1550, 1557, 1562, 1567, 1573]
    columns [2626, 2625, 2644, 2647, 2687, 2690, 2717, 2720, 2728, 2731, 2753, 2756, 2768, 2771, 2791, 2794, 2810, 2813, 2827, 2830]
    output [2740, 2782, 2818, 2852, 2856, 2839]

theorem zRight_product (p q : PointWords) :
    outputLimbs .zRight p q = Raw.product .zRight (leftInput .zRight p q) (rightInput .zRight p q) := by
  match_add_product .zRight .fullCarry
    left [2832, 2834, 2836, 2838, 2845] right [998, 1001, 1003, 1005, 1041]
    columns [2851, 2850, 2869, 2872, 2912, 2915, 2942, 2945, 2953, 2956, 2978, 2981, 2993, 2996, 3016, 3019, 3035, 3038, 3052, 3055]
    output [2965, 3007, 3046, 3057, 3061]

end K256.Proofs.Generate.Generator.Multiply.AddGraph
