import K256.Proofs.Common.Point.DoubleWords.Replay
import K256.Proofs.Common.Point.AddWords.Product
import Lean

namespace K256.Proofs.Common.Point.DoubleWords.Replay

open Field Field.Multiply Field.Multiply.SqrtSchedule AddWords X86Proofs
open Lean Meta Elab Tactic

private theorem carry_sum_swap (a b c d e : Word) :
    a + b + c + d + e = b + a + 0 + c + d + e := by
  exact congrArg (fun t : Word => t + c + d + e) ((BitVec.add_comm a b).trans (BitVec.add_zero _).symm)

private def isGraphWord (n : Name) : Bool :=
  n.getPrefix == `K256.Proofs.Common.Point.DoubleWords.Replay && n.getString!.startsWith "w" &&
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

elab "double_product_word" "[" stage:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
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
        BitVec.zero_add, BitVec.reduceSetWidth, BitVec.zero_mul]
     all_goals first | rfl | exact carry_sum_swap _ _ _ _ _ | ac_rfl)))


local macro "w[" i:num "]" : term =>
  `($(Lean.mkIdent (Lean.Name.mkSimple s!"w{i.getNat}"))
    $(Lean.mkIdent `p) $(Lean.mkIdent `yy) $(Lean.mkIdent `zz) $(Lean.mkIdent `sp))

theorem xy_words (p : PointWords) (yy zz : Limbs) (sp : Word) :
    #v[w[163] &&& 0xfffffffffffff, w[202] &&& 0xfffffffffffff, w[240] &&& 0xfffffffffffff, w[253] &&& 0xfffffffffffff, w[260]] = Product.words .reverseCarry (p.y) (p.x) := by
  let a := p.y
  let b := p.x
  have h7 : w[7] = a[0] := rfl
  have h8 : w[8] = a[1] := rfl
  have h9 : w[9] = a[2] := rfl
  have h10 : w[10] = a[3] := rfl
  have h11 : w[11] = a[4] := rfl
  have h2 : w[2] = b[0] := rfl
  have h3 : w[3] = b[1] := rfl
  have h4 : w[4] = b[2] := rfl
  have h5 : w[5] = b[3] := rfl
  have h6 : w[6] = b[4] := rfl
  let c8 := Product.c8 .reverseCarry a b
  have h58 : w[58] = c8.1 := by double_product_word [c8, Product.c8]
  have h57 : w[57] = c8.2 := by double_product_word [c8, Product.c8]
  let d3 := Product.d3 .reverseCarry a b c8
  have h75 : w[75] = d3.1 := by double_product_word [d3, Product.d3]
  have h79 : w[79] = d3.2 := by double_product_word [d3, Product.d3]
  let d4 := Product.d4 .reverseCarry a b c8 d3
  have h119 : w[119] = d4.1 := by double_product_word [d4, Product.d4]
  have h123 : w[123] = d4.2 := by double_product_word [d4, Product.d4]
  let d5 := Product.d5 .reverseCarry a b d4
  have h151 : w[151] = d5.1 := by double_product_word [d5, Product.d5]
  have h154 : w[154] = d5.2 := by double_product_word [d5, Product.d5]
  let r0 := Product.r0 .reverseCarry a b d4 d5
  have h163 : w[163] = r0.1 := by double_product_word [r0, Product.r0]
  have h166 : w[166] = r0.2 := by double_product_word [r0, Product.r0]
  let d6 := Product.d6 .reverseCarry a b d5
  have h186 : w[186] = d6.1 := by double_product_word [d6, Product.d6]
  have h189 : w[189] = d6.2 := by double_product_word [d6, Product.d6]
  let r1 := Product.r1 .reverseCarry a b r0 d6
  have h202 : w[202] = r1.1 := by double_product_word [r1, Product.r1]
  have h205 : w[205] = r1.2 := by double_product_word [r1, Product.r1]
  let d7 := Product.d7 .reverseCarry a b d6
  have h221 : w[221] = d7.1 := by double_product_word [d7, Product.d7]
  have h224 : w[224] = d7.2 := by double_product_word [d7, Product.d7]
  let r2 := Product.r2 .reverseCarry a b r1 d7
  have h240 : w[240] = r2.1 := by double_product_word [r2, Product.r2]
  have h243 : w[243] = r2.2 := by double_product_word [r2, Product.r2]
  let r3 := Product.r3 .reverseCarry d3 d7 r2
  have h253 : w[253] = r3.1 := by double_product_word [r3, Product.r3]
  have h256 : w[256] = r3.2 := by double_product_word [r3, Product.r3]
  have limb0 : w[163] &&& 0xfffffffffffff = low52 r0 := by double_product_word []
  have limb1 : w[202] &&& 0xfffffffffffff = low52 r1 := by double_product_word []
  have limb2 : w[240] &&& 0xfffffffffffff = low52 r2 := by double_product_word []
  have limb3 : w[253] &&& 0xfffffffffffff = low52 r3 := by double_product_word []
  have limb4 : w[260] = low48 d4 + high52 r3 := by double_product_word []
  change _ = #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]
  rw [limb0, limb1, limb2, limb3, limb4]

theorem yyzz_words (p : PointWords) (yy zz : Limbs) (sp : Word) :
    #v[w[517], w[557], w[593], w[628], w[605]] = Product.words .diagonal (zz) (yy) := by
  let a := zz
  let b := yy
  have h22 : w[22] = a[0] := rfl
  have h23 : w[23] = a[1] := rfl
  have h24 : w[24] = a[2] := rfl
  have h25 : w[25] = a[3] := rfl
  have h26 : w[26] = a[4] := rfl
  have h17 : w[17] = b[0] := rfl
  have h18 : w[18] = b[1] := rfl
  have h19 : w[19] = b[2] := rfl
  have h20 : w[20] = b[3] := rfl
  have h21 : w[21] = b[4] := rfl
  let c8 := Product.c8 .diagonal a b
  have h406 : w[406] = c8.1 := by double_product_word [c8, Product.c8]
  have h405 : w[405] = c8.2 := by double_product_word [c8, Product.c8]
  let d3 := Product.d3 .diagonal a b c8
  have h429 : w[429] = d3.1 := by double_product_word [d3, Product.d3]
  have h432 : w[432] = d3.2 := by double_product_word [d3, Product.d3]
  let d4 := Product.d4 .diagonal a b c8 d3
  have h467 : w[467] = d4.1 := by double_product_word [d4, Product.d4]
  have h470 : w[470] = d4.2 := by double_product_word [d4, Product.d4]
  let d5 := Product.d5 .diagonal a b d4
  have h496 : w[496] = d5.1 := by double_product_word [d5, Product.d5]
  have h499 : w[499] = d5.2 := by double_product_word [d5, Product.d5]
  let r0 := Product.r0 .diagonal a b d4 d5
  have h506 : w[506] = r0.1 := by double_product_word [r0, Product.r0]
  have h509 : w[509] = r0.2 := by double_product_word [r0, Product.r0]
  let d6 := Product.d6 .diagonal a b d5
  have h530 : w[530] = d6.1 := by double_product_word [d6, Product.d6]
  have h533 : w[533] = d6.2 := by double_product_word [d6, Product.d6]
  let r1 := Product.r1 .diagonal a b r0 d6
  have h546 : w[546] = r1.1 := by double_product_word [r1, Product.r1]
  have h549 : w[549] = r1.2 := by double_product_word [r1, Product.r1]
  let d7 := Product.d7 .diagonal a b d6
  have h566 : w[566] = d7.1 := by double_product_word [d7, Product.d7]
  have h569 : w[569] = d7.2 := by double_product_word [d7, Product.d7]
  let r2 := Product.r2 .diagonal a b r1 d7
  have h585 : w[585] = r2.1 := by double_product_word [r2, Product.r2]
  have h588 : w[588] = r2.2 := by double_product_word [r2, Product.r2]
  let r3 := Product.r3 .diagonal d3 d7 r2
  have h599 : w[599] = r3.1 := by double_product_word [r3, Product.r3]
  have h602 : w[602] = r3.2 := by double_product_word [r3, Product.r3]
  have limb0 : w[517] = low52 r0 := by double_product_word []
  have limb1 : w[557] = low52 r1 := by double_product_word []
  have limb2 : w[593] = low52 r2 := by double_product_word []
  have limb3 : w[628] = low52 r3 := by double_product_word []
  have limb4 : w[605] = low48 d4 + high52 r3 := by double_product_word []
  change _ = #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]
  rw [limb0, limb1, limb2, limb3, limb4]

theorem yyy_words (p : PointWords) (yy zz : Limbs) (sp : Word) :
    #v[w[1052], w[1053], w[1054], w[1055], w[1050]] = Product.words .reverseCarry (p.y) (yy) := by
  let a := p.y
  let b := yy
  have h7 : w[7] = a[0] := rfl
  have h8 : w[8] = a[1] := rfl
  have h9 : w[9] = a[2] := rfl
  have h10 : w[10] = a[3] := rfl
  have h11 : w[11] = a[4] := rfl
  have h17 : w[17] = b[0] := rfl
  have h18 : w[18] = b[1] := rfl
  have h19 : w[19] = b[2] := rfl
  have h20 : w[20] = b[3] := rfl
  have h21 : w[21] = b[4] := rfl
  let c8 := Product.c8 .reverseCarry a b
  have h857 : w[857] = c8.1 := by double_product_word [c8, Product.c8]
  have h856 : w[856] = c8.2 := by double_product_word [c8, Product.c8]
  let d3 := Product.d3 .reverseCarry a b c8
  have h877 : w[877] = d3.1 := by double_product_word [d3, Product.d3]
  have h880 : w[880] = d3.2 := by double_product_word [d3, Product.d3]
  let d4 := Product.d4 .reverseCarry a b c8 d3
  have h915 : w[915] = d4.1 := by double_product_word [d4, Product.d4]
  have h918 : w[918] = d4.2 := by double_product_word [d4, Product.d4]
  let d5 := Product.d5 .reverseCarry a b d4
  have h944 : w[944] = d5.1 := by double_product_word [d5, Product.d5]
  have h947 : w[947] = d5.2 := by double_product_word [d5, Product.d5]
  let r0 := Product.r0 .reverseCarry a b d4 d5
  have h954 : w[954] = r0.1 := by double_product_word [r0, Product.r0]
  have h957 : w[957] = r0.2 := by double_product_word [r0, Product.r0]
  let d6 := Product.d6 .reverseCarry a b d5
  have h977 : w[977] = d6.1 := by double_product_word [d6, Product.d6]
  have h980 : w[980] = d6.2 := by double_product_word [d6, Product.d6]
  let r1 := Product.r1 .reverseCarry a b r0 d6
  have h993 : w[993] = r1.1 := by double_product_word [r1, Product.r1]
  have h996 : w[996] = r1.2 := by double_product_word [r1, Product.r1]
  let d7 := Product.d7 .reverseCarry a b d6
  have h1012 : w[1012] = d7.1 := by double_product_word [d7, Product.d7]
  have h1015 : w[1015] = d7.2 := by double_product_word [d7, Product.d7]
  let r2 := Product.r2 .reverseCarry a b r1 d7
  have h1031 : w[1031] = r2.1 := by double_product_word [r2, Product.r2]
  have h1034 : w[1034] = r2.2 := by double_product_word [r2, Product.r2]
  let r3 := Product.r3 .reverseCarry d3 d7 r2
  have h1044 : w[1044] = r3.1 := by double_product_word [r3, Product.r3]
  have h1047 : w[1047] = r3.2 := by double_product_word [r3, Product.r3]
  have limb0 : w[1052] = low52 r0 := by double_product_word []
  have limb1 : w[1053] = low52 r1 := by double_product_word []
  have limb2 : w[1054] = low52 r2 := by double_product_word []
  have limb3 : w[1055] = low52 r3 := by double_product_word []
  have limb4 : w[1050] = low48 d4 + high52 r3 := by double_product_word []
  change _ = #v[low52 r0, low52 r1, low52 r2, low52 r3, low48 d4 + high52 r3]
  rw [limb0, limb1, limb2, limb3, limb4]

end K256.Proofs.Common.Point.DoubleWords.Replay
