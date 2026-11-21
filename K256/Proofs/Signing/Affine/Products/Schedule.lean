import K256.Proofs.Signing.Affine.Products.Input
import K256.Proofs.Generate.Generator.Affine.Memory
import K256.Proofs.Generate.Generator.Affine.Products.Multiply.Schedule

namespace K256.Proofs.Signing.Affine

open K256.Proofs.Generate.Generator.Affine
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC
open K256.Proofs.Common.Tactic
open Lean Meta Elab.Tactic

private theorem productLoadAddr {m : Ram} {a b : Word} (h : a = b) :
    memLoad m a 64 = memLoad m b 64 :=
  congrArg (fun p => memLoad m p 64) h

open Sec1.Sqrt.WordReads in
private partial def normalizeProductWord (env : Env) (e : Expr) :
    StateRefT (Std.HashMap Expr Simp.Result) MetaM Simp.Result := do
  unless e.hasFVar do return { expr := e }
  if let some r := (← get)[e]? then return r
  let r ←
    if e.isAppOfArity ``memLoad 5 then do
      let args := e.getAppArgs
      let addr ← normalizeProductWord env args[3]!
      let (offset, _) ← Meta.simp addr.expr env.shared.words.1 env.shared.words.2
      let addr ← addr.mkEqTrans offset
      let source := mkAppN e.getAppFn (args.set! 3 addr.expr)
      let load ← read env source
      let h := addr.proof?.map fun p =>
        mkAppN (mkConst ``productLoadAddr) #[args[2]!, args[3]!, addr.expr, p]
      let r : Simp.Result := { expr := source, proof? := h }
      let r ← r.mkEqTrans load
      r.mkEqTrans (← normalizeProductWord env load.expr)
    else if let .app f a := e then do
      let rf ← normalizeProductWord env f
      let ra ← normalizeProductWord env a
      Simp.mkCongr rf ra
    else pure { expr := e }
  modify (·.insert e r)
  return r

private theorem wordWidth (x : Word) : Value.mk 64 x = ⟨64,(Value.mk 64 x).get 64⟩ := by
  simp only [Value.get, BitVec.setWidth_eq]

private theorem productRegisterWidths {b : Registers}
    (h3 : b[3] = ⟨64, b[3].get 64⟩)
    (h5 : b[5] = ⟨64, b[5].get 64⟩)
    (h12 : b[12] = ⟨64, b[12].get 64⟩)
    (h13 : b[13] = ⟨64, b[13].get 64⟩)
    (h14 : b[14] = ⟨64, b[14].get 64⟩)
    (h15 : b[15] = ⟨64, b[15].get 64⟩) :
    ∀ j : Fin Reg.count, j.val ∈ [3,5,12,13,14,15] → b[j] = ⟨64, b[j].get 64⟩ := by
  rintro ⟨i, hi⟩ hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

private theorem productControlRegisters {a b : Registers}
    (h22 : b[22] = a[22])
    (h39 : b[39] = a[39])
    (h50 : b[50] = a[50])
    (h51 : b[51] = a[51]) :
    ∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → b[j] = a[j] := by
  rintro ⟨i, hi⟩ hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl <;> assumption

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem productBlockCall {x y w : Limbs} {sp source : Word} {a : Registers} {m : Ram}
    (rsp : a[4].get 64 = sp + 280) (src : a[6].get 64 = source)
    (scalar : a[2].get 64 = sp + 288) (dst : a[7].get 64 = sp + 376)
    (stack : Writable Extracted.programImage m (sp - 8) 336)
    (coords : Readable m source 80)
    (room : 8 ≤ sp.toNat) (high : sp.toNat + 464 ≤ 2^32)
    (above : sp.toNat + 520 ≤ source.toNat)
    (ha : WordsAt m source 64 x) (hb : WordsAt m (source + 40) 64 y)
    (hw : WordsAt m (sp + 288) 64 w)
    (ret : memLoad m (sp + 280) 64 = 0x10ee37) (df : a[22] = ⟨1,0⟩) :
    ∃ (b : Registers) (n : Ram),
      program.runBlock (dialect Extracted.programImage) ⟨.l10e4c0, a, m⟩ =
        .call ⟨.l114930, b, n⟩ (productNormalizeReturn .l10ecb2 0x10ecb2) ∧
      (WordsAt n (sp + 152) 64 (mulWords x w) ∧ WordsAt n (sp + 192) 64 (mulWords y w)) ∧
      (∀ x y : Limbs, WordsAt n (sp + 152) 64 x → WordsAt n (sp + 192) 64 y →
        ProductNormalizeInput sp b n x y) ∧
      ProductSlots sp n (a[3].get 64) (a[12].get 64) (a[14].get 64) (a[15].get 64) ∧
      (∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → b[j] = a[j]) ∧
      RamWriteFrame m n [⟨(sp - 8).toNat, 288⟩] := by
  have start : (sp - 8).toNat = sp.toNat - 8 := BitVec.toNat_sub_of_le room
  rw [Multiply.SqrtSchedule.mulWords_comm x w, ← Sec1.SqrtProducts.secondProduct_eq_mulWords y w]
  have data := And.intro ha (And.intro hb hw)
  lifted_inputs data
  lifted_registers [rsp, src, scalar, dst]
  refine Exists.intro ?regs (Exists.intro ?memory (And.intro ?run (And.intro ?words ?post)))
  case run =>
    generate_block [rsp, src, scalar, dst, Lift.reduceAddOffset, Lift.reduceSubOffset]
    coordinate_guards
    rfl
  case words =>
    constructor
    run_tac withMainContext do
      let shared ← Refine.Tactic.Shared.new #[]
      let inputs ← (List.range 15).toArray.mapM fun i => do
        Sec1.Sqrt.WordReads.inputOf (← getLocalDeclFromUserName (.mkSimple s!"word{i}"))
      let env : Sec1.Sqrt.WordReads.Env :=
        { shared, inputs, bases := #[(← getLocalDeclFromUserName `sp).toExpr, (← getLocalDeclFromUserName `source).toExpr] }
      let mut cache := {}
      let mut left := #[]
      for wordSet in ← getGoals do
        for g in ← Sec1.Sqrt.WordReads.wordGoals wordSet do
          let some (_, lhs, rhs) := (← g.getType).eq? | throwError "expected a word equality"
          let (normalized, cache') ← (normalizeProductWord env lhs).run cache
          cache := cache'
          let ty := mkApp (mkConst ``BitVec) (mkNatLit 64)
          let pureGoal ← mkFreshExprSyntheticOpaqueMVar
            (mkApp3 (mkConst ``Eq [.one]) ty normalized.expr rhs)
          g.assign (mkAppN (mkConst ``Eq.trans [.one])
            #[ty, lhs, normalized.expr, rhs, ← normalized.getProof, pureGoal])
          left := left.push pureGoal.mvarId!
      replaceMainGoal left.toList
    all_goals try dsimp -zeta only [Sec1.SqrtProducts.secondProduct, Sec1.SqrtProducts.secondCoefficients,
      Multiply.SqrtSchedule.reduceWords]
    all_goals first
      | lifted_word_eq []
      | (rw [BitVec.and_comm]; lifted_word_eq [])
  case post =>
    abstract_product_scratch
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y hx hy
      constructor
      case rsp | src => rfl
      case dst | base => apply congrArg (Value.mk 64); lifted_word_reads [] <;> rfl
      case df => exact df
      case saved => apply productRegisterWidths <;> exact wordWidth _
      case slot => lifted_word_reads [] <;> rfl
      case xAt => exact hx
      case yAt => exact hy
    · constructor <;> lifted_word_reads [ret] <;> rfl
    · exact productControlRegisters rfl rfl rfl rfl
    · have low : (sp - 8).toNat + 288 ≤ 2^32 := by omega
      coordinate_frame low

theorem coordinateProductBlock {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (h : ProductInput fr a m x y z) :
    let sp := fr.rsp - 520
    ∃ (b : Registers) (m' : Ram) (xl yl w : Limbs),
      program.runBlock (dialect Extracted.programImage) ⟨.l10e4c0, a, m⟩ =
        .call ⟨.l114930, b, m'⟩ (productNormalizeReturn .l10ecb2 0x10ecb2) ∧
      ProductNormalizeInput sp b m' (mulWords xl w) (mulWords yl w) ∧
      ProductSlots sp m' fr.rdi (sp + 376) fr.rsi 1 ∧
      (∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → b[j] = a[j]) ∧
      RamWriteFrame m m' [⟨(sp - 8).toNat, 288⟩] ∧
      FieldRepr xl x 8 ∧ FieldRepr yl y 8 ∧ FieldRepr w (inverse z) 8 := by
  let sp := fr.rsp - (520 : Word)
  have lower : Atom.All Extracted.programImage _ _ (Fn10fe50.frameAt .l10ee37 fr) := h.parent.atoms
  obtain ⟨_, df, bx, r14, _, _, _, _, _, _, _, _, _, _, _, _, win, room, _, _⟩ := lower
  simp (disch := decide) only [Atom.Holds, Fin.getElem_fin, Vector.getElem_set_ne] at df bx r14
  change Writable Extracted.programImage m (fr.rsp - 976) 976 at win
  change fr.low.toNat + 976 ≤ fr.rsp.toNat at room
  have low (k : Word) (hk : k.toNat ≤ 976) : (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have spNat : sp.toNat = fr.rsp.toNat - 520 := low 520 (by decide)
  have high := h.parent.source.low
  have above := h.parent.srcAbove
  have alignOff (k : Word) : fr.rsp - k = sp + (520 - k) := by dsimp only [sp]; bv_omega
  have win' : Writable Extracted.programImage m (sp - 8) 336 := by
    rw [show sp - 8 = fr.rsp - 528 by dsimp only [sp]; bv_omega]
    exact win.sub (by rw [low 976 (by decide), low 528 (by decide)]; simp only [BitVec.reduceToNat]; omega)
      (by rw [low 976 (by decide), low 528 (by decide)]; simp only [BitVec.reduceToNat]; omega)
  obtain ⟨xl, yl, _, hx, hy, _, rx, ry, _⟩ := h.coords.repr
  obtain ⟨w, hw, rw'⟩ := h.operand
  have coords := h.parent.source
  rw [alignOff 232] at hw
  have num := h.ret
  rw [alignOff 240] at num
  have get {r : Nat} {hr : r < Reg.count} {v : Word} (eq : a[r]'hr = ⟨64,v⟩) : (a[r]'hr).get 64 = v :=
    congrArg (Value.get 64) eq
  have rsp := (get h.sp).trans (alignOff 240)
  have fromSrc := get h.src
  have scalar := (get h.scalar).trans (alignOff 232)
  have dst := (get h.dst).trans (alignOff 144)
  have readable : Readable m fr.rsi 80 := coords.sub (Nat.le_refl _) (by omega)
  have room' : 8 ≤ sp.toNat := by omega
  have high' : sp.toNat + 464 ≤ 2^32 := by omega
  have above' : sp.toNat + 520 ≤ fr.rsi.toNat := by omega
  obtain ⟨b, n, run, ⟨xAt, yAt⟩, norm, slots, keep, frame⟩ := productBlockCall (a := a) (sp := sp)
    rsp fromSrc scalar dst win' readable room' high' above' hx hy hw num df
  change a[3] = ⟨64,fr.rdi⟩ at bx
  change a[14] = ⟨64,fr.rsi⟩ at r14
  rw [get bx, get h.address, get r14, get h.choice, alignOff 144] at slots
  exact ⟨b, n, xl, yl, w, run, norm _ _ xAt yAt, slots, keep, frame, rx, ry, rw'⟩

end K256.Proofs.Signing.Affine
