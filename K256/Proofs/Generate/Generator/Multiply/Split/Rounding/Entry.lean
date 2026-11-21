import K256.Proofs.Generate.Generator.Multiply.Split.Rounding.Frame
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.ProductFlags

namespace K256.Proofs.Generate.Generator.Multiply.Split.Rounding

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

open Lean Meta Elab Tactic in
elab "rounded_input_words" : tactic => withMainContext do
  let shared ← Refine.Tactic.Shared.new #[]
  let regions ← Refine.Tactic.regions
  let env : K256.Proofs.Sec1.Sqrt.WordReads.Env := {shared, inputs := #[], bases := regions.map (·.addr.base)}
  let goal ← getMainGoal
  let some goalTy ← whnfUntil (← instantiateMVars (← goal.getType)) ``WordsAt | throwError "expected stored words"
  let gs ← K256.Proofs.Sec1.Sqrt.WordReads.wordGoals (← goal.change goalTy)
  for g in gs do
    let some (_,l,r) := (← whnfR (← instantiateMVars (← g.getType))).eq? | throwError "expected word equality"
    let addr := l.getArg! 3
    let some i ← K256.Proofs.CFG.Eval.indexValue? addr.appArg! | throwError "expected literal limb index"
    let names := #[`offset0,`offset1,`offset2,`offset3]
    let off ← getLocalDeclFromUserName names[i]!
    let some (_,_,pos) := off.type.eq? | throwError "expected slot equality"
    let args := l.getAppArgs
    let atPos := mkAppN l.getAppFn (args.set! 3 pos)
    let moved ← mkCongrFun (← mkCongrArg (mkAppN l.getAppFn (args.extract 0 3)) off.toExpr) args[4]!
    let lhs ← K256.Proofs.Sec1.Sqrt.WordReads.read env atPos
    let some word ← K256.Proofs.CFG.Eval.getElem? r | throwError "expected four stored words"
    let rhs ← K256.Proofs.Sec1.Sqrt.WordReads.exposeLimb word
    unless ← withReducible (isDefEq lhs.expr rhs.expr) do throwError "different selected word"
    let pp ← mkEqTrans (← lhs.getProof) (← mkEqSymm (← rhs.getProof))
    g.assign (← mkEqTrans moved pp)
  replaceMainGoal []

open Lean Meta Elab Tactic in
elab "expose_round_word" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_,l,r) := (← whnfR (← instantiateMVars (← g.getType))).eq? | throwError "expected a register word equality"
  let q ← K256.Proofs.Sec1.Sqrt.WordReads.exposeLimb l
  let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq q.expr r)
  g.assign (← mkEqTrans (← q.getProof) g')
  replaceMainGoal [g'.mvarId!]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3500000 in
theorem enterAdd {x y : Vector (BitVec 64) 4} {fr : Activation} {a : Registers} {m : Ram}
    (entry : Atom.All Extracted.programImage a m (Fn11b8f0.frameAt .l11b8f0 fr))
    (left : Readable m fr.rsi 32) (right : Readable m fr.rdx 32)
    (apart : ∀ src ∈ [fr.rsi, fr.rdx], src.toNat + 32 ≤ fr.rsp.toNat - 0xe0 ∨
      fr.rsp.toNat + 8 ≤ src.toNat)
    (wx : WordsAt m fr.rsi 64 x) (wy : WordsAt m fr.rdx 64 y) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l11b8f0, a, m⟩ =
        .call ⟨.l1109b0, b, n⟩ ⟨.l11badf, #v[], rfl, some ⟨64, 0x11badf⟩⟩ ∧
      Atom.All Extracted.programImage b n (Fn1109b0.frameAt .l1109b0 (addFrame fr b)) ∧
      RamWriteFrame m n [⟨fr.rsp.toNat - 0xe0,0xe0⟩] ∧ AdditionFrame fr n ∧
      WordsAt n (fr.rsp-112) 64 #v[b[3].get 64,b[12].get 64,0,0] ∧
      b[3].get 64 = (ProductSchedule.machineProduct x y)[6] ∧
      b[12].get 64 = (ProductSchedule.machineProduct x y)[7] ∧
      b[15].get 64 = (ProductSchedule.machineProduct x y)[5] >>> 63 := by
  simp only [Fn11b8f0.frameAt, Fn11b8f0.frameAtG1, Atom.All, Atom.Holds] at entry
  obtain ⟨sp, df, cx, dx, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ftw, fcw,
    retRead, ret, retLow, stack, low, align, _⟩ := entry
  have ls := apart fr.rsi (by simp)
  have rs := apart fr.rdx (by simp)
  have g4 : a[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have g7 : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have g2 : a[2].get 64 = fr.rdx := congrArg (Value.get 64) dx
  have g6 : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have g5 : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have g3 : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have g12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have g13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have g14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have g15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have wordx0 : memLoad m fr.rsi 64 = x[0] := by simpa [wordAddr] using wx 0 (by decide)
  have wordx1 : memLoad m (fr.rsi + 8) 64 = x[1] := wx 1 (by decide)
  have wordx2 : memLoad m (fr.rsi + 16) 64 = x[2] := wx 2 (by decide)
  have wordx3 : memLoad m (fr.rsi + 24) 64 = x[3] := wx 3 (by decide)
  have wordy0 : memLoad m fr.rdx 64 = y[0] := by simpa [wordAddr] using wy 0 (by decide)
  have wordy1 : memLoad m (fr.rdx + 8) 64 = y[1] := wy 1 (by decide)
  have wordy2 : memLoad m (fr.rdx + 16) 64 = y[2] := wy 2 (by decide)
  have wordy3 : memLoad m (fr.rdx + 24) 64 = y[3] := wy 3 (by decide)
  refine ⟨?valuesAfterRound, ?memoryAfterRound, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l11b8f0 [g4,g7,g2,g6,g5,g3,g12,g13,g14,g15,
      wordx0,wordx1,wordx2,wordx3,wordy0,wordy1,wordy2,wordy3,
      Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
      BitVec.reduceAdd, BitVec.reduceSub]
  case post =>
    have ofs (k : BitVec 64) (hk : k.toNat ≤ 224) :
        (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Fn1109b0.frameAt, Fn1109b0.frameAtG1, Atom.All, Atom.Holds]
      refine ⟨rfl,df,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,mx,ftw,fcw,
        ?_, ?_, by decide, ?_, ?_, ?_, trivial⟩
      · slot_state region
      · refine_norm []
      · simp only [Lift.reduceSubOffset]
        slot_state region
      · rw [ofs 160 (by decide)]
        change fr.low.toNat + 64 ≤ fr.rsp.toNat - 160
        omega
      · rw [ofs 160 (by decide)]
        change (fr.rsp.toNat - 160) % 16 = 8
        omega
    · slot_state region
    · refine ⟨?_, ?_, ?_, retLow, ?_, low, align⟩
      · intro k r h
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
          refine_norm [Activation.entryReg]
      · slot_state region
      · refine_norm [ret]
      · slot_state region
    · have offset0 : wordAddr (fr.rsp - 112) 64 0 = fr.rsp - 112 := by
        change fr.rsp - 112 + 0 = fr.rsp - 112
        bv_omega
      have offset1 : wordAddr (fr.rsp - 112) 64 1 = fr.rsp - 104 := by
        change fr.rsp - 112 + 8 = fr.rsp - 104
        bv_omega
      have offset2 : wordAddr (fr.rsp - 112) 64 2 = fr.rsp - 96 := by
        change fr.rsp - 112 + 16 = fr.rsp - 96
        bv_omega
      have offset3 : wordAddr (fr.rsp - 112) 64 3 = fr.rsp - 88 := by
        change fr.rsp - 112 + 24 = fr.rsp - 88
        bv_omega
      rounded_input_words
    all_goals expose_round_word <;> match_product_words

end K256.Proofs.Generate.Generator.Multiply.Split.Rounding
