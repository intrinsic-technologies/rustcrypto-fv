import P256.Proofs.Signing.Core.Iteration.Candidate.Select.Setup
import P256.Proofs.Signing.Core.Iteration.Candidate.Decode
import P256.Proofs.Scalar.Select.Correct
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)
open NextNonce (arguments_copy)

structure Selected [Bindings] (s t : RamState) (state : Nonce.State) (nonce : Nat) : Prop where
  frame : Frame s t
  arguments : StoredArguments s t
  generator : Nonce.GeneratorAt t (frameBase s + 2160) (frameBase s + 272) state
  scalar : Nat256At t (frameBase s + 432) nonce
  flag : (t.regValue .r12).setWidth 8 = 1
  positive : 0 < nonce
  canonical : nonce < Operations.domain.n
  rbp : t.regValue .rbp = frameBase s + 528
  rbx : t.regValue .rbx = frameBase s + 40
  r13 : t.regValue .r13 = frameBase s + 432
  r14 : t.regValue .r14 = frameBase s + 2160
  r15 : t.regValue .r15 = frameBase s + 1328

theorem select [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce : Nat} (pre : SignPre s boundary)
    (input : Decoded s t state nonce) (rip : t.RIP = 0x10cb11) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cb5f ∧ Selected s u state nonce := by
  obtain ⟨n, a, runA, frameA, effectA⟩ := Select.run pre input.frame rip
  have preserveA (offset len : Nat) (bound : offset + len ≤ 2280)
      (apart : offset + len ≤ 176 ∨ 208 ≤ offset) :
      ∀ i < len, a.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply word_writes_byte (Select.writes input.frame) effectA.agrees (by omega)
    intro off ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    constructor <;> omega
  have diA : a.regValue .rdi = frameBase s + 432 := effectA.writes.2.2.2.2.2.1.trans input.r13
  have siA : a.regValue .rsi = frameBase s + 176 := effectA.writes.2.2.2.2.2.2.1.trans (congrArg (· + 176) input.frame.rsp)
  have dxA : a.regValue .rdx = frameBase s + 528 := effectA.writes.2.2.2.2.2.2.2.1.trans input.rbp
  have flags : (a.regValue .r12).setWidth 8 = 1 ∧ (a.regValue .rcx).setWidth 8 = 1 := by
    have word : ((Operand.mem (rspOf t + 560) : Operand 32).read t).setWidth 8 = 1 := by
      change (memLoad t.external (rspOf t + 560) 32).setWidth 8 = 1
      rw [P256.Proofs.Common.Field.SquareRoot.memLoad_setWidth_of_le _ _ (by decide) (by decide)]
      have sp : rspOf t = frameBase s := input.frame.rsp
      rw [sp, memLoad_8]
      change ((t.external[frameBase s + 560]?).getD 0).toBitVec = 1
      rw [input.flag]
      rfl
    constructor
    · rw [show a.regValue .r12 = ((Operand.mem (rspOf t + 560) : Operand 32).read t).setWidth 64
        from effectA.writes.2.2.2.2.1,
        BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), word]
    · rw [show a.regValue .rcx = ((Operand.mem (rspOf t + 560) : Operand 32).read t).setWidth 64
        from effectA.writes.2.2.2.2.2.2.2.2,
        BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), word]
  obtain ⟨v, runV, readyV, effectV⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) (NextNonce.scalarFrame frameA) 0xcb5a 0x6701
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x13260 (by decide)) effectA.rip
  have effect : (callEffect (fun _ => 0x113260) 0x10cb5f a).Holds a v := effectV
  have cp := local_call_pre pre frameA readyV effect
    (inputBytes := 32) (outputBytes := 32) (reserve := 16)
    (inProgram_of_textOffset 0xcb5f (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (.inl (by decide)) siA diA
  have dxV : v.regValue .rdx = frameBase s + 528 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans dxA
  have diV : v.regValue .rdi = frameBase s + 432 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans diA
  have scalarV : Nat256At v (v.regValue .rdx) nonce := by
    rw [dxV]
    refine ⟨input.scalar.1, fun i hi => ?_⟩
    exact ((local_call_copy frameA effect (offset := 528) (len := 32) (by decide) i hi).trans
      (preserveA 528 32 (by decide) (.inr (by decide)) i hi)).trans (input.scalar.2 i hi)
  have readV : MemReadable v (v.regValue .rdx) 32 := by
    rw [dxV]
    exact readable_of_grow (local_readable pre frameA (by decide)) effect.agrees.grow
  have flagV : (v.regValue .rcx).setWidth 8 = 1 :=
    (congrArg (BitVec.setWidth 8) (effect.agrees.read (n := 64) (r := 1) (by simp))).trans flags.2
  have apartV : RangeApart (stackPtr v - 1) 1 (v.regValue .rdx) 32 := by
    have spV : stackPtr v = frameBase s - 8 := effect.writes.1.trans (congrArg (· - 8) frameA.rsp)
    rw [spV, dxV]
    intro i hi j hj
    have h := OffsetsApart.ne (c₁ := -9) (c₂ := 528) (len₁ := 1) (len₂ := 32)
      (by unfold OffsetsApart; decide +kernel) (frameBase s) hi hj (by decide)
    rw [BitVec.sub_sub]
    change frameBase s - 9 + BitVec.ofNat 64 i ≠ frameBase s + 528 + BitVec.ofNat 64 j
    rw [BitVec.sub_eq_add_neg]
    exact h
  obtain ⟨u, result, scalar⟩ := P256.Proofs.Scalar.Select.correct cp readV apartV scalarV flagV
  have preserve (offset len : Nat) (bound : offset + len ≤ 2280)
      (copyApart : offset + len ≤ 176 ∨ 208 ≤ offset)
      (resultApart : offset + len ≤ 432 ∨ 464 ≤ offset) :
      ∀ i < len, u.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (local_result_copy pre frameA effect result diA bound (by decide) resultApart i hi).trans
      (preserveA offset len bound copyApart i hi)
  have args := arguments_copy input.arguments (fun offset range => by
    obtain ⟨lo, hi⟩ := range
    have h := preserve offset 1 (by omega) (.inl (by omega)) (.inl (by omega)) 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h)
  have generator := input.generator.copy
    (preserve 2160 72 (by decide) (.inr (by decide)) (.inr (by decide)))
    ⟨input.generator.2.1.1, fun i hi =>
      (preserve 272 32 (by decide) (.inr (by decide)) (.inl (by decide)) i hi).trans
        (input.generator.2.1.2 i hi)⟩
  have registers (reg : Syntax.Reg) (member : reg ∈ [.rbp, .rbx, .r13, .r14, .r15]) :
      u.regValue reg = t.regValue reg := by
    refine (result.calleeSaved reg (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp)).trans ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact (effect.agrees.read (n := 64) (r := 5) (by simp)).trans
        (effectA.agrees.read (n := 64) (r := 5) (by simp [Select.Block.effect, Effect.components]))
    · exact (effect.agrees.read (n := 64) (r := 3) (by simp)).trans
        (effectA.agrees.read (n := 64) (r := 3) (by simp [Select.Block.effect, Effect.components]))
    · exact (effect.agrees.read (n := 64) (r := 13) (by simp)).trans
        (effectA.agrees.read (n := 64) (r := 13) (by simp [Select.Block.effect, Effect.components]))
    · exact (effect.agrees.read (n := 64) (r := 14) (by simp)).trans
        (effectA.agrees.read (n := 64) (r := 14) (by simp [Select.Block.effect, Effect.components]))
    · exact (effect.agrees.read (n := 64) (r := 15) (by simp)).trans
        (effectA.agrees.read (n := 64) (r := 15) (by simp [Select.Block.effect, Effect.components]))
  obtain ⟨m, runU⟩ := result.execution
  refine ⟨n+1+m, u, (runA.trans runV).trans runU,
    result.rip.trans (callEffect_stack effect).1,
    ⟨after_call pre frameA readyV effect result (by decide) (by decide) diA,
      args, generator, diV ▸ scalar, ?_, input.positive, input.canonical,
      (registers .rbp (by simp)).trans input.rbp,
      (registers .rbx (by simp)).trans input.rbx,
      (registers .r13 (by simp)).trans input.r13,
      (registers .r14 (by simp)).trans input.r14,
      (registers .r15 (by simp)).trans input.r15⟩⟩
  exact (congrArg (BitVec.setWidth 8) ((result.calleeSaved .r12 (by simp)).trans
    (effect.agrees.read (n := 64) (r := 12) (by simp)))).trans flags.1

end P256.Proofs.Signing.Core.Iteration.Candidate
