import P256.Proofs.Sec1Serialize.Tail.State
import P256.Proofs.Sec1Serialize.Tail.Prepare.Effect
import P256.Proofs.Sec1Serialize.Tail.Prepare.EncodingMemory
import P256.Proofs.Sec1Serialize.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

open P256.Proofs.Common.Instructions (bswap64)
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame

theorem prepareEncodingEffect_savedInput {t u : RamState}
    (effect : (prepareEncodingEffect t).Holds t u) :
    (Operand.mem (rspOf t + 120) : Operand 64).read u =
      (Operand.mem (rspOf t + 120) : Operand 64).read t := by
  apply read_mem_of_agrees effect.agrees
  intro i hi c hc hcov
  have apart (offset len : Nat) (ho : offset + len ≤ 120 ∨ 128 ≤ offset)
      (hb : offset+len ≤ 2^64) :
      ¬ (Component.mem (rspOf t + BitVec.ofNat 64 offset) len).Covers
        (rspOf t + 120 + BitVec.ofNat 64 i) := by
    rintro ⟨j,hj,he⟩
    exact RangeApart.offsets (rspOf t) (a := offset) (b := 120)
      (len := len) (count := 8) hb (by decide) ho j hj i hi he.symm
  simp only [prepareEncodingEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · exact apart 88 8 (by decide) (by decide) hcov
  · exact apart 96 8 (by decide) (by decide) hcov
  · exact apart 104 8 (by decide) (by decide) hcov
  · exact apart 112 8 (by decide) (by decide) hcov
  · exact apart 40 8 (by decide) (by decide) hcov
  · exact apart 32 8 (by decide) (by decide) hcov
  · exact apart 24 8 (by decide) (by decide) hcov
  · exact apart 16 8 (by decide) (by decide) hcov
  · exact apart 200 8 (by decide) (by decide) hcov
  · exact apart 208 8 (by decide) (by decide) hcov
  · exact apart 216 8 (by decide) (by decide) hcov
  · exact apart 224 8 (by decide) (by decide) hcov
  · exact apart 199 1 (by decide) (by decide) hcov
  · exact apart 232 8 (by decide) (by decide) hcov
  · exact apart 240 8 (by decide) (by decide) hcov
  · exact apart 248 8 (by decide) (by decide) hcov
  · exact apart 256 8 (by decide) (by decide) hcov

theorem encoded_post [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x y : Nat} {infinity : Bool}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : FrameState s t 65 328 312) (finalStage : FrameState s u 65 328 312)
    (execution : ∃ n, Advances boundary n s u)
    (effect : (prepareEncodingEffect t).Holds t u)
    (converted : Converted t x y) (rdi : t.regValue .rdi = s.regValue .rdi)
    (savedInput : (Operand.mem (stackPtr s - 192) : Operand 64).read t = s.regValue .rsi)
    (inputFlag : t.external[s.regValue .rsi + 64]? = some (if infinity then 1 else 0)) :
    EncodedEntry s u boundary (Points.encode (.affine x y)) infinity := by
  have hdest := effect.writes.2.1
  have hx3 := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hx2 := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hx1 := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hx0 := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htag := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hy3 := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hy2 := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hy1 := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hy0 := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hbase : rspOf t + 199 = stackPtr s - 113 := by
    change stackPtr t + 199 = _
    rw [stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have haddr (offset : Nat) : stackPtr s - 113 + BitVec.ofNat 64 offset =
      rspOf t + BitVec.ofNat 64 (199+offset) := by
    rw [← hbase, BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  have hsaved : stackPtr s - 192 = rspOf t + 120 := by
    change _ = stackPtr t + 120
    rw [stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  refine ⟨finalStage, execution, effect.rip, hdest.trans rdi, ?_, ?_, ?_⟩
  · apply encoded_hasBytes (a := stackPtr s-113)
    · intro i hi
      have h := readable_of_grow
        (stack_sub_readable pre.stack (offset := 113) (len := 65) (by decide) (by decide))
        finalStage.allocated
      exact h.mem i hi
    · rw [← hbase]
      exact htag
    · intro j hj
      rw [haddr]
      rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl | rfl | rfl | rfl
      · change (Operand.mem (rspOf t+200) : Operand 64).read u = bswap64 (canonicalLimb x 3)
        exact hx3.trans (congrArg bswap64 converted.x3)
      · change (Operand.mem (rspOf t+208) : Operand 64).read u = bswap64 (canonicalLimb x 2)
        exact hx2.trans (congrArg bswap64 converted.x2)
      · change (Operand.mem (rspOf t+216) : Operand 64).read u = bswap64 (canonicalLimb x 1)
        exact hx1.trans (congrArg bswap64 converted.x1)
      · change (Operand.mem (rspOf t+224) : Operand 64).read u = bswap64 (canonicalLimb x 0)
        exact hx0.trans (congrArg bswap64 converted.x0)
    · intro j hj
      rw [haddr]
      rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl | rfl | rfl | rfl
      · change (Operand.mem (rspOf t+232) : Operand 64).read u = bswap64 (canonicalLimb y 3)
        exact hy3.trans (congrArg bswap64 converted.y3)
      · change (Operand.mem (rspOf t+240) : Operand 64).read u = bswap64 (canonicalLimb y 2)
        exact hy2.trans (congrArg bswap64 converted.y2)
      · change (Operand.mem (rspOf t+248) : Operand 64).read u = bswap64 (canonicalLimb y 1)
        exact hy1.trans (congrArg bswap64 converted.y1)
      · change (Operand.mem (rspOf t+256) : Operand 64).read u = bswap64 (canonicalLimb y 0)
        exact hy0.trans (congrArg bswap64 converted.y0)
  · rw [hsaved, prepareEncodingEffect_savedInput effect]
    exact hsaved ▸ savedInput
  · exact (input_byte pre finalStage (i := 64) (by decide)).trans
      ((input_byte pre stage (i := 64) (by decide)).symm.trans inputFlag)

end P256.Proofs.Sec1Serialize.Prepare
