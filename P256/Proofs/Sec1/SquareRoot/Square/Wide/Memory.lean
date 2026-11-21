import P256.Proofs.Sec1.SquareRoot.Square.Wide.BodyInterface
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Frame
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

open P256.Proofs.Program (CalleePre inProgram_of_textOffset memoryRegion_contains_add memoryRegion_memReadable)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Common.Field.SquareRoot

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem input_readable (pre : CalleePre s boundary 0x11cba0 32 64 88)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    {off : Nat} (ho : off+8 ≤ 32) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 off) 8 := by
  apply P256.Proofs.Program.readable_of_grow _ grow
  exact P256.Proofs.Common.Memory.memReadable_sub
    (memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (Nat.le_refl _))
    off 8 ho

theorem stack_writable (pre : CalleePre s boundary 0x11cba0 32 64 88)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    {off : Nat} (ho : off ≤ 88) (ha : off % 8 = 0) :
    MemWritable t (stackPtr s-88+BitVec.ofNat 64 off) 8 := by
  rw [scratch_address s ho]
  exact P256.Proofs.Program.writable_of_grow
    (P256.Proofs.Program.stack_sub_writable8 pre.stack
      (fun a ha => pre.avoids _ (by simp) a ha ∘ Or.inr) (by omega) (by omega)) grow

theorem stack_code_apart (pre : CalleePre s boundary 0x11cba0 32 64 88)
    {off : Nat} (ho : off+8 ≤ 88) (offset len : Nat) (hc : offset+len ≤ 118431) :
    RangeApart (stackPtr s-88+BitVec.ofNat 64 off) 8
      (Extracted.textAddress+BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 88) (by simp) _
    (scratch_inside pre ho ⟨i,hi,rfl⟩) (.inl ?_)
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset+j) (by omega)

theorem output_code_apart (pre : CalleePre s boundary 0x11cba0 32 64 88)
    {off : Nat} (ho : off+8 ≤ 64) (offset len : Nat) (hc : offset+len ≤ 118431) :
    RangeApart (s.regValue .rdi+BitVec.ofNat 64 off) 8
      (Extracted.textAddress+BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply pre.avoids (registerRegion s .rdi 64) (by simp)
    (s.regValue .rdi+BitVec.ofNat 64 off+BitVec.ofNat 64 i) _ (.inl ?_)
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
      (show off+i < 64 by omega)
  · rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (offset+j) (by omega)

theorem stack_input_apart (pre : CalleePre s boundary 0x11cba0 32 64 88)
    {off j : Nat} (ho : off+8 ≤ 88) (hj : j+8 ≤ 32) :
    RangeApart (stackPtr s-88+BitVec.ofNat 64 off) 8
      (s.regValue .rsi+BitVec.ofNat 64 j) 8 := by
  intro i hi k hk he
  have hin : (registerRegion s .rsi 32).Contains
      (s.regValue .rsi+BitVec.ofNat 64 j+BitVec.ofNat 64 k).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _)
      (show j+k < 32 by omega)
  exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hin
    (he ▸ scratch_inside pre ho ⟨i,hi,rfl⟩)

theorem stack_output_apart (pre : CalleePre s boundary 0x11cba0 32 64 88)
    {off j : Nat} (ho : off+8 ≤ 88) (hj : j+8 ≤ 64) :
    RangeApart (stackPtr s-88+BitVec.ofNat 64 off) 8
      (s.regValue .rdi+BitVec.ofNat 64 j) 8 := by
  intro i hi k hk he
  have hin : (registerRegion s .rdi 64).Contains
      (s.regValue .rdi+BitVec.ofNat 64 j+BitVec.ofNat 64 k).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
      (show j+k < 64 by omega)
  exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hin
    (he ▸ scratch_inside pre ho ⟨i,hi,rfl⟩)

theorem bodyPre_of_prologue (pre : CalleePre s boundary 0x11cba0 32 64 88)
    (hip : t.RIP = 0x11cbb8) (hsp : stackPtr t = stackPtr s-88)
    (hf : AgreesExcept (Multiply.prologueComponents s) s t) : BodyPre t := by
  have hsi : (Operand.reg 6 : Operand 64).read t = s.regValue .rsi :=
    hf.read (by simp [Multiply.prologueComponents])
  have hdi : (Operand.reg 7 : Operand 64).read t = s.regValue .rdi :=
    hf.read (by simp [Multiply.prologueComponents])
  have hrsp : (Operand.reg 4 : Operand 64).read t = stackPtr s-88 := hsp
  refine ⟨hip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hsi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact input_readable pre hf.grow (by decide)
  · intro i hi
    rw [hrsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact (stack_writable pre hf.grow (by decide) (by decide)).readable
  · intro i hi
    rw [hrsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact stack_writable pre hf.grow (by decide) (by decide)
  · intro i hi
    rw [hdi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact (output_writable pre hf.grow).add _ (by decide)
  · intro i hi o n hn
    rw [hrsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact stack_code_apart pre (by decide) o n hn
  · intro i hi o n hn
    rw [hdi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact output_code_apart pre (by decide) o n hn
  · intro i hi j hj
    rw [hrsp, hsi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl | rfl
    all_goals rcases hj with rfl | rfl | rfl | rfl
    all_goals exact stack_input_apart pre (by decide) (by decide)
  · intro i hi j hj
    rw [hrsp, hdi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl | rfl
    all_goals rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact stack_output_apart pre (by decide) (by decide)

end P256.Proofs.Sec1.SquareRoot.Square.Wide
