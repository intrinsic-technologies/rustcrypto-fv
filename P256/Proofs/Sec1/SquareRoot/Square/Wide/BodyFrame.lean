import P256.Proofs.Sec1.SquareRoot.Square.Wide.BodyInterface
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Frame
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Epilogue

set_option autoImplicit false

open P256.Proofs.Program (CalleePre memoryRegion_contains_add stack_region_end)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Common.Field.SquareRoot

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def bodyFrame (s : RamState) : List Component :=
  (List.range 16).map (fun i => Component.reg (BitVec.ofNat 5 i)) ++
    [.flags, .rip, .mem (stackPtr s) 40, .mem (s.regValue .rdi) 64]

theorem covers_add {base a : BitVec 64} {offset len count : Nat}
    (h : offset+len ≤ count)
    (ha : (Component.mem (base+BitVec.ofNat 64 offset) len).Covers a) :
    (Component.mem base count).Covers a := by
  obtain ⟨i, hi, rfl⟩ := ha
  exact ⟨offset+i, by omega, by simp only [BitVec.ofNat_add, BitVec.add_assoc]⟩

theorem bodyEffect_components (s : RamState) : (bodyEffect s).components =
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15,
   .mem ((Operand.reg 4 : Operand 64).read s+8) 8, .mem ((Operand.reg 4 : Operand 64).read s+16) 8, .mem ((Operand.reg 4 : Operand 64).read s+24) 8, .mem ((Operand.reg 4 : Operand 64).read s+32) 8,
   .mem ((Operand.reg 7 : Operand 64).read s+0) 8, .mem ((Operand.reg 7 : Operand 64).read s+8) 8, .mem ((Operand.reg 7 : Operand 64).read s+16) 8, .mem ((Operand.reg 7 : Operand 64).read s+24) 8, .mem ((Operand.reg 7 : Operand 64).read s+32) 8, .mem ((Operand.reg 7 : Operand 64).read s+40) 8, .mem ((Operand.reg 7 : Operand 64).read s+48) 8, .mem ((Operand.reg 7 : Operand 64).read s+56) 8, .flags, .rip] := by
  simp [bodyEffect, Effect.components]

theorem bodyEffect_frame {s t : RamState} (h : (bodyEffect s).Holds s t) :
    AgreesExcept (bodyFrame s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [bodyEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | solve | cases hm | simp [bodyFrame, List.range_succ]
  · intro a c hc ha
    simp only [bodyEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨.mem (stackPtr s) 40, by simp [bodyFrame], covers_add (offset := 8) (by decide) ha⟩
    · exact ⟨.mem (stackPtr s) 40, by simp [bodyFrame], covers_add (offset := 16) (by decide) ha⟩
    · exact ⟨.mem (stackPtr s) 40, by simp [bodyFrame], covers_add (offset := 24) (by decide) ha⟩
    · exact ⟨.mem (stackPtr s) 40, by simp [bodyFrame], covers_add (offset := 32) (by decide) ha⟩
    · exact ⟨.mem (s.regValue .rdi) 64, by simp [bodyFrame], covers_add (offset := 0) (by decide) ha⟩
    · exact ⟨.mem (s.regValue .rdi) 64, by simp [bodyFrame], covers_add (offset := 8) (by decide) ha⟩
    · exact ⟨.mem (s.regValue .rdi) 64, by simp [bodyFrame], covers_add (offset := 16) (by decide) ha⟩
    · exact ⟨.mem (s.regValue .rdi) 64, by simp [bodyFrame], covers_add (offset := 24) (by decide) ha⟩
    · exact ⟨.mem (s.regValue .rdi) 64, by simp [bodyFrame], covers_add (offset := 32) (by decide) ha⟩
    · exact ⟨.mem (s.regValue .rdi) 64, by simp [bodyFrame], covers_add (offset := 40) (by decide) ha⟩
    · exact ⟨.mem (s.regValue .rdi) 64, by simp [bodyFrame], covers_add (offset := 48) (by decide) ha⟩
    · exact ⟨.mem (s.regValue .rdi) 64, by simp [bodyFrame], covers_add (offset := 56) (by decide) ha⟩

theorem body_frame {s t u : RamState}
    (rsp : stackPtr t = stackPtr s-88) (rdi : t.regValue .rdi = s.regValue .rdi)
    (h : AgreesExcept (bodyFrame t) t u) : AgreesExcept (frame s) t u := by
  apply h.widen
  · intro c hc hm
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> simp_all [frame, Component.isMem]
  · intro a c hc ha
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      exact ha.elim
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact ha.elim
      · exact ha.elim
      · rw [rsp] at ha
        obtain ⟨i, hi, he⟩ := ha
        exact ⟨.mem (stackPtr s-88) 88, by simp [frame], i, by omega, he⟩
      · rw [rdi] at ha
        exact ⟨.mem (s.regValue .rdi) 64, by simp [frame], ha⟩

theorem saved_word_inside [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (pre : CalleePre s boundary entry 32 64 88)
    {offset i : Nat} (ho : offset ≤ 48) (hi : i < 8) :
    (Stack.region s 88).Contains
      (stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat := by
  apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
  · rw [P256.Proofs.Program.stack_sub_toNat pre.stack (by omega)]
    change (stackPtr s).toNat-88 ≤ (stackPtr s).toNat-offset
    omega
  · rw [stack_region_end, P256.Proofs.Program.stack_sub_toNat pre.stack (by omega)]
    have := (P256.Proofs.Program.stack_bounds pre.stack).1
    omega

theorem saved_word_preserved [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (pre : CalleePre s boundary entry 32 64 88)
    (rsp : stackPtr t = stackPtr s-88) (rdi : t.regValue .rdi = s.regValue .rdi)
    (ag : AgreesExcept (bodyFrame t) t u) {offset : Nat} (ho : offset ≤ 48) :
    memLoad u.external (stackPtr s-BitVec.ofNat 64 offset) 64 =
      memLoad t.external (stackPtr s-BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  apply ag.memory
  intro c hc ha
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
    exact ha.elim
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ha.elim
    · exact ha.elim
    · rw [rsp] at ha
      obtain ⟨j, hj, he⟩ := ha
      have hb : stackPtr s-BitVec.ofNat 64 offset =
          stackPtr s-88+BitVec.ofNat 64 (88-offset) := by
        have h := scratch_address s (offset := 88-offset) (by omega)
        rw [Nat.sub_sub_self (by omega : offset ≤ 88)] at h
        exact h.symm
      have hap := RangeApart.offsets (stackPtr s-88) (a := 0) (len := 40)
        (b := 88-offset) (count := 8) (by decide) (by omega) (by omega)
      have hn := hap j hj i hi
      rw [BitVec.add_zero, ← hb] at hn
      exact hn he.symm
    · rw [rdi] at ha
      obtain ⟨j, hj, he⟩ := ha
      have hout := memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hj
      have hstack := saved_word_inside pre ho hi
      rw [he] at hstack
      exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hout hstack

theorem epilogue_frame {s t u : RamState} (ag : AgreesExcept epilogueComponents t u) :
    AgreesExcept (frame s) t u := by
  apply ag.mono
  intro c hc
  simp only [epilogueComponents, P256.Proofs.Field.Schoolbook.epilogueComponents,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [frame, List.range_succ]

end P256.Proofs.Sec1.SquareRoot.Square.Wide
