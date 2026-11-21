import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Sec1.Decompress.Select.Zero
import P256.Proofs.Sec1.Decompress.Cubic.Support
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct
import P256.Proofs.Projective.Multiply.Machine.Lookup.Negate.Correct

set_option autoImplicit false
open P256.Proofs.Program P256.Proofs.Program.FieldCall P256.Proofs.Field
open P256.Proofs.Sec1.Decompress.Cubic (input_stack_address montgomeryAt_of_copy)

namespace P256.Proofs.Sec1.Decompress.Select

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem zero_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x10fede) : ZeroPre t := by
  refine ⟨rip, ?_, ?_⟩
  · intro off ho
    have bound : off.toNat + 8 ≤ 408 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> decide
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using ScalarFrame.stack_writable pre state (by decide) bound (by decide)
  · intro off ho codeOffset len hcode
    have bound : off.toNat + 8 ≤ 408 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> decide
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using ScalarFrame.stack_code pre state (by decide) bound hcode

def zeroComponents (s : RamState) : List Component := [.rip, .mem (stackPtr s - 216) 32]

theorem zero_frame [Bindings] {s t u : RamState} (state : Frame s t)
    (effect : (zeroEffect t).Holds t u) : AgreesExcept (zeroComponents s) t u := by
  apply Cubic.agrees_of_footprint effect.agrees
  · intro c hc hm
    simp only [zeroEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [Component.isMem] at hm
    all_goals simp [zeroComponents]
  · intro c hc a ha
    simp only [zeroEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (stackPtr s - 216) 32, by simp [zeroComponents], ?_⟩
      rw [state.rsp]
    · refine ⟨24+i, by omega, ?_⟩
      simp (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    · refine ⟨16+i, by omega, ?_⟩
      simp (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    · refine ⟨8+i, by omega, ?_⟩
      simp (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    · refine ⟨i, by omega, ?_⟩
      simp (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem zero_result [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x10fede) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10ff0e ∧
      MontgomeryAt u (stackPtr s - 216) 0 ∧ AgreesExcept (zeroComponents s) t u := by
  obtain ⟨fuel, u, advance, ready, _, effect⟩ := zero boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfede zeroBytes
      (by decide +kernel) zeroBytes_extracted) (zero_pre pre state rip)
  have frame := zero_frame state effect
  have writes : WritesWithin (zeroComponents s) #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro c hc a ha
    simp only [zeroComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.elim
    · exact ⟨ScalarFrame.workRegion s 2592, by simp, ScalarFrame.work_contains pre (by decide) (by decide) ha⟩
  have finalState := state.after_effect pre (by decide) ready frame writes (by simp [zeroComponents])
  refine ⟨fuel, u, advance, finalState, effect.rip, ?_, frame⟩
  have out := ScalarFrame.stack_readable pre finalState (by decide) (offset := 192) (len := 32) (by decide)
  rw [input_stack_address finalState.rsp (by decide)] at out
  change MemReadable u (stackPtr s - 216) 32 at out
  apply Field.montgomeryAt_of_memLoad_limbs (by decide +kernel) out.mem
  have values := effect.writes
  change _ ∧ _ ∧ _ ∧ _ at values
  rcases values with ⟨h24, h16, h8, h0⟩
  change memLoad u.external (stackPtr t + 216) 64 = 0 at h24
  change memLoad u.external (stackPtr t + 208) 64 = 0 at h16
  change memLoad u.external (stackPtr t + 200) 64 = 0 at h8
  change memLoad u.external (stackPtr t + 192) 64 = 0 at h0
  have a24 : stackPtr t + 216 = (stackPtr s - 216) + 24 := by
    rw [state.rsp, show (408 : BitVec 64) = 216 + 192 by decide +kernel,
      ← BitVec.sub_sub, show (216 : BitVec 64) = 192 + 24 by decide +kernel,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have a16 : stackPtr t + 208 = (stackPtr s - 216) + 16 := by
    rw [state.rsp, show (408 : BitVec 64) = 216 + 192 by decide +kernel,
      ← BitVec.sub_sub, show (208 : BitVec 64) = 192 + 16 by decide +kernel,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have a8 : stackPtr t + 200 = (stackPtr s - 216) + 8 := by
    rw [state.rsp, show (408 : BitVec 64) = 216 + 192 by decide +kernel,
      ← BitVec.sub_sub, show (200 : BitVec 64) = 192 + 8 by decide +kernel,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have a0 : stackPtr t + 192 = stackPtr s - 216 := input_stack_address state.rsp (by decide)
  rw [a24] at h24
  rw [a16] at h16
  rw [a8] at h8
  rw [a0] at h0
  intro j hj
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.zero_mul, Nat.zero_mod, Nat.zero_div] using h0
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Nat.zero_mul, Nat.zero_mod, Nat.zero_div] using h8
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Nat.zero_mul, Nat.zero_mod, Nat.zero_div] using h16
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Nat.zero_mul, Nat.zero_mod, Nat.zero_div] using h24

end P256.Proofs.Sec1.Decompress.Select
