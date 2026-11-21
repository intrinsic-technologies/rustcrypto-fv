import P256.Proofs.Field.Inverse.Tail.Support

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Inverse.SecondCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure CandidateCopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x11419b
  readable : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([40,48,56,64] : List (BitVec 64)),
    MemWritable s ((Operand.reg 4 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([40,48,56,64] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 4 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def candidateCopyBytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x18,0x48,0x89,0x44,0x24,0x40,0x48,0x8b,0x44,0x24,0x10,0x48,0x89,0x44,0x24,0x38,0x48,0x8b,0x4,0x24,0x48,0x8b,0x4c,0x24,0x8,0x48,0x89,0x4c,0x24,0x30,0x48,0x89,0x44,0x24,0x28]

def candidateCopyEffect (s : RamState) : Effect :=
  { rip := 0x1141c2
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 0) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 40) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 0) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 48) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 56) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 64) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64).read s⟩] }

theorem candidate_copy_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x11419b candidateCopyBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1419b candidateCopyBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem candidate_copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CandidateCopyPre (codeRange 0x11419b candidateCopyBytes)
      (Effect.post candidateCopyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11419b 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 24 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x141a0 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1141a0 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11419b candidateCopyBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 (by simp)
    · x86_norm
      exact hP.codeApart 64 (by simp) 0x141a0 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 64 (by simp) 0x1419b 39 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141a5 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1141a5 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11419b candidateCopyBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141aa (by decide))
  advance_then (mov_m64_r64_effect_step 0x1141aa 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11419b candidateCopyBytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      exact hP.codeApart 56 (by simp) 0x141aa 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp) 0x1419b 39 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141af (by decide))
  advance_then (mov_r64_m64_effect_step 0x1141af 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11419b candidateCopyBytes 20 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141b3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1141b3 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11419b candidateCopyBytes 24 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141b8 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1141b8 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11419b candidateCopyBytes 29 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 (by simp) 0x141b8 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp) 0x1419b 39 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141bd (by decide))
  advance_then (mov_m64_r64_effect_step 0x1141bd 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11419b candidateCopyBytes 34 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x141bd 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x1419b 39 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141c2 (by decide))
  advance_finish [candidateCopyEffect]

theorem candidateCopyPre_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11419b) : CandidateCopyPre t := by
  have addr (i : BitVec 64) : (Operand.reg 4 : Operand 64).read t + i = stackPtr s - (168-i) := by
    change stackPtr t + i = _
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i hi
    rw [addr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack (by decide) (by decide)) state.allocated
  · intro i hi
    rw [addr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact P256.Proofs.Program.writable_of_grow (P256.Proofs.Program.stack_sub_writable8 pre.stack (fun a ha ht ↦ pre.avoids _ (by simp) a ha (.inr ht)) (by decide) (by decide)) state.allocated
  · intro i hi offset len hcode
    rw [addr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact stack_code_apart pre (by decide) (by decide) hcode

theorem candidateCopyEffect_value {s t : RamState} {x : Nat}
    (pre : CandidateCopyPre s) (effect : (candidateCopyEffect s).Holds s t)
    (input : Nat256At s (stackPtr s + 0) x) :
    Nat256At t (stackPtr s + 40) x := by
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_, _, h0, h8, h16, h24⟩
  apply nat256At_copy_limbs input
  · intro i hi
    apply effect.agrees.grow
    have cases : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
    have writable : MemWritable s ((stackPtr s + 40) + BitVec.ofNat 64 (8*(i/8))) 8 := by
      change MemWritable s (((Operand.reg 4 : Operand 64).read s + 40) + BitVec.ofNat 64 (8*(i/8))) 8
      rcases cases with h | h | h | h
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 40 (by simp)
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 48 (by simp)
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 56 (by simp)
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 64 (by simp)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8)+i%8=i by omega] using
      writable.mem (i%8) (by omega)
  · intro j hj
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    change memLoad t.external (((Operand.reg 4 : Operand 64).read s + 40) + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (((Operand.reg 4 : Operand 64).read s + 0) + BitVec.ofNat 64 (8*j)) 64
    rcases cases with rfl | rfl | rfl | rfl
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h0
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h8
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h16
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h24

end P256.Proofs.Field.Inverse.SecondCopy
