import P256.Proofs.Field.Inverse.Tail.Support

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Inverse.FirstCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure CandidateCopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x11411e
  readable : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([112,120,128,136] : List (BitVec 64)),
    MemWritable s ((Operand.reg 4 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([112,120,128,136] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 4 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def candidateCopyBytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x18,0x48,0x89,0x84,0x24,0x88,0x0,0x0,0x0,0x48,0x8b,0x44,0x24,0x10,0x48,0x89,0x84,0x24,0x80,0x0,0x0,0x0,0x48,0x8b,0x4,0x24,0x48,0x8b,0x4c,0x24,0x8,0x48,0x89,0x4c,0x24,0x78,0x48,0x89,0x44,0x24,0x70]

def candidateCopyEffect (s : RamState) : Effect :=
  { rip := 0x11414b
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 0) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 112) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 0) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 120) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 128) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 136) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64).read s⟩] }

theorem candidate_copy_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x11411e candidateCopyBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1411e candidateCopyBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem candidate_copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CandidateCopyPre (codeRange 0x11411e candidateCopyBytes)
      (Effect.post candidateCopyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11411e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 24 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x14123 (by decide))
  advance_then (mov_m64_r64_effect_step 0x114123 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11411e candidateCopyBytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      exact hP.codeApart 136 (by simp) 0x14123 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 136 (by simp) 0x1411e 45 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1412b (by decide))
  advance_then (mov_r64_m64_effect_step 0x11412b 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11411e candidateCopyBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14130 (by decide))
  advance_then (mov_m64_r64_effect_step 0x114130 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11411e candidateCopyBytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by simp)
    · x86_norm
      exact hP.codeApart 128 (by simp) 0x14130 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 (by simp) 0x1411e 45 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14138 (by decide))
  advance_then (mov_r64_m64_effect_step 0x114138 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11411e candidateCopyBytes 26 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1413c (by decide))
  advance_then (mov_r64_m64_effect_step 0x11413c 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11411e candidateCopyBytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14141 (by decide))
  advance_then (mov_m64_r64_effect_step 0x114141 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11411e candidateCopyBytes 35 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 120 (by simp)
    · x86_norm
      exact hP.codeApart 120 (by simp) 0x14141 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 120 (by simp) 0x1411e 45 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14146 (by decide))
  advance_then (mov_m64_r64_effect_step 0x114146 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11411e candidateCopyBytes 40 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 112 (by simp)
    · x86_norm
      exact hP.codeApart 112 (by simp) 0x14146 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 112 (by simp) 0x1411e 45 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1414b (by decide))
  advance_finish [candidateCopyEffect]

theorem candidateCopyPre_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11411e) : CandidateCopyPre t := by
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
    Nat256At t (stackPtr s + 112) x := by
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_, _, h0, h8, h16, h24⟩
  apply nat256At_copy_limbs input
  · intro i hi
    apply effect.agrees.grow
    have cases : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
    have writable : MemWritable s ((stackPtr s + 112) + BitVec.ofNat 64 (8*(i/8))) 8 := by
      change MemWritable s (((Operand.reg 4 : Operand 64).read s + 112) + BitVec.ofNat 64 (8*(i/8))) 8
      rcases cases with h | h | h | h
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 112 (by simp)
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 120 (by simp)
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 128 (by simp)
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 136 (by simp)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8)+i%8=i by omega] using
      writable.mem (i%8) (by omega)
  · intro j hj
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    change memLoad t.external (((Operand.reg 4 : Operand 64).read s + 112) + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (((Operand.reg 4 : Operand 64).read s + 0) + BitVec.ofNat 64 (8*j)) 64
    rcases cases with rfl | rfl | rfl | rfl
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h0
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h8
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h16
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h24

end P256.Proofs.Field.Inverse.FirstCopy
