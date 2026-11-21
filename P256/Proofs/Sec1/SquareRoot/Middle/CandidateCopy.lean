import P256.Proofs.Sec1.SquareRoot.SelectZero
import P256.Proofs.Sec1.SquareRoot.Representation
import P256.Proofs.Common.EffectCompose.Memory
set_option autoImplicit false

open P256.Proofs.Program
open P256.Proofs.HMAC.Key (stack_code_apart)
open P256.Proofs.Field
open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Sec1.SquareRoot.Middle

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CandidateCopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x1144a9
  readable : ∀ i ∈ ([336,344,352,360] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([8,16,24,32] : List (BitVec 64)),
    MemWritable s ((Operand.reg 4 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([8,16,24,32] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 4 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def candidateCopyBytes : List UInt8 :=
  [0x48,0x8b,0x84,0x24,0x68,1,0,0,0x48,0x89,0x44,0x24,0x20,
    0x48,0x8b,0x84,0x24,0x60,1,0,0,0x48,0x89,0x44,0x24,0x18,
    0x48,0x8b,0x84,0x24,0x50,1,0,0,0x48,0x8b,0x8c,0x24,0x58,1,0,0,
    0x48,0x89,0x4c,0x24,0x10,0x48,0x89,0x44,0x24,8]

def candidateCopyEffect (s : RamState) : Effect :=
  { rip := 0x1144dd
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 336) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 344) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 336) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 344) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 352) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 360) : Operand 64).read s⟩] }

theorem candidate_copy_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1144a9 candidateCopyBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x144a9 candidateCopyBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem candidate_copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CandidateCopyPre (codeRange 0x1144a9 candidateCopyBytes)
      (Effect.post candidateCopyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1144a9 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 360)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 360 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x144b1 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1144b1 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1144a9 candidateCopyBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0x144b1 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0x144a9 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144b6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1144b6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 352)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1144a9 candidateCopyBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 352 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144be (by decide))
  advance_then (mov_m64_r64_effect_step 0x1144be 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1144a9 candidateCopyBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x144be 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x144a9 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144c3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1144c3 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1144a9 candidateCopyBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 336 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144cb (by decide))
  advance_then (mov_r64_m64_effect_step 0x1144cb 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 344)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1144a9 candidateCopyBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 344 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144d3 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1144d3 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1144a9 candidateCopyBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x144d3 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x144a9 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144d8 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1144d8 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1144a9 candidateCopyBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x144d8 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x144a9 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x144dd (by decide))
  advance_finish [candidateCopyEffect]

theorem candidateCopyPre_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x1144a9) : CandidateCopyPre t := by
  have addr (i : BitVec 64) : (Operand.reg 4 : Operand 64).read t + i = stackPtr s - (584-i) := by
    change stackPtr t + i = _
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i hi
    rw [addr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) state.allocated
  · intro i hi
    rw [addr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact writable_of_grow (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) state.allocated
  · intro i hi offset len hcode
    rw [addr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact stack_code_apart pre (by decide) (by decide) hcode

theorem candidateCopyEffect_montgomery {s t : RamState} {x : Nat}
    (pre : CandidateCopyPre s) (effect : (candidateCopyEffect s).Holds s t)
    (input : MontgomeryAt s (stackPtr s + 336) x) :
    MontgomeryAt t (stackPtr s + 8) x := by
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_, _, h0, h8, h16, h24⟩
  apply montgomeryAt_of_memLoad_limbs input.1
  · intro i hi
    apply effect.agrees.grow
    have cases : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
    have writable : MemWritable s ((stackPtr s + 8) + BitVec.ofNat 64 (8*(i/8))) 8 := by
      change MemWritable s (((Operand.reg 4 : Operand 64).read s + 8) + BitVec.ofNat 64 (8*(i/8))) 8
      rcases cases with h | h | h | h
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 8 (by simp)
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 16 (by simp)
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 24 (by simp)
      · simpa (config := {decide := true}) only [x86_compose,h,BitVec.add_assoc] using pre.writable 32 (by simp)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8)+i%8=i by omega] using
      writable.mem (i%8) (by omega)
  · intro j hj
    rw [← input.memLoad_limb j hj]
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    change memLoad t.external (((Operand.reg 4 : Operand 64).read s + 8) + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (((Operand.reg 4 : Operand 64).read s + 336) + BitVec.ofNat 64 (8*j)) 64
    rcases cases with rfl | rfl | rfl | rfl
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h0
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h8
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h16
    · simpa (config := {decide := true}) only [x86_compose, BitVec.add_assoc, Write.AllHold] using h24

end P256.Proofs.Sec1.SquareRoot.Middle
