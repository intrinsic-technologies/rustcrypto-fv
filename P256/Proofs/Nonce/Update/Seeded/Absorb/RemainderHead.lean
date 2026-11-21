import P256.Proofs.Nonce.Update.Absorb.Prefix.TagTail
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.RemainderHead

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions

attribute [local x86_compose] movM8Imm8Effect
attribute [local x86_local] Prepare.CompressionSetup.byteStore_local

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a7d8
  remaining : (Operand.reg 15 : Operand 64).read s = 1
  writable : MemWritable s (rspOf s + 383) 1
  codeApart : ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + 383) 1 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 := [0xc6, 0x84, 0x24, 0x7f, 0x1, 0x0, 0x0, 0x0, 0x48, 0x89, 0xde, 0x4c, 0x89, 0xfa, 0x48, 0xc1, 0xea, 0x6, 0x74, 0x16]

def effect (s : RamState) : Effect :=
  { rip := 0x10a7ea
    writes := [⟨(.mem (rspOf s + 383) : Operand 8),0⟩,
      ⟨(.reg 6 : Operand 64),(Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64),0⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 (1 : BitVec 64)) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a7d8 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa7d8 bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem head [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a7d8 bytes) (Effect.post effect) := by
  advance_begin (mov_m8_imm8_effect_step 0x10a7d8 (.sib 4 none 0 (.d32 383)) (by decide) rfl rfl 0)
  case pre => intro s h; exact ⟨h.rip,h.writable,h.codeApart 0xa7d8 8 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    simp only [movM8Imm8Effect,storeEffect_components,List.mem_cons,List.not_mem_nil,or_false]
    intro c hc a len eq
    rcases hc with rfl | rfl
    · cases eq; x86_norm; exact h.codeApart 0xa7d8 20 (by decide)
    · cases eq
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa7e0 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10a7e0 6 3) from mov_r64_r64_effect_step 0x10a7e0 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a7d8 bytes 8 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa7e3 (by decide))⟩
  advance_then (show StepEffect _ _ (movR64R64Effect 0x10a7e3 2 15) from mov_r64_r64_effect_step 0x10a7e3 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a7d8 bytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa7e6 (by decide))⟩
  advance_then (show StepEffect _ _ (shrR64Effect 0x10a7e6 4 2 6) from shr_r64_imm8_effect_step 0x10a7e6 0x48 0xea 6 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a7d8 bytes 14 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa7ea (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  have rem := hP.remaining
  simp only [BitVec.ofNat_eq_ofNat] at rem
  apply hH.weaken
  · x86_norm [effect,rem]
  · x86_norm [effect,rem]
  · intro i; cases i <;> x86_norm [effect,rem]
  · x86_norm [effect,rem]

def branchEffect (s : RamState) : Effect := { effect s with rip := 0x10a802 }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a7d8 bytes) (Effect.post branchEffect) := by
  intro s ready codeIn pre
  obtain ⟨n, t, advances, readyT, codeT, h⟩ := head boundary outside s ready codeIn pre
  have zero : (StatusFlags.ofRFLAGS t.RFLAGS).ZF = true := by
    have hz := h.flags.2.2.2.1
    exact hz
  obtain ⟨u, step, readyU, branch⟩ := jcc_rel8_effect_step 0x10a7ea 4 0x16 t readyT
    (codeT.mono (codeRange_slice_subset 0x10a7d8 bytes 18 2))
    ⟨h.rip, by intro; decide⟩
  have ip : u.RIP = 0x10a802 := by
    rw [branch.rip]
    change (if (StatusFlags.ofRFLAGS t.RFLAGS).ZF then 0x10a802 else 0x10a7ec) = _
    simp only [zero, ite_true]
  have runU : Advances boundary 1 t u := Advances.of_step step (.inl (by
    rw [ip]; exact boundary_ne_program outside (inProgram_of_textOffset 0xa802 (by decide))))
  have ag : AgreesExcept [.rip] t u := branch.agrees
  have ext : u.external = t.external := ag.external (by simp [Component.Covers])
  refine ⟨n+1, u, advances.trans runU, readyU, codeT.of_external_eq ext, ip, ?_, ?_, ?_⟩
  · have hw := h.writes
    change _ ∧ _ ∧ _ at hw ⊢
    refine ⟨?_, ?_, ?_⟩
    · change memLoad u.external _ 8 = _
      rw [ext]
      exact hw.1
    · exact (ag.read (r := 6) (n := 64) (by simp)).trans hw.2.1
    · exact (ag.read (r := 2) (n := 64) (by simp)).trans hw.2.2
  · change (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 (1 : BitVec 64)).Allows (StatusFlags.ofRFLAGS u.RFLAGS)
    rw [ag.rflags (by simp) (by simp)]
    exact h.flags
  · exact (h.agrees.trans ag).mono (by simp [branchEffect, effect, Effect.components])

end P256.Proofs.Nonce.Update.Seeded.Absorb.RemainderHead
