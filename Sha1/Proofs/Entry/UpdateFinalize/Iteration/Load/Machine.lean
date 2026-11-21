import Sha1.Proofs.Compress.Machine.Segment
import Sha1.Proofs.Streaming.Loop

namespace Sha1.Proofs.Entry.UpdateFinalize

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine Sha1.Proofs.Streaming.UpdateFinalize

def tableAddress (s : RamState) (offset : Nat) : BitVec 64 :=
  stackWord s offset + ((Operand.reg 15 : Operand 64).read s <<< 3)

structure SliceLoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x101cdd
  pointers : MemReadable s (stackPtr s + 0xc8) 8
  lengths : MemReadable s (stackPtr s + 0xd0) 8
  pointerEntry : MemReadable s (tableAddress s 0xc8) 8
  lengthEntry : MemReadable s (tableAddress s 0xd0) 8

def sliceLoadEffect (s : RamState) : Effect where
  rip := 0x101cf5
  writes := [⟨(.reg 14 : Operand 64), (Operand.mem (tableAddress s 0xc8) : Operand 64).read s⟩,
    ⟨(.reg 0 : Operand 64), stackWord s 0xd0⟩,
    ⟨(.reg 3 : Operand 64), (Operand.mem (tableAddress s 0xd0) : Operand 64).read s⟩]

theorem slice_load_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary SliceLoadPre
      (codeRange 0x101cdd [0x48,0x8b,0x84,0x24,0xc8,0,0,0,0x4e,0x8b,0x34,0xf8,
        0x48,0x8b,0x84,0x24,0xd0,0,0,0,0x4a,0x8b,0x1c,0xf8])
      sliceLoadEffect := by
  have hBoundary (i : Nat) (hi : i < 25) :
      (0x101cdd : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip := by
    intro he
    exact hout (he ▸ program_text_range 0x1cdd 25 (by decide +kernel) i hi)
  sha1_run_begin_manual (mov_r64_m64_effect_step 0x101cdd 0x48 (by unfold RexWPrefix; decide) 0
    (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide))
  case pre => intro s h; exact ⟨h.rip, h.pointers⟩
  case av => intro s h; x86_avoid
  sha1_run_then_manual (mov_r64_m64_effect_step 0x101ce5 0x4e (by unfold RexWPrefix; decide) 6
    (.sib 0 (some 15) 3 .none) (by decide) (by decide) (by decide))
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by rfl) (by x86_addr_obs) ?_, ?_⟩
    · sha1_norm
      simp only [BitVec.add_zero]
      exact h.pointerEntry
    · x86_avoid
  sha1_run_then_manual (mov_r64_m64_effect_step 0x101ce9 0x48 (by unfold RexWPrefix; decide) 0
    (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide))
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by rfl) (by x86_addr_obs) ?_, ?_⟩
    · sha1_norm
      exact h.lengths
    · x86_avoid
  sha1_run_then_manual (mov_r64_m64_effect_step 0x101cf1 0x4a (by unfold RexWPrefix; decide) 3
    (.sib 0 (some 15) 3 .none) (by decide) (by decide) (by decide))
  case mid =>
    intro s t h hE hO
    refine ⟨LoadPre.of_holds hE (hO true) (by rfl) (by x86_addr_obs) ?_, ?_⟩
    · sha1_norm
      simp only [BitVec.add_zero]
      exact h.lengthEntry
    · x86_avoid
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · rfl
  · sha1_norm [sliceLoadEffect, tableAddress, stackWord, stackPtr_eq_read, BitVec.add_zero]
  · intro i; cases i <;> sha1_norm [sliceLoadEffect]
  · sha1_norm [sliceLoadEffect]

end Sha1.Proofs.Entry.UpdateFinalize
