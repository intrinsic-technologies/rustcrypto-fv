import P256.Proofs.Sec1.Affine.State
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.NegByte.Legacy
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Flags

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Instructions P256.Proofs.Common.Instructions.NegByte

structure MaskPre (s : RamState) : Prop where
  rip : s.RIP = 0x11027b
  writable : MemWritable s (stackPtr s + 12) 1
  codeApart : ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + 12) 1
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def maskBytes : List UInt8 := [0x89,0xe8,0xf6,0xd8,0x88,0x44,0x24,0x0c]

def maskEffect (s : RamState) : Effect :=
  { rip := 0x110283
    writes := [⟨(.mem (stackPtr s + 12) : Operand 8), -(s.regValue .rbp).setWidth 8⟩,
      ⟨(.reg 0 : Operand 64), mergeGPR 8 (-(s.regValue .rbp).setWidth 8)
        (((s.regValue .rbp).setWidth 32).setWidth 64)⟩]
    flags := some (.ofStatusFlags (subSpec 0 ((s.regValue .rbp).setWidth 8)).2) }

attribute [local x86_compose] negR8LegacyEffect

@[x86_local] theorem neg_legacy_local (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (negR8LegacyEffect p dst) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [negR8LegacyEffect, negR8Effect, h.read_reg]
  · intro s
    simp [negR8LegacyEffect, negR8Effect, Write.Full, Operand.Full]

set_option maxHeartbeats 800000 in
theorem mask_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary MaskPre (codeRange 0x11027b maskBytes) maskEffect := by
  unfold maskBytes
  slice_run_begin (mov_r32_r32_effect_step 0x11027b 0xe8 rfl)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1027d (by decide))
  slice_run_then (show StepEffect _ _ (negR8LegacyEffect 0x11027d 0) from
    neg_r8_legacy_effect_step 0x11027d 0xd8 rfl rfl (by decide))
  case sub => exact codeRange_mem_of_drop (p := 0x11027b) 2 (by decide +kernel)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x1027f (by decide))
  slice_run_then (mov_m8_r8_legacy_effect_step 0x11027f 0 (by decide)
    (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl)
  case sub => exact codeRange_mem_of_drop (p := 0x11027b) 4 (by decide +kernel)
  case loc => effect_local [storeEffect, storeAddrAt]
  case mid =>
    intro s t hp he ho
    refine ⟨StorePre.of_holds he (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_⟩
    · x86_norm
      exact hp.writable
    · x86_norm
      exact hp.codeApart 0x1027f 4 (by decide)
    · apply Effect.Local.avoids (by effect_local [storeEffect, storeAddrAt]) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 0x1027b 8 (by decide)
  case boundary => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10283 (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [maskEffect]
  · x86_norm [maskEffect]
    simp only [Operand.read, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    exact ⟨.inr rfl, .inl rfl⟩
  · intro f; cases f <;> x86_norm [maskEffect]
    all_goals simp only [Operand.read, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    all_goals rfl
  · x86_norm [maskEffect]

end P256.Proofs.Sec1.Affine.Compact.Flags
