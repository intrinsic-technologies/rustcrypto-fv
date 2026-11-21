import Md5.Proofs.Buffered.FinalizeReset.Prepare.Model
import Md5.Proofs.Buffered.FinalizeReset.Normalize
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def copyBytes : List UInt8 :=
  [0x48, 0x8d, 0x4c, 0x24, 0x48, 0x48, 0x8b, 0x01, 0x48, 0x8b, 0x49, 0x08,
    0x48, 0x89, 0x8c, 0x24, 0xf0, 0, 0, 0, 0x48, 0x89, 0x84, 0x24, 0xe8, 0, 0, 0]

structure CopyPre (s : RamState) (variant : Variant := .saved) : Prop extends Storage s variant where
  rip : s.RIP = (variant.address 0x1007aa)

def copyBodyEffect (s : RamState) (variant : Variant := .saved) : Effect :=
  { rip := (variant.address 0x1007c6)
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 0x48) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 0x50) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 0xf0) : Operand 64),
        (.mem (stackPtr s + 0x50) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 0xe8) : Operand 64),
        (.mem (stackPtr s + 0x48) : Operand 64).read s⟩] }

theorem copy_body_execution {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ CopyPre s variant) (codeRange (variant.address 0x1007aa) copyBytes) (fun s ↦ copyBodyEffect s variant) := by
  cases variant with
  | saved =>
    unfold copyBytes
    md5_run_begin (lea_r64_effect_step 0x1007aa 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide))
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7af (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step 0x1007af 0x48 (by unfold RexWPrefix; decide)
      0 (.base 1 .none) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1007aa) 5 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact h.toStorage.readable 0x48 8 (by decide)
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7b2 (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step 0x1007b2 0x48 (by unfold RexWPrefix; decide)
      1 (.base 1 (.d8 8)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1007aa) 8 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact h.toStorage.readable 0x50 8 (by decide)
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7b6 (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step 0x1007b6 0x48
      (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xf0))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1007aa) 12 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0xf0 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage _ _ 0x7b6 _ (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components 0x1007b6 1 (.sib 4 none 0 (.d32 0xf0)) t)
        change RangeApart (stackPtr t + 0xf0) 8 0x1007aa 28
        rw [hsp]
        exact Export.stackTextApart h.toStorage _ _ 0x7aa _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7be (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step 0x1007be 0x48
      (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xe8))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1007aa) 20 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0xe8 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage _ _ 0x7be _ (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components 0x1007be 0 (.sib 4 none 0 (.d32 0xe8)) t)
        change RangeApart (stackPtr t + 0xe8) 8 0x1007aa 28
        rw [hsp]
        exact Export.stackTextApart h.toStorage _ _ 0x7aa _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7c6 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, copyBodyEffect]
    · x86_norm [Variant.address, copyBodyEffect, stackPtr]
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
    · intro i; cases i <;> x86_norm [Variant.address, copyBodyEffect]
    · x86_norm [Variant.address, copyBodyEffect, stackPtr]
      exact ⟨Or.inl rfl, Or.inr rfl⟩
  | direct =>
    unfold copyBytes
    md5_run_begin (lea_r64_effect_step 0x100e5a 0x48 (by unfold RexWPrefix; decide)
      1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide))
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe5f (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step 0x100e5f 0x48 (by unfold RexWPrefix; decide)
      0 (.base 1 .none) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x100e5a) 5 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact h.toStorage.readable 0x48 8 (by decide)
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe62 (by decide +kernel)
    md5_run_then (mov_r64_m64_effect_step 0x100e62 0x48 (by unfold RexWPrefix; decide)
      1 (.base 1 (.d8 8)) (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x100e5a) 8 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      refine ⟨LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
      · x86_norm
        exact h.toStorage.readable 0x50 8 (by decide)
      · x86_avoid
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe66 (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step 0x100e66 0x48
      (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xf0))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x100e5a) 12 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0xf0 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage _ _ 0xe66 _ (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components 0x100e66 1 (.sib 4 none 0 (.d32 0xf0)) t)
        change RangeApart (stackPtr t + 0xf0) 8 0x100e5a 28
        rw [hsp]
        exact Export.stackTextApart h.toStorage _ _ 0xe5a _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe6e (by decide +kernel)
    md5_run_then (Stores.mov_m64_r64_effect_step 0x100e6e 0x48
      (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xe8))
      (by decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x100e5a) 20 (by decide +kernel)
    case mid =>
      intro s t h hE hO
      have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
      refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
      · x86_norm
        exact Export.stackWritable h.toStorage 0xe8 8 (by decide)
      · x86_norm
        exact Export.stackTextApart h.toStorage _ _ 0xe6e _ (by decide) (by decide +kernel)
      · apply Effect.avoids_of_components_mem_rip
          (movM64R64Effect_components 0x100e6e 0 (.sib 4 none 0 (.d32 0xe8)) t)
        change RangeApart (stackPtr t + 0xe8) 8 0x100e5a 28
        rw [hsp]
        exact Export.stackTextApart h.toStorage _ _ 0xe5a _ (by decide) (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe76 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, copyBodyEffect]
    · x86_norm [Variant.address, copyBodyEffect, stackPtr]
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
    · intro i; cases i <;> x86_norm [Variant.address, copyBodyEffect]
    · x86_norm [Variant.address, copyBodyEffect, stackPtr]
      exact ⟨Or.inl rfl, Or.inr rfl⟩

end Md5.Proofs.Buffered.FinalizeReset.Prepare
