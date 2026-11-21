import Md5.Proofs.Buffered.FinalizeReset.Length.Register
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.FinalizeReset.Length

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def bytes : List UInt8 :=
  [0x41, 0xc1, 0xe7, 0x03, 0x4d, 0x09, 0xf7, 0x4c, 0x89, 0x7c, 0x24,
    0x40, 0x4c, 0x89, 0xbc, 0x24, 0x98, 0x00, 0x00, 0x00]

structure RunPre (s : RamState) (variant : Variant := .saved) : Prop extends Storage s variant where
  rip : s.RIP = (variant.address 0x1008a2)

def value (s : RamState) : BitVec 64 :=
  (((Operand.reg 15 : Operand 32).read s) <<< 3).setWidth 64 |||
    (Operand.reg 14 : Operand 64).read s

def effect (s : RamState) (variant : Variant := .saved) : Effect :=
  { rip := (variant.address 0x1008b6)
    writes := [⟨(.reg 15 : Operand 64), value s⟩,
      ⟨(.mem (stackPtr s + 0x40) : Operand 64), value s⟩,
      ⟨(.mem (stackPtr s + 0x98) : Operand 64), value s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

@[x86_compose] theorem address_add (variant : Variant) (p n : BitVec 64) :
    variant.address p + n = variant.address (p + n) := by
  simp only [Variant.address, BitVec.add_assoc]
  exact congrArg (fun x : BitVec 64 ↦ p + x) (BitVec.add_comm _ n)

theorem execution {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ RunPre s variant) (codeRange (variant.address 0x1008a2) bytes) (fun s ↦ effect s variant) := by
  unfold bytes
  md5_run_begin (shl_r32_imm8_rex_effect_step (variant.address 0x1008a2) 0x41 0xe7 3
    (by unfold RexNoWPrefix; decide) (by cases variant <;> decide) (by cases variant <;> decide))
  case boundary => intro _ _; have haddr := text_address_ne_return hOutside (0x8a6 + (if variant = .saved then 0 else 0x6b0)) (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  md5_run_then (or_r64_r64_effect_step (variant.address 0x1008a6) 0x4d 0xf7
    (by unfold RexWPrefix; decide) (by cases variant <;> decide))
  case sub =>
    rw [show variant.address 0x1008a6 = variant.address 0x1008a2 + 4 by cases variant <;> rfl]
    exact codeRange_mem_of_drop (p := variant.address 0x1008a2) 4 (by cases variant <;> decide +kernel)
  case boundary => intro _ _; have haddr := text_address_ne_return hOutside (0x8a9 + (if variant = .saved then 0 else 0x6b0)) (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  md5_run_then (Stores.mov_m64_r64_effect_step (variant.address 0x1008a9) 0x4c
    (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x40))
    (by cases variant <;> decide) (by cases variant <;> decide) (by cases variant <;> decide))
  case sub =>
    rw [show variant.address 0x1008a9 = variant.address 0x1008a2 + 7 by cases variant <;> rfl]
    exact codeRange_mem_of_drop (p := variant.address 0x1008a2) 7 (by cases variant <;> decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by cases variant <;> x86_norm [Variant.address])
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by cases variant <;> x86_norm [Variant.address]) ?_ ?_, ?_⟩
    · x86_norm
      exact Export.stackWritable h.toStorage 0x40 8 (by cases variant <;> decide)
    · x86_norm
      have haddr := Export.stackTextApart h.toStorage 64 8 (0x8a9 + (if variant = .saved then 0 else 0x6b0)) 5 (by cases variant <;> decide) (by cases variant <;> decide +kernel); cases variant <;> exact haddr
    · apply Effect.avoids_of_components_mem_rip
        (movM64R64Effect_components (variant.address 0x1008a9) 15 (.sib 4 none 0 (.d8 0x40)) t)
      change RangeApart (stackPtr t + 0x40) 8 (variant.address 0x1008a2) 20
      rw [hsp]
      have haddr := Export.stackTextApart h.toStorage 64 8 (0x8a2 + (if variant = .saved then 0 else 0x6b0)) 20 (by cases variant <;> decide) (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  case boundary => intro _ _; have haddr := text_address_ne_return hOutside (0x8ae + (if variant = .saved then 0 else 0x6b0)) (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  md5_run_then (Stores.mov_m64_r64_effect_step (variant.address 0x1008ae) 0x4c
    (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 0x98))
    (by cases variant <;> decide) (by cases variant <;> decide) (by cases variant <;> decide))
  case sub =>
    rw [show variant.address 0x1008ae = variant.address 0x1008a2 + 12 by cases variant <;> rfl]
    exact codeRange_mem_of_drop (p := variant.address 0x1008a2) 12 (by cases variant <;> decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by cases variant <;> x86_norm [Variant.address])
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by cases variant <;> x86_norm [Variant.address]) ?_ ?_, ?_⟩
    · x86_norm
      exact Export.stackWritable h.toStorage 0x98 8 (by cases variant <;> decide)
    · x86_norm
      have haddr := Export.stackTextApart h.toStorage 152 8 (0x8ae + (if variant = .saved then 0 else 0x6b0)) 8 (by cases variant <;> decide) (by cases variant <;> decide +kernel); cases variant <;> exact haddr
    · apply Effect.avoids_of_components_mem_rip
        (movM64R64Effect_components (variant.address 0x1008ae) 15 (.sib 4 none 0 (.d32 0x98)) t)
      change RangeApart (stackPtr t + 0x98) 8 (variant.address 0x1008a2) 20
      rw [hsp]
      have haddr := Export.stackTextApart h.toStorage 152 8 (0x8a2 + (if variant = .saved then 0 else 0x6b0)) 20 (by cases variant <;> decide) (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  case boundary => intro _ _; have haddr := text_address_ne_return hOutside (0x8b6 + (if variant = .saved then 0 else 0x6b0)) (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [effect]
  · x86_norm [effect, value, stackPtr]
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect, stackPtr]
    exact ⟨Or.inl rfl, Or.inr rfl⟩

end Md5.Proofs.Buffered.FinalizeReset.Length
