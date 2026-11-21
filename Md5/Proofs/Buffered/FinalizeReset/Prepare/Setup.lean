import Md5.Proofs.Buffered.FinalizeReset.Prepare.Tail
import Md5.Proofs.Buffered.FinalizeReset.Prepare.Geometry
import Md5.Proofs.Buffered.Xor

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def maskEffect (s : RamState) (variant : Variant := .saved) : Effect :=
  { rip := (variant.address 0x1007cd)
    writes := [⟨(.reg 3 : Operand 64), (.reg 15 : Operand 64).read s ^^^ 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem mask_execution {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (variant.address 0x1007c6))
      (codeRange (variant.address 0x1007c6) [0x4c, 0x89, 0xfb, 0x48, 0x83, 0xf3, 0x3f]) (fun s ↦ maskEffect s variant) := by
  cases variant with
  | saved =>
    md5_run_begin (mov_r64_r64_effect_step 0x1007c6 0x4c 0xfb
      (by unfold RexWPrefix; decide) (by decide))
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7c9 (by decide +kernel)
    md5_run_then (xor_r64_imm8_effect_step 0x1007c9 0x48 0xf3 63
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x1007c6) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x7cd (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, maskEffect]
    · x86_norm [Variant.address, maskEffect]
      rfl
    · intro i; cases i <;> x86_norm [Variant.address, maskEffect]
    · x86_norm [Variant.address, maskEffect]
  | direct =>
    md5_run_begin (mov_r64_r64_effect_step 0x100e76 0x4c 0xfb
      (by unfold RexWPrefix; decide) (by decide))
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe79 (by decide +kernel)
    md5_run_then (xor_r64_imm8_effect_step 0x100e79 0x48 0xf3 63
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    case sub => exact codeRange_mem_of_drop (p := 0x100e76) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xe7d (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [Variant.address, maskEffect]
    · x86_norm [Variant.address, maskEffect]
      rfl
    · intro i; cases i <;> x86_norm [Variant.address, maskEffect]
    · x86_norm [Variant.address, maskEffect]

theorem tail_avoids {variant : Variant} {s : RamState} (hs : Storage s variant)
    (hp : ((.reg 15 : Operand 64).read s).toNat < 64) :
    (tailBodyEffect s variant).Avoids Extracted.programImage := by
  have hsize := variant.stackBytes_bounds
  intro x hx c hc ha
  simp only [tailBodyEffect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  apply hs.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
  apply Export.stack_cover hs (offset := ((.reg 15 : Operand 64).read s).toNat + 8)
    (len := 1) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc] using ha

theorem setup_run {variant : Variant} [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage s variant) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = (variant.address 0x1007c6)) (hPosition : ((.reg 15 : Operand 64).read s).toNat < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (setupEffect s variant).Holds s t := by
  cases variant with
  | saved =>
    obtain ⟨n, u, ha, hu, _, he⟩ := mask_execution (variant := .saved) boundary hOutside s hReady
      (program_text_slice hCode 0x7c6 7 (by decide +kernel)) hRip
    have hcu := he.codeIn (Effect.Avoids.of_noMem (by
      simp [maskEffect, Effect.components, Write.component, Operand.component, Component.Covers]) _) hCode
    have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4) (by
      simp [maskEffect, Effect.components, Write.component, Operand.component])
    have h15 : (.reg 15 : Operand 64).read u = (.reg 15 : Operand 64).read s :=
      he.agrees.read (n := 64) (r := 15) (by
        simp [maskEffect, Effect.components, Write.component, Operand.component])
    have hs : Storage u Variant.saved := agrees_storage hStorage (he.agrees.mono (by
      simp [maskEffect, Effect.components, Write.component, Operand.component, changes]))
    have hp : ((.reg 15 : Operand 64).read u).toNat < 64 := by rwa [h15]
    obtain ⟨m, t, hb, ht, _, heb⟩ := tail_body_execution (variant := .saved) boundary hOutside u hu
      (program_text_slice hcu 0x7cd 19 (by decide +kernel)) ⟨hs, he.rip, hp⟩
    have hw := heb.writes
    simp only [tailBodyEffect, Write.AllHold, hsp, h15] at hw
    have hbx : (.reg 3 : Operand 64).read t = (.reg 15 : Operand 64).read s ^^^ 63 :=
      (heb.agrees.read (n := 64) (r := 3) (by
        simp [tailBodyEffect, Effect.components, Write.component, Operand.component])).trans he.writes
    have hfull : (setupEffect s Variant.saved).Holds s t := by
      refine ⟨heb.rip, ⟨hbx, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.trans he.writes⟩, ?_, ?_⟩
      · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
      · apply (he.agrees.trans heb.agrees).mono
        simp [maskEffect, setupEffect, tailBodyEffect, Effect.components, Write.component,
          Operand.component, hsp]
        exact h15
    exact ⟨n + m, t, ha.trans hb, ht, heb.codeIn (tail_avoids hs hp) hcu, hfull⟩
  | direct =>
    obtain ⟨n, u, ha, hu, _, he⟩ := mask_execution (variant := .direct) boundary hOutside s hReady
      (program_text_slice hCode 0xe76 7 (by decide +kernel)) hRip
    have hcu := he.codeIn (Effect.Avoids.of_noMem (by
      simp [maskEffect, Effect.components, Write.component, Operand.component, Component.Covers]) _) hCode
    have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4) (by
      simp [maskEffect, Effect.components, Write.component, Operand.component])
    have h15 : (.reg 15 : Operand 64).read u = (.reg 15 : Operand 64).read s :=
      he.agrees.read (n := 64) (r := 15) (by
        simp [maskEffect, Effect.components, Write.component, Operand.component])
    have hs : Storage u Variant.direct := agrees_storage hStorage (he.agrees.mono (by
      simp [maskEffect, Effect.components, Write.component, Operand.component, changes]))
    have hp : ((.reg 15 : Operand 64).read u).toNat < 64 := by rwa [h15]
    obtain ⟨m, t, hb, ht, _, heb⟩ := tail_body_execution (variant := .direct) boundary hOutside u hu
      (program_text_slice hcu 0xe7d 19 (by decide +kernel)) ⟨hs, he.rip, hp⟩
    have hw := heb.writes
    simp only [tailBodyEffect, Write.AllHold, hsp, h15] at hw
    have hbx : (.reg 3 : Operand 64).read t = (.reg 15 : Operand 64).read s ^^^ 63 :=
      (heb.agrees.read (n := 64) (r := 3) (by
        simp [tailBodyEffect, Effect.components, Write.component, Operand.component])).trans he.writes
    have hfull : (setupEffect s Variant.direct).Holds s t := by
      refine ⟨heb.rip, ⟨hbx, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.trans he.writes⟩, ?_, ?_⟩
      · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
      · apply (he.agrees.trans heb.agrees).mono
        simp [maskEffect, setupEffect, tailBodyEffect, Effect.components, Write.component,
          Operand.component, hsp]
        exact h15
    exact ⟨n + m, t, ha.trans hb, ht, heb.codeIn (tail_avoids hs hp) hcu, hfull⟩

end Md5.Proofs.Buffered.FinalizeReset.Prepare
