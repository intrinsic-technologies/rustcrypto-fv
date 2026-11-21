import Md5.Proofs.Buffered.FinalizeReset.Prepare.Copy
import Md5.Proofs.Buffered.FinalizeReset.Prepare.Register
import Md5.Proofs.Buffered.FinalizeReset.Prepare.Geometry

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem copy_avoids {variant : Variant} {s : RamState} (h : Storage s variant) :
    (copyEffect s variant).Avoids Extracted.programImage := by
  have hsize := variant.stackBytes_bounds
  intro x hx c hc ha
  simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (Export.stack_cover h (by omega : 240 + 8 ≤ variant.stackBytes) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (Export.stack_cover h (by omega : 232 + 8 ≤ variant.stackBytes) ha)
      (.inl ⟨x.2, hx⟩)

theorem copy_run {variant : Variant} [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage s variant) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = (variant.address 0x1007a6)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (copyEffect s variant).Holds s t := by
  cases variant with
  | saved =>
    obtain ⟨u, ha, hu, he⟩ := (Register.movzx_r15d_al_effect_step 0x1007a6).advances
      hReady (program_text_slice hCode 0x7a6 4 (by decide +kernel)) hRip
      (text_address_ne_return hOutside 0x7aa (by decide +kernel))
    have hcu := he.codeIn (Register.movzxR15dAlEffect_avoids _ _ _) hCode
    have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4) (by simp
      [Register.movzxR15dAlEffect_components])
    have hout : outputAddress u = outputAddress s := by
      unfold outputAddress
      rw [hsp]
      apply memLoad_congr
      intro i hi
      change (u.external[_]?).getD 0 = _
      rw [he.agrees.byte (by simp [Register.movzxR15dAlEffect_components, Component.Covers])]
      rfl
    have hsu : Storage u Variant.saved := hStorage.of_agrees he.agrees hsp hout
    obtain ⟨n, t, hb, ht, _, heb⟩ := copy_body_execution (variant := .saved) boundary hOutside u hu
      (program_text_slice hcu 0x7aa 28 (by decide +kernel)) ⟨hsu, he.rip⟩
    have hmem (a : BitVec 64) : (.mem a : Operand 64).read u =
        (.mem a : Operand 64).read s := by
      apply memLoad_congr
      intro i hi
      change (u.external[_]?).getD 0 = _
      rw [he.agrees.byte (by simp [Register.movzxR15dAlEffect_components, Component.Covers])]
      rfl
    have hw := heb.writes
    simp only [copyBodyEffect, Write.AllHold, hsp, hmem] at hw
    have h15 : (.reg 15 : Operand 64).read t = position s := by
      exact (heb.agrees.read (n := 64) (r := 15) (by
        simp [copyBodyEffect, Effect.components, Write.component, Operand.component])).trans he.writes
    have hfull : (copyEffect s Variant.saved).Holds s t := by
      refine ⟨heb.rip, ⟨h15, hw⟩, trivial, ?_⟩
      apply (he.agrees.trans heb.agrees).mono
      simp [Register.movzxR15dAlEffect, copyEffect, copyBodyEffect,
        Effect.components, Write.component, Operand.component, hsp]
    exact ⟨1 + n, t, ha.trans hb, ht, hfull.codeIn (copy_avoids hStorage) hCode, hfull⟩
  | direct =>
    obtain ⟨u, ha, hu, he⟩ := (Register.movzx_r15d_al_effect_step 0x100e56).advances
      hReady (program_text_slice hCode 0xe56 4 (by decide +kernel)) hRip
      (text_address_ne_return hOutside 0xe5a (by decide +kernel))
    have hcu := he.codeIn (Register.movzxR15dAlEffect_avoids _ _ _) hCode
    have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4) (by simp
      [Register.movzxR15dAlEffect_components])
    have hout : outputAddress u = outputAddress s := by
      unfold outputAddress
      rw [hsp]
      apply memLoad_congr
      intro i hi
      change (u.external[_]?).getD 0 = _
      rw [he.agrees.byte (by simp [Register.movzxR15dAlEffect_components, Component.Covers])]
      rfl
    have hsu : Storage u Variant.direct := hStorage.of_agrees he.agrees hsp hout
    obtain ⟨n, t, hb, ht, _, heb⟩ := copy_body_execution (variant := .direct) boundary hOutside u hu
      (program_text_slice hcu 0xe5a 28 (by decide +kernel)) ⟨hsu, he.rip⟩
    have hmem (a : BitVec 64) : (.mem a : Operand 64).read u =
        (.mem a : Operand 64).read s := by
      apply memLoad_congr
      intro i hi
      change (u.external[_]?).getD 0 = _
      rw [he.agrees.byte (by simp [Register.movzxR15dAlEffect_components, Component.Covers])]
      rfl
    have hw := heb.writes
    simp only [copyBodyEffect, Write.AllHold, hsp, hmem] at hw
    have h15 : (.reg 15 : Operand 64).read t = position s := by
      exact (heb.agrees.read (n := 64) (r := 15) (by
        simp [copyBodyEffect, Effect.components, Write.component, Operand.component])).trans he.writes
    have hfull : (copyEffect s Variant.direct).Holds s t := by
      refine ⟨heb.rip, ⟨h15, hw⟩, trivial, ?_⟩
      apply (he.agrees.trans heb.agrees).mono
      simp [Register.movzxR15dAlEffect, copyEffect, copyBodyEffect,
        Effect.components, Write.component, Operand.component, hsp]
    exact ⟨1 + n, t, ha.trans hb, ht, hfull.codeIn (copy_avoids hStorage) hCode, hfull⟩

end Md5.Proofs.Buffered.FinalizeReset.Prepare
