import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Frame
import P256.Proofs.Program.SaveRegisters
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program (save_registers saveMemory saveFrame saveMemory_saved)

theorem saveFrame_in_frame {s t : RamState} (h : AgreesExcept (saveFrame s) s t) :
    AgreesExcept (frame s) s t := by
  apply agrees_of_footprint h
  · intro c hc hm
    simp only [saveFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨4, by decide, rfl⟩)
    · simp [frame]
    all_goals contradiction
  · intro c hc address hcover
    refine ⟨.mem (stackPtr s - 128) 128, by simp [frame], ?_⟩
    simp only [saveFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcover.elim
    · exact hcover.elim
    · exact stack_covers (offset := 8) (by decide) (by decide) hcover
    · exact stack_covers (offset := 16) (by decide) (by decide) hcover
    · exact stack_covers (offset := 24) (by decide) (by decide) hcover
    · exact stack_covers (offset := 32) (by decide) (by decide) hcover
    · exact stack_covers (offset := 40) (by decide) (by decide) hcover
    · exact stack_covers (offset := 48) (by decide) (by decide) hcover

theorem allocate_frame [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109530 32 32 128) :
    ∃ t, Stage s t boundary ∧ t.RIP = 0x10953e ∧ t.external = saveMemory s ∧
      AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, hrun, hready, hloaded, hip, hsp, hmem, hframe⟩ :=
    save_registers pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (by decide)
      (codeOffset := 0x9530) pre.rip
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel⟩
  obtain ⟨t, hstep, hready', he⟩ :=
    sub_r64_imm8_effect_step 0x10953a 0x48 0xec 24
      (by constructor <;> decide +kernel) (by decide +kernel) (by decide +kernel)
      u hready (programText_slice (programLoaded_codeIn hloaded) 0x953a
        [0x48, 0x83, 0xec, 0x18] (by decide +kernel) rfl) hip
  have hrip : t.RIP = 0x10953e := he.rip
  have hsp' : stackPtr t = stackPtr s - 72 := by
    have hw : stackPtr t = stackPtr u - 24 := he.writes
    rw [hw, hsp, BitVec.sub_sub]
    rfl
  have hmem' : t.external = saveMemory s := by
    rw [he.agrees.external (by simp [subR64Imm8Effect_components, Component.Covers]), hmem]
  have hsmall : AgreesExcept (saveFrame s ++ [.flags]) s t := by
    apply (hframe.trans he.agrees).mono
    simp only [subR64Imm8Effect_components, List.mem_append, saveFrame,
      List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with h | (rfl | rfl | rfl)
    · exact .inl h
    · exact .inl (.inl rfl)
    · exact .inr rfl
    · exact .inl (.inr (.inl rfl))
  have hbig : AgreesExcept (frame s) s t := by
    apply ((saveFrame_in_frame hframe).trans he.agrees).mono
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hc
    · simp only [subR64Imm8Effect_components, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨4, by decide, rfl⟩)
      · simp [frame]
      · simp [frame]
  refine ⟨t, ⟨⟨7, hrun.trans (Advances.of_step hstep (.inl ?_))⟩, hready', hbig,
    loaded_of_frame pre hbig, hsp', ?_⟩, hrip, hmem', hsmall⟩
  · rw [hrip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x953e (by decide))
  · intro entry hentry
    change memLoad t.external _ 64 = _
    rw [hmem']
    exact saveMemory_saved s entry hentry

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
