import Md5.Proofs.Buffered.Update.Slices.Tail.Preparation
import Md5.Proofs.Buffered.Update.Slices.Byte
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.MemoryRoutines.Ranges

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] tailPointerEffect tailCopyEffect

@[local x86_compose] private theorem stackPtr_read (s : RamState) :
    stackPtr s = (.reg 4 : Operand 64).read s := rfl

@[local x86_local] theorem tailCopyEffect_local {variant : Bool} : Effect.Local (tailCopyEffect variant) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [tailCopyEffect, stackPtr_read, h.read_reg]
  · simpa only [tailCopyEffect, Effect.flag] using congrArg some hi
  · simp [tailCopyEffect, Write.Full, Operand.Full]

def tailReadyEffect (variant : Bool) (s : RamState) : Effect :=
  let full := (.reg 5 : Operand 64).read s &&& 0x7fffffffffffffc0
  let rest := (((.reg 5 : Operand 32).read s) &&& 63).setWidth 64
  { rip := (pc variant 0x100409)
    writes := [⟨(.reg 0 : Operand 64), full⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 5 : Operand 64), rest⟩,
      ⟨(.reg 14 : Operand 64), (.reg 14 : Operand 64).read s + full⟩,
      ⟨(.mem (stackPtr s + 255) : Operand 8), rest.setWidth 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 192⟩,
      ⟨(.reg 6 : Operand 64), (.reg 14 : Operand 64).read s + full⟩,
      ⟨(.reg 2 : Operand 64), rest⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem tail_ready {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hip : s.RIP = (pc variant 0x1003dd))
    (hw : MemoryRoutines.WritableRange s (stackPtr s + 255) 1) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (tailReadyEffect variant s).Holds s t := by
  cases variant with
  | false =>
    have hb : CodeIn (codeRange 0x1003dd tailPointerBytes) s :=
      program_text_slice hc 0x3dd 22 (by decide +kernel)
    obtain ⟨f₁, v, ha₁, hr₁, _, he₁⟩ := tail_pointer_prepare (variant := false) boundary hout s hr hb hip
    have hc₁ : CodeIn Extracted.programImage v := he₁.codeIn (by
      apply Effect.Avoids.of_noMem
      simp [tailPointerEffect, Effect.components, Component.Covers]) hc
    have hsp : stackPtr v = stackPtr s :=
      he₁.agrees.read (n := 64) (r := 4) (by simp [tailPointerEffect, Effect.components])
    have hw₁ : MemoryRoutines.WritableRange v (stackPtr v + 255) 1 := by
      rw [hsp]
      exact hw.of_agrees he₁.agrees
    have hb₁ : CodeIn (codeRange 0x1003f3 [0x40, 0x88, 0xac, 0x24, 0xff, 0x00, 0x00, 0x00]) v :=
      program_text_slice hc₁ 0x3f3 8 (by decide +kernel)
    have hp₁ : Md5.Proofs.Memory.StorePre 0x1003f3 8
        (storeAddrAt 0x1003f3 (.sib 4 none 0 (.d32 255)) 8) 1 v := by
      refine ⟨he₁.rip, ⟨hw₁.readable.low, hw₁.readable.mem, hw₁.tables⟩, ?_⟩
      intro i hi j hj heq
      apply hw₁.code i hi
      change stackPtr v + 255 + BitVec.ofNat 64 i = _ at heq
      rw [heq]
      have ht := text_address_in_program (0x3f3 + j) (by
        have hs : 0x3fb ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      simpa [Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc] using ht
    obtain ⟨w, ha₂, hr₂, he₂⟩ := (Byte.mov_m8_r8_rex_effect_step 0x1003f3 0x40
      (by unfold RexPrefix; decide) 5 (.sib 4 none 0 (.d32 255))
      (by decide) (by decide) (by decide)).advances hr₁ hb₁ hp₁
        (text_address_ne_return hout 0x3fb (by decide +kernel))
    have hc₂ : CodeIn Extracted.programImage w := by
      apply CodeIn.of_agreesExcept he₂.agrees _ hc₁
      intro x hx c hm hcover
      x86_norm at hm
      rcases hm with rfl | rfl
      · obtain ⟨i, hi, heq⟩ := hcover
        exact hw₁.code i hi (heq ▸ ⟨x.2, hx⟩)
      · exact hcover.elim
    have hb₂ : CodeIn (codeRange 0x1003fb tailCopyBytes) w :=
      program_text_slice hc₂ 0x3fb 14 (by decide +kernel)
    obtain ⟨f₃, t, ha₃, hr₃, _, he₃⟩ := tail_copy_prepare (variant := false) boundary hout w hr₂ hb₂ he₂.rip
    have hc₃ : CodeIn Extracted.programImage t := he₃.codeIn (by
      apply Effect.Avoids.of_noMem
      simp [tailCopyEffect, Effect.components, Component.Covers]) hc₂
    have hs := he₁.seq (Byte.movM8R8Effect_local 0x1003f3 8 5 (.sib 4 none 0 (.d32 255)))
      (by simp [tailPointerEffect, Write.Full, Operand.Full]) he₂
    have htotal := hs.seq (tailCopyEffect_local (variant := false)) (by x86_norm) he₃
    refine ⟨f₁ + 1 + f₃, (t), (ha₁.trans ha₂).trans ha₃, hr₃, hc₃, ?_⟩
    apply htotal.weaken
    · x86_norm [tailReadyEffect]
    · x86_norm [tailReadyEffect]
    · intro i; cases i <;> x86_norm [tailReadyEffect]
    · x86_norm [tailReadyEffect]
  | true =>
    have hb : CodeIn (codeRange 0x10198d tailPointerBytes) s :=
      program_text_slice hc 0x198d 22 (by decide +kernel)
    obtain ⟨f₁, v, ha₁, hr₁, _, he₁⟩ := tail_pointer_prepare (variant := true) boundary hout s hr hb hip
    have hc₁ : CodeIn Extracted.programImage v := he₁.codeIn (by
      apply Effect.Avoids.of_noMem
      simp [tailPointerEffect, Effect.components, Component.Covers]) hc
    have hsp : stackPtr v = stackPtr s :=
      he₁.agrees.read (n := 64) (r := 4) (by simp [tailPointerEffect, Effect.components])
    have hw₁ : MemoryRoutines.WritableRange v (stackPtr v + 255) 1 := by
      rw [hsp]
      exact hw.of_agrees he₁.agrees
    have hb₁ : CodeIn (codeRange 0x1019a3 [0x40, 0x88, 0xac, 0x24, 0xff, 0x00, 0x00, 0x00]) v :=
      program_text_slice hc₁ 0x19a3 8 (by decide +kernel)
    have hp₁ : Md5.Proofs.Memory.StorePre 0x1019a3 8
        (storeAddrAt 0x1019a3 (.sib 4 none 0 (.d32 255)) 8) 1 v := by
      refine ⟨he₁.rip, ⟨hw₁.readable.low, hw₁.readable.mem, hw₁.tables⟩, ?_⟩
      intro i hi j hj heq
      apply hw₁.code i hi
      change stackPtr v + 255 + BitVec.ofNat 64 i = _ at heq
      rw [heq]
      have ht := text_address_in_program (0x19a3 + j) (by
        have hs : 0x19ab ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      simpa [Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc] using ht
    obtain ⟨w, ha₂, hr₂, he₂⟩ := (Byte.mov_m8_r8_rex_effect_step 0x1019a3 0x40
      (by unfold RexPrefix; decide) 5 (.sib 4 none 0 (.d32 255))
      (by decide) (by decide) (by decide)).advances hr₁ hb₁ hp₁
        (text_address_ne_return hout 0x19ab (by decide +kernel))
    have hc₂ : CodeIn Extracted.programImage w := by
      apply CodeIn.of_agreesExcept he₂.agrees _ hc₁
      intro x hx c hm hcover
      x86_norm at hm
      rcases hm with rfl | rfl
      · obtain ⟨i, hi, heq⟩ := hcover
        exact hw₁.code i hi (heq ▸ ⟨x.2, hx⟩)
      · exact hcover.elim
    have hb₂ : CodeIn (codeRange 0x1019ab tailCopyBytes) w :=
      program_text_slice hc₂ 0x19ab 14 (by decide +kernel)
    obtain ⟨f₃, t, ha₃, hr₃, _, he₃⟩ := tail_copy_prepare (variant := true) boundary hout w hr₂ hb₂ he₂.rip
    have hc₃ : CodeIn Extracted.programImage t := he₃.codeIn (by
      apply Effect.Avoids.of_noMem
      simp [tailCopyEffect, Effect.components, Component.Covers]) hc₂
    have hs := he₁.seq (Byte.movM8R8Effect_local 0x1019a3 8 5 (.sib 4 none 0 (.d32 255)))
      (by simp [tailPointerEffect, Write.Full, Operand.Full]) he₂
    have htotal := hs.seq (tailCopyEffect_local (variant := true)) (by x86_norm) he₃
    refine ⟨f₁ + 1 + f₃, (t), (ha₁.trans ha₂).trans ha₃, hr₃, hc₃, ?_⟩
    apply htotal.weaken
    · x86_norm [tailReadyEffect]
    · x86_norm [tailReadyEffect]
    · intro i; cases i <;> x86_norm [tailReadyEffect]
    · x86_norm [tailReadyEffect]

end Md5.Proofs.Buffered.Update.Slices
