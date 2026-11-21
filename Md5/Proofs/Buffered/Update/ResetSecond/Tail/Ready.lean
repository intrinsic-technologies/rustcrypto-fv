import Md5.Proofs.Buffered.Update.ResetSecond.Preparation
import Md5.Proofs.Buffered.Update.ResetSecond.Position
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] tailPointerEffect tailCopyEffect

@[local x86_compose] private theorem stackPtr_read (s : RamState) :
    stackPtr s = (.reg 4 : Operand 64).read s := rfl

@[local x86_local] theorem tailCopyEffect_local (kind : UpdateKind) : Effect.Local (tailCopyEffect kind) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [tailCopyEffect, UpdateKind.context, stackPtr, h.read_reg, h.gpr]
  · simpa only [tailCopyEffect, Effect.flag] using congrArg some hi
  · by_cases hk : kind = .resetDiscardSecond <;>
      simp [tailCopyEffect, hk, Write.Full, Operand.Full]

def tailReadyEffect (kind : UpdateKind) (s : RamState) : Effect :=
  let full := (.reg 14 : Operand 64).read s &&& 0x7fffffffffffffc0
  let rest := (((.reg 14 : Operand 32).read s) &&& 63).setWidth 64
  { rip := (pc kind 0x100a6c)
    writes := [⟨(.reg 0 : Operand 64), full⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 14 : Operand 64), rest⟩,
      ⟨(.reg kind.inputRegister : Operand 64), (.reg kind.inputRegister : Operand 64).read s + full⟩,
      ⟨(.mem (kind.context s + 63) : Operand 8), rest.setWidth 8⟩,
      ⟨(.reg 7 : Operand 64), if kind = .resetDiscardSecond then kind.context s else (.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), rest⟩] ++
      (if kind = .resetDiscardSecond then [⟨(.reg 6 : Operand 64), (.reg 3 : Operand 64).read s + full⟩] else [])
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem tail_ready [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {initial s : RamState} (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input initial)
    {changes : List Component} (ha : AgreesExcept changes initial s)
    (hsp : stackPtr s = stackPtr initial)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hip : s.RIP = (pc kind 0x100a4a)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (tailReadyEffect kind s).Holds s t := by
  have hb : CodeIn (codeRange (pc kind 0x100a4a) (tailPointerBytes kind)) s := by
    rcases hkind with rfl | rfl | rfl
    · exact program_text_slice hc 0xa4a 23 (by decide +kernel)
    · exact program_text_slice hc 0x10da 23 (by decide +kernel)
    · exact program_text_slice hc 0x15b5 23 (by decide +kernel)
  obtain ⟨f₁, v, ha₁, hr₁, _, he₁⟩ := tail_pointer_prepare hkind boundary h.boundaryOutside s hr hb hip
  have hc₁ : CodeIn Extracted.programImage v := he₁.codeIn (by
    apply Effect.Avoids.of_noMem
    rcases hkind with rfl | rfl | rfl <;> simp [tailPointerEffect, UpdateKind.inputRegister, Effect.components, Component.Covers]) hc
  have hsp₁ : stackPtr v = stackPtr s :=
    he₁.agrees.read (n := 64) (r := 4) (by rcases hkind with rfl | rfl | rfl <;> simp [tailPointerEffect, UpdateKind.inputRegister, Effect.components])
  obtain ⟨w, ha₂, hr₂, hc₂, he₂⟩ := position_store hkind h (ha.trans he₁.agrees)
    (hsp₁.trans hsp) hr₁ hc₁ (Or.inr ⟨rfl, rfl⟩) he₁.rip
  have hb₂ : CodeIn (codeRange (pc kind 0x100a66) (tailCopyBytes kind)) w := by
    rcases hkind with rfl | rfl | rfl
    · exact program_text_slice hc₂ 0xa66 6 (by decide +kernel)
    · exact program_text_slice hc₂ 0x10f6 6 (by decide +kernel)
    · exact program_text_slice hc₂ 0x15d1 11 (by decide +kernel)
  obtain ⟨f₃, t, ha₃, hr₃, _, he₃⟩ := tail_copy_prepare hkind boundary h.boundaryOutside
    w hr₂ hb₂ (by rcases hkind with rfl | rfl | rfl <;> exact he₂.rip)
  have hc₃ : CodeIn Extracted.programImage t := he₃.codeIn (by
    apply Effect.Avoids.of_noMem
    rcases hkind with rfl | rfl | rfl <;> simp [tailCopyEffect, Effect.components, Component.Covers]) hc₂
  have hstoreLocal : Effect.Local (storeEffect (pc kind 0x100a61) 5
      (fun u ↦ stackPtr u + BitVec.ofNat 64 (kind.contextOffset + 63))
      (fun u ↦ (.reg 14 : Operand 8).read u)) := by
    rcases hkind with rfl | rfl | rfl
    · exact Update.Byte.movM8R8Effect_local 0x100a61 5 14 (.sib 4 none 0 (.d8 71))
    · exact Update.Byte.movM8R8Effect_local 0x1010f1 5 14 (.sib 4 none 0 (.d8 71))
    · exact Update.Byte.movM8R8Effect_local 0x1015cc 5 14 (.sib 4 none 0 (.d8 95))
  have hs := he₁.seq hstoreLocal
    (by rcases hkind with rfl | rfl | rfl <;> simp [tailPointerEffect, Write.Full, Operand.Full]) he₂
  have htotal := hs.seq (tailCopyEffect_local kind) (by
    rcases hkind with rfl | rfl | rfl <;> x86_norm) he₃
  refine ⟨f₁ + 1 + f₃, t, (ha₁.trans ha₂).trans ha₃, hr₃, hc₃, ?_⟩
  rcases hkind with rfl | rfl | rfl
  all_goals apply htotal.weaken
  all_goals first
    | solve | x86_norm [tailReadyEffect, pc, UpdateKind.inputRegister, UpdateKind.context, UpdateKind.contextOffset]
    | solve | intro i; cases i <;> x86_norm [tailReadyEffect, pc, UpdateKind.inputRegister, UpdateKind.context, UpdateKind.contextOffset]

end Md5.Proofs.Buffered.ResetSecond
