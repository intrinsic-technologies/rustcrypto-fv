import Md5.Proofs.Buffered.Update.ResetFirst.KindMachine
import Md5.Proofs.Buffered.Update.Store
import Md5.Proofs.Buffered.Update.Slices.Byte
import Md5.Proofs.Block.Rounds.Store.Compose

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] tailPointerEffect_of_kind tailCopyEffect_of_kind

@[local x86_compose] private theorem stackPtr_read (s : RamState) :
    stackPtr s = (.reg 4 : Operand 64).read s := rfl

@[local x86_local] theorem tailCopyEffect_local_of_kind (kind : UpdateKind) : Effect.Local (tailCopyEffect_of_kind kind) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [tailCopyEffect_of_kind, stackPtr_read, h.read_reg]
  · simpa only [tailCopyEffect_of_kind, Effect.flag] using congrArg some hi
  · simp [tailCopyEffect_of_kind, Write.Full, Operand.Full]

def tailReadyEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  let full := (.reg (reg kind 3) : Operand 64).read s &&& 0x7fffffffffffffc0
  let rest := (((.reg (reg kind 3) : Operand 32).read s) &&& 63).setWidth 64
  { rip := pc kind 0x765
    writes := [⟨(.reg 0 : Operand 64), full⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg (reg kind 3) : Operand 64), rest⟩,
      ⟨(.reg kind.inputRegister : Operand 64), (.reg kind.inputRegister : Operand 64).read s + full⟩,
      ⟨(.mem (stackPtr s + stackOffset kind 71) : Operand 8), rest.setWidth 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + stackOffset kind 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg kind.inputRegister : Operand 64).read s + full⟩,
      ⟨(.reg 2 : Operand 64), rest⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def tailStoreLength (kind : UpdateKind) : Nat := if kind = .resetDiscardFirst then 5 else 4

def tailStoreMode (kind : UpdateKind) : AddrMode :=
  .sib 4 none 0 (.d8 (BitVec.ofNat 8 (kind.contextOffset + 63)))

def tailStoreBytes (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then [0x44, 0x88, 0x6c, 0x24, 0x5f]
  else [0x88, 0x5c, 0x24, 0x47]

private theorem tail_position_store_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    {boundary : ReturnBoundary} {message input : ByteArray} {initial s : RamState}
    (h : UpdatePre kind boundary message input initial)
    {changes : List Component} (ha : AgreesExcept changes initial s)
    (hsp : stackPtr s = stackPtr initial)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = pc kind 0x756) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      (Update.Byte.movM8R8Effect (pc kind 0x756) (tailStoreLength kind)
        (reg kind 3) (tailStoreMode kind) s).Holds s t := by
  have htext : ∀ j < tailStoreLength kind, InProgram (pc kind 0x756 + BitVec.ofNat 64 j) := by
    rcases hk with rfl | rfl | rfl
    all_goals intro j hj
    all_goals simp only [tailStoreLength, reduceCtorEq, ite_true, ite_false] at hj
    · have hn : 0x75a ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0x756 + j) (by omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hx
      exact hx
    · have hn : 0xe0a ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0xe06 + j) (by omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hx
      exact hx
    · have hn : 0x1495 ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0x1490 + j) (by omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hx
      exact hx
  have hp := h.contextStorePre ha hsp hrip (tailStoreLength kind) 63 1 (by decide) htext
  have haddr : storeAddrAt (pc kind 0x756) (tailStoreMode kind) (tailStoreLength kind) =
      (fun u ↦ stackPtr u + BitVec.ofNat 64 (kind.contextOffset + 63)) := by
    rcases hk with rfl | rfl | rfl <;> funext u <;> rfl
  have hb : CodeIn (codeRange (pc kind 0x756) (tailStoreBytes kind)) s := by
    rcases hk with rfl | rfl | rfl
    · exact program_text_slice hcode 0x756 4 (by decide +kernel)
    · exact program_text_slice hcode 0xe06 4 (by decide +kernel)
    · exact program_text_slice hcode 0x1490 5 (by decide +kernel)
  have hs : StepEffect (Memory.StorePre (pc kind 0x756) (tailStoreLength kind)
      (storeAddrAt (pc kind 0x756) (tailStoreMode kind) (tailStoreLength kind)) 1)
      (codeRange (pc kind 0x756) (tailStoreBytes kind))
      (Update.Byte.movM8R8Effect (pc kind 0x756) (tailStoreLength kind) (reg kind 3) (tailStoreMode kind)) := by
    rcases hk with rfl | rfl | rfl
    · exact Update.Byte.mov_m8_r8_effect_step 0x100756 3 (.sib 4 none 0 (.d8 71))
        (by decide) (by decide) (by decide) (by decide)
    · exact Update.Byte.mov_m8_r8_effect_step 0x100e06 3 (.sib 4 none 0 (.d8 71))
        (by decide) (by decide) (by decide) (by decide)
    · exact Update.Byte.mov_m8_r8_rex_effect_step 0x101490 0x44 (by unfold RexPrefix; decide) 5 (.sib 4 none 0 (.d8 95))
        (by decide) (by decide) (by decide)
  obtain ⟨t, hadv, ht, he⟩ := hs.advances hready hb (haddr ▸ hp) (by
    rcases hk with rfl | rfl | rfl
    · exact text_address_ne_return h.boundaryOutside 0x75a (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0xe0a (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0x1495 (by decide +kernel))
  refine ⟨t, hadv, ht, ?_, he⟩
  apply he.codeIn _ hcode
  intro x hx c hc hcov
  simp only [Update.Byte.movM8R8Effect, storeEffect_components,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, heq⟩ := hcov
    have hw := h.contextWritable_of_agrees ha 63 1 (by decide)
    have hx' : InProgram x.1 := ⟨x.2, hx⟩
    rw [haddr] at heq
    rw [heq] at hx'
    dsimp only at hx'
    rw [hsp] at hx'
    exact hw.code j hj hx'
  · exact hcov

theorem tail_ready_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {initial s : RamState} (h : UpdatePre kind boundary message input initial)
    {changes : List Component} (ha : AgreesExcept changes initial s)
    (hsp : stackPtr s = stackPtr initial)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hip : s.RIP = (pc kind 0x740)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (tailReadyEffect_of_kind kind s).Holds s t := by
  obtain ⟨f₁, v, ha₁, hr₁, _, he₁⟩ := tail_pointer_prepare_of_kind hk boundary h.boundaryOutside s hr hc hip
  have hc₁ : CodeIn Extracted.programImage v := he₁.codeIn (by
    apply Effect.Avoids.of_noMem
    simp [tailPointerEffect_of_kind, Effect.components, Component.Covers]) hc
  have hsp₁ : stackPtr v = stackPtr s :=
    he₁.agrees.read (n := 64) (r := 4) (by rcases hk with rfl | rfl | rfl <;> simp [reg, UpdateKind.inputRegister, tailPointerEffect_of_kind, Effect.components])
  obtain ⟨w, ha₂, hr₂, hc₂, he₂⟩ := tail_position_store_of_kind hk h (ha.trans he₁.agrees)
    (hsp₁.trans hsp) hr₁ hc₁ he₁.rip
  obtain ⟨f₃, t, ha₃, hr₃, _, he₃⟩ := tail_copy_prepare_of_kind hk boundary h.boundaryOutside
    w hr₂ hc₂ (by rcases hk with rfl | rfl | rfl <;> exact he₂.rip)
  have hc₃ : CodeIn Extracted.programImage t := he₃.codeIn (by
    apply Effect.Avoids.of_noMem
    simp [tailCopyEffect_of_kind, Effect.components, Component.Covers]) hc₂
  have hs := he₁.seq (Update.Byte.movM8R8Effect_local (pc kind 0x756) (tailStoreLength kind) (reg kind 3) (tailStoreMode kind))
    (by simp [tailPointerEffect_of_kind, Write.Full, Operand.Full]) he₂
  have htotal := hs.seq (tailCopyEffect_local_of_kind kind) (by rcases hk with rfl | rfl | rfl <;> x86_norm [tailStoreMode, tailStoreLength]) he₃
  refine ⟨f₁ + 1 + f₃, t, (ha₁.trans ha₂).trans ha₃, hr₃, hc₃, ?_⟩
  apply htotal.weaken
  · rcases hk with rfl | rfl | rfl <;> x86_norm [tailReadyEffect_of_kind, tailPointerEffect_of_kind, tailCopyEffect_of_kind, tailStoreMode, tailStoreLength, pc, reg, stackOffset, UpdateKind.contextOffset, UpdateKind.inputRegister]
  · rcases hk with rfl | rfl | rfl <;> x86_norm [tailReadyEffect_of_kind, tailPointerEffect_of_kind, tailCopyEffect_of_kind, tailStoreMode, tailStoreLength, pc, reg, stackOffset, UpdateKind.contextOffset, UpdateKind.inputRegister]
  · rcases hk with rfl | rfl | rfl <;> intro i <;> cases i <;> x86_norm [tailReadyEffect_of_kind, tailPointerEffect_of_kind, tailCopyEffect_of_kind, tailStoreMode, tailStoreLength, pc, reg, stackOffset, UpdateKind.contextOffset, UpdateKind.inputRegister]
  · rcases hk with rfl | rfl | rfl <;> x86_norm [tailReadyEffect_of_kind, tailPointerEffect_of_kind, tailCopyEffect_of_kind, tailStoreMode, tailStoreLength, pc, reg, stackOffset, UpdateKind.contextOffset, UpdateKind.inputRegister]


def tailReadyEffect (s : RamState) : Effect := tailReadyEffect_of_kind .resetFirst s

theorem tail_ready [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {initial s : RamState} (h : UpdatePre .resetFirst boundary message input initial)
    {changes : List Component} (ha : AgreesExcept changes initial s)
    (hsp : stackPtr s = stackPtr initial)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x100740) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (tailReadyEffect s).Holds s t := by
  exact tail_ready_of_kind (kind := .resetFirst) (Or.inl rfl) h ha hsp hr hc hip

end Md5.Proofs.Buffered.ResetFirst
