import Md5.Proofs.Buffered.Update.Store
import Md5.Proofs.Buffered.Update.Slices.Byte
import Md5.Proofs.Buffered.Update.ResetSecond.Layout

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

set_option maxHeartbeats 800000 in
theorem position_store [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {initial s : RamState} (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input initial)
    {changes : List Component} (ha : AgreesExcept changes initial s)
    (hsp : stackPtr s = stackPtr initial)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    {p : BitVec 64} {r : BitVec 3}
    (hsite : (p = pc kind 0x1009b1 ∧ r = (if kind = .resetDiscardSecond then 5 else 4)) ∨ (p = pc kind 0x100a61 ∧ r = 6))
    (hrip : s.RIP = p) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      (storeEffect p 5 (fun u ↦ stackPtr u + BitVec.ofNat 64 (kind.contextOffset + 63))
        (fun u ↦ (Operand.reg (gprNumber 0 1 r) : Operand 8).read u) s).Holds s t := by
  have htext : ∀ j < 5, InProgram (p + BitVec.ofNat 64 j) := by
    intro j hj
    rcases hkind with rfl | rfl | rfl <;>
      rcases hsite with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · have hsize : 0x9b6 ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0x9b1 + j) (by omega)
      have he : Extracted.textAddress + BitVec.ofNat 64 (0x9b1 + j) =
          0x1009b1 + BitVec.ofNat 64 j := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      exact he ▸ hx
    · have hsize : 0xa66 ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0xa61 + j) (by omega)
      have he : Extracted.textAddress + BitVec.ofNat 64 (0xa61 + j) =
          0x100a61 + BitVec.ofNat 64 j := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      exact he ▸ hx
    · have hsize : 0x1046 ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0x1041 + j) (by omega)
      have he : Extracted.textAddress + BitVec.ofNat 64 (0x1041 + j) =
          0x101041 + BitVec.ofNat 64 j := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      exact he ▸ hx
    · have hsize : 0x10f6 ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0x10f1 + j) (by omega)
      have he : Extracted.textAddress + BitVec.ofNat 64 (0x10f1 + j) =
          0x1010f1 + BitVec.ofNat 64 j := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      exact he ▸ hx
    · have hsize : 0x1529 ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0x1524 + j) (by omega)
      have he : Extracted.textAddress + BitVec.ofNat 64 (0x1524 + j) =
          0x101524 + BitVec.ofNat 64 j := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      exact he ▸ hx
    · have hsize : 0x15d1 ≤ Extracted.textBytes.size := by decide +kernel
      have hx := text_address_in_program (0x15cc + j) (by omega)
      have he : Extracted.textAddress + BitVec.ofNat 64 (0x15cc + j) =
          0x1015cc + BitVec.ofNat 64 j := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      exact he ▸ hx
  have hp := h.contextStorePre ha hsp hrip 5 63 1 (by decide) htext
  have hbytes : CodeIn (codeRange p [0x44, 0x88,
      (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (kind.contextOffset + 63))) : AddrMode).modrm r, 0x24, UInt8.ofNat (kind.contextOffset + 63)]) s := by
    rcases hkind with rfl | rfl | rfl <;>
      rcases hsite with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact program_text_slice hcode 0x9b1 5 (by decide +kernel)
    · exact program_text_slice hcode 0xa61 5 (by decide +kernel)
    · exact program_text_slice hcode 0x1041 5 (by decide +kernel)
    · exact program_text_slice hcode 0x10f1 5 (by decide +kernel)
    · exact program_text_slice hcode 0x1524 5 (by decide +kernel)
    · exact program_text_slice hcode 0x15cc 5 (by decide +kernel)
  have hstep := Update.Byte.mov_m8_r8_rex_effect_step p 0x44
    (by unfold RexPrefix; decide) r (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (kind.contextOffset + 63))))
    (by cases kind <;> decide) (by cases kind <;> decide) (by cases kind <;> decide)
  have hstep' : StepEffect (Memory.StorePre p 5 (fun u ↦ stackPtr u + BitVec.ofNat 64 (kind.contextOffset + 63)) 1)
    (codeRange p [0x44, 0x88,
      (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (kind.contextOffset + 63))) : AddrMode).modrm r,
      0x24, UInt8.ofNat (kind.contextOffset + 63)])
    (storeEffect p 5 (fun u ↦ stackPtr u + BitVec.ofNat 64 (kind.contextOffset + 63))
      (fun u ↦ (Operand.reg (gprNumber 0 1 r) : Operand 8).read u)) := by
    rcases hkind with rfl | rfl | rfl <;> exact hstep
  have hne : p + 5 ≠ boundary.rip := by
    rcases hkind with rfl | rfl | rfl <;>
      rcases hsite with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact text_address_ne_return h.boundaryOutside 0x9b6 (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0xa66 (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0x1046 (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0x10f6 (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0x1529 (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0x15d1 (by decide +kernel)
  obtain ⟨t, hadv, ht, he⟩ := hstep'.advances hready hbytes hp hne
  refine ⟨t, hadv, ht, ?_, he⟩
  apply he.codeIn _ hcode
  intro x hx c hc hcov
  simp only [storeEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, heq⟩ := hcov
    have hw := h.contextWritable_of_agrees ha 63 1 (by decide)
    have hav := hw.code
    change ∀ i < 1, ¬ InProgram (stackPtr initial + BitVec.ofNat 64 (kind.contextOffset + 63) + BitVec.ofNat 64 i) at hav
    have hx' : InProgram x.1 := ⟨x.2, hx⟩
    simp only [heq, hsp] at hx'
    exact hav j hj hx' 
  · exact hcov


set_option maxHeartbeats 800000 in
theorem short_finish [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {initial s : RamState} (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input initial)
    {changes : List Component} (ha : AgreesExcept changes initial s)
    (hsp : stackPtr s = stackPtr initial)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = (pc kind 0x1009ae)) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (pc kind 0x1009b6) ∧
      (Operand.mem (kind.context s + 63) : Operand 8).read t =
        (Operand.reg kind.sizeRegister : Operand 8).read s + (Operand.reg (positionRegister kind) : Operand 8).read s ∧
      AgreesExcept [.reg kind.sizeRegister, .flags, .rip, .mem (kind.context s + 63) 1] s t := by
  let rex : UInt8 := if kind = .resetDiscardSecond then 0x41 else 0x45
  let modrm : UInt8 := if kind = .resetDiscardSecond then 0xed else 0xec
  have hb : CodeIn (codeRange (pc kind 0x1009ae) [rex, 0x00, modrm]) s := by
    rcases hkind with rfl | rfl | rfl
    · exact program_text_slice hcode 0x9ae 3 (by decide +kernel)
    · exact program_text_slice hcode 0x103e 3 (by decide +kernel)
    · exact program_text_slice hcode 0x1521 3 (by decide +kernel)
  have hs : StepEffect (fun u ↦ u.RIP = pc kind 0x1009ae)
    (codeRange (pc kind 0x1009ae) [rex, 0x00, modrm])
    (Update.Byte.addR8R8Effect (pc kind 0x1009ae) kind.sizeRegister (positionRegister kind)) := by
    rcases hkind with rfl | rfl | rfl
    · exact Update.Byte.add_r8_r8_effect_step 0x1009ae 0x45 0xec
        (by unfold RexPrefix; decide) (by decide)
    · exact Update.Byte.add_r8_r8_effect_step 0x10103e 0x45 0xec
        (by unfold RexPrefix; decide) (by decide)
    · exact Update.Byte.add_r8_r8_effect_step 0x101521 0x41 0xed
        (by unfold RexPrefix; decide) (by decide)
  have hnext : pc kind 0x1009ae + 3 ≠ boundary.rip := by
    rcases hkind with rfl | rfl | rfl
    · exact text_address_ne_return h.boundaryOutside 0x9b1 (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0x1041 (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0x1524 (by decide +kernel)
  obtain ⟨u, huadv, hu, heu⟩ := hs.advances hready hb hrip
    hnext
  have hcu := heu.codeIn (Update.Byte.addR8R8Effect_avoids _ _ _ _ _) hcode
  have hspu : stackPtr u = stackPtr s := heu.agrees.read (n := 64) (r := 4) (by
    rcases hkind with rfl | rfl | rfl <;> simp [Update.Byte.addR8R8Effect_components, UpdateKind.sizeRegister])
  obtain ⟨t, htadv, ht, hct, het⟩ := position_store hkind h (ha.trans heu.agrees)
    (hspu.trans hsp) hu hcu (Or.inl ⟨rfl, rfl⟩) (by
      rcases hkind with rfl | rfl | rfl <;> exact heu.rip)
  have hv : (Operand.reg kind.sizeRegister : Operand 8).read u =
      (Operand.reg kind.sizeRegister : Operand 8).read s + (Operand.reg (positionRegister kind) : Operand 8).read s :=
    Update.Byte.addR8R8Effect.read8 heu
  refine ⟨t, huadv.trans htadv, ht, hct, (by rcases hkind with rfl | rfl | rfl <;> exact het.rip), ?_, ?_⟩
  · have hw := het.writes
    change (Operand.mem (stackPtr u + BitVec.ofNat 64 (kind.contextOffset + 63)) : Operand 8).read t =
      (Operand.reg (gprNumber 0 1 (if kind = .resetDiscardSecond then 5 else 4)) : Operand 8).read u at hw
    have hw' : (Operand.mem (kind.context u + 63) : Operand 8).read t =
      (Operand.reg kind.sizeRegister : Operand 8).read u := by
      rcases hkind with rfl | rfl | rfl <;> simpa [UpdateKind.context, UpdateKind.contextOffset, UpdateKind.sizeRegister, gprNumber, BitVec.add_assoc, ← BitVec.ofNat_add] using hw
    simpa only [UpdateKind.context, hspu, hv] using hw'
  · have hag := heu.agrees.trans het.agrees
    simp only [Update.Byte.addR8R8Effect_components, storeEffect_components, hspu] at hag
    apply hag.mono
    rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]


end Md5.Proofs.Buffered.ResetSecond
