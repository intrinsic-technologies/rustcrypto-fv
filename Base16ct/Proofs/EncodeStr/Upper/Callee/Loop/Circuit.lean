import Base16ct.Proofs.EncodeStr.Upper.Machine
import Base16ct.Proofs.EncodeStr.Upper.ByteEncoding
import Base16ct.Proofs.EncodeStr.Upper.LoopInstructions
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.ByteLogic (andR8Imm8Effect)
open Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Byte (addR8R8Effect mergeGPR8_setWidth)

private theorem circuit_instruction [Bindings] {p : BitVec 64} {bytes : List UInt8}
    {e : RamState → Effect} (step : StepEffect (fun s ↦ s.RIP = p) (codeRange p bytes) e)
    (offset next : Nat) (hlen : offset + bytes.length ≤ Extracted.textBytes.size)
    (hp : p = Extracted.textAddress + BitVec.ofNat 64 offset)
    (hb : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (hn : next < Extracted.textBytes.size)
    (he : ∀ s, (e s).rip = Extracted.textAddress + BitVec.ofNat 64 next)
    (hav : ∀ s, (e s).Avoids Extracted.programImage)
    {boundary : ReturnBoundary} (hout : ¬ InProgram boundary.rip)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hip : s.RIP = p) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (e s).Holds s t := by
  have hcode := program_text_slice hc offset bytes.length hlen
  rw [← hp, hb] at hcode
  obtain ⟨t, ha, ht, hh⟩ := step.advances hr hcode hip
    (he s ▸ text_address_ne_return hout next hn)
  exact ⟨t, ha, ht, hh.codeIn (hav s) hc, hh⟩

private theorem circuit_read {t : RamState} {r : BitVec 5} {v : BitVec 64}
    (h : (Operand.reg r : Operand 64).read t = v) (n : Nat) :
    (Operand.reg r : Operand n).read t = v.setWidth n := by
  change t.GPR[gprIndex r].setWidth n = _
  simpa only [Operand.read_reg64] using congrArg (BitVec.setWidth n) h

theorem highCircuit_advances_raw [Bindings] {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) {s : RamState} (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x1005f5)
    (b : UInt8) (hb : s.regValue .r9 = b.toBitVec.setWidth 64) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x100614 ∧
      AgreesExcept [.reg 10, .reg 11, .flags, .rip] s t ∧
      (Operand.reg 11 : Operand 8).read t =
        (((57 - ((b.toBitVec.setWidth 32 >>> 4) ||| 48)) >>> 8).setWidth 8 &&& 7) +
          (((b.toBitVec.setWidth 32 >>> 4) ||| 48).setWidth 8) := by
  obtain ⟨s1, a1, r1, c1, h1⟩ := circuit_instruction
    (mov_r32_r32_rex_effect_step 0x1005f5 0x45 0xca (by unfold RexNoWPrefix; decide +kernel) rfl)
    0x5f5 0x5f8 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [movR32R32Effect, Effect.components, Component.Covers]) _)
    hout hr hc hip
  change (movR32R32Effect 0x1005f5 3 10 9 s).Holds s s1 at h1
  obtain ⟨s2, a2, r2, c2, h2⟩ := circuit_instruction
    (shr_r32_imm8_rex_effect_step 0x1005f8 0x41 0xea 4
      (by unfold RexNoWPrefix; decide +kernel) rfl rfl)
    0x5f8 0x5fc (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [shrR32Effect, Effect.components, Component.Covers]) _)
    hout r1 c1 h1.rip
  change (shrR32Effect 0x1005f8 4 10 4 s1).Holds s1 s2 at h2
  obtain ⟨s3, a3, r3, c3, h3⟩ := circuit_instruction
    (or_r10d_48_effect_step 0x1005fc)
    0x5fc 0x600 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [orR32Imm8Effect, Effect.components, Component.Covers]) _)
    hout r2 c2 h2.rip
  change (orR32Imm8Effect 0x1005fc 10 48 s2).Holds s2 s3 at h3
  obtain ⟨s4, a4, r4, c4, h4⟩ := circuit_instruction
    (mov_r32_imm32_rex_effect_step 0x100600 0x41 0xbb
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) 57)
    0x600 0x606 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [movR32Imm32Effect, Effect.components, Component.Covers]) _)
    hout r3 c3 h3.rip
  change (movR32Imm32Effect 0x100600 6 11 57 s3).Holds s3 s4 at h4
  obtain ⟨s5, a5, r5, c5, h5⟩ := circuit_instruction
    (sub_r32_r32_rex_effect_step 0x100606 0x45 0xd3 (by unfold RexNoWPrefix; decide +kernel) rfl)
    0x606 0x609 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [subR32R32Effect, Effect.components, Component.Covers]) _)
    hout r4 c4 h4.rip
  change (subR32R32Effect 0x100606 3 11 10 s4).Holds s4 s5 at h5
  obtain ⟨s6, a6, r6, c6, h6⟩ := circuit_instruction
    (shr_r32_imm8_rex_effect_step 0x100609 0x41 0xeb 8
      (by unfold RexNoWPrefix; decide +kernel) rfl rfl)
    0x609 0x60d (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [shrR32Effect, Effect.components, Component.Covers]) _)
    hout r5 c5 h5.rip
  change (shrR32Effect 0x100609 4 11 8 s5).Holds s5 s6 at h6
  obtain ⟨s7, a7, r7, c7, h7⟩ := circuit_instruction
    (and_r11b_7_effect_step 0x10060d)
    0x60d 0x611 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [andR8Imm8Effect, Effect.components, Component.Covers]) _)
    hout r6 c6 h6.rip
  change (andR8Imm8Effect 0x10060d 4 11 7 s6).Holds s6 s7 at h7
  obtain ⟨s8, a8, r8, c8, h8⟩ := circuit_instruction
    (add_r11b_r10b_effect_step 0x100611)
    0x611 0x614 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [addR8R8Effect, Effect.components, Component.Covers]) _)
    hout r7 c7 h7.rip
  change (addR8R8Effect 0x100611 11 10 s7).Holds s7 s8 at h8
  refine ⟨s8, ?_, r8, c8, h8.rip, ?_, ?_⟩
  · exact ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8
  · exact ((((((h1.agrees.trans h2.agrees).trans h3.agrees).trans h4.agrees).trans
      h5.agrees).trans h6.agrees).trans h7.agrees).trans h8.agrees |>.mono (by
        simp [Effect.components, movR32R32Effect, shrR32Effect, orR32Imm8Effect,
          movR32Imm32Effect, subR32R32Effect, andR8Imm8Effect, addR8R8Effect])
  · have hbyte : (Operand.reg 9 : Operand 32).read s = b.toBitVec.setWidth 32 := by
      have h64 : (Operand.reg 9 : Operand 64).read s = b.toBitVec.setWidth 64 := hb
      simpa using circuit_read h64 32
    have w1 := circuit_read h1.writes 32
    have w2 := circuit_read h2.writes 32
    have w3 := circuit_read h3.writes 32
    have w4 := circuit_read h4.writes 32
    have keep10_4 := h4.agrees.read (n := 32) (r := 10)
      (by simp [movR32Imm32Effect, Effect.components])
    have w5 := circuit_read h5.writes 32
    have w6 := circuit_read h6.writes 8
    have w7 := circuit_read h7.writes 8
    have keep10 := ((h4.agrees.trans h5.agrees).trans h6.agrees).trans h7.agrees
      |>.read (n := 8) (r := 10) (by
        simp [Effect.components, movR32Imm32Effect, subR32R32Effect, shrR32Effect,
          andR8Imm8Effect])
    have w3byte := circuit_read h3.writes 8
    rw [addR8R8Effect.read8 h8, keep10]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      at w1 w2 w3 w4 w5
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), mergeGPR8_setWidth]
      at w6 w7 w3byte
    rw [w7, w6, w5, w4, keep10_4, w3, w2, w1, hbyte, w3byte, w2, w1, hbyte]
    rfl

theorem lowCircuit_advances_raw [Bindings] {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) {s : RamState} (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x100618)
    (b : UInt8) (hb : s.regValue .r9 = b.toBitVec.setWidth 64) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x100634 ∧
      AgreesExcept [.reg 9, .reg 10, .flags, .rip] s t ∧
      (Operand.reg 10 : Operand 8).read t =
        (((57 - ((b.toBitVec.setWidth 32 &&& 15) ||| 48)) >>> 8).setWidth 8 &&& 7) +
          (((b.toBitVec.setWidth 32 &&& 15) ||| 48).setWidth 8) := by
  obtain ⟨s1, a1, r1, c1, h1⟩ := circuit_instruction
    (and_r32_imm8_rex_effect_step 0x100618 0x41 0xe1 15
      (by unfold RexNoWPrefix; decide +kernel) rfl rfl)
    0x618 0x61c (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [andR32Imm8Effect, Effect.components, Component.Covers]) _)
    hout hr hc hip
  change (andR32Imm8Effect 0x100618 4 9 15 s).Holds s s1 at h1
  obtain ⟨s2, a2, r2, c2, h2⟩ := circuit_instruction
    (or_r9d_48_effect_step 0x10061c)
    0x61c 0x620 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [orR32Imm8Effect, Effect.components, Component.Covers]) _)
    hout r1 c1 h1.rip
  change (orR32Imm8Effect 0x10061c 9 48 s1).Holds s1 s2 at h2
  obtain ⟨s3, a3, r3, c3, h3⟩ := circuit_instruction
    (mov_r32_imm32_rex_effect_step 0x100620 0x41 0xba
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) 57)
    0x620 0x626 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [movR32Imm32Effect, Effect.components, Component.Covers]) _)
    hout r2 c2 h2.rip
  change (movR32Imm32Effect 0x100620 6 10 57 s2).Holds s2 s3 at h3
  obtain ⟨s4, a4, r4, c4, h4⟩ := circuit_instruction
    (sub_r32_r32_rex_effect_step 0x100626 0x45 0xca (by unfold RexNoWPrefix; decide +kernel) rfl)
    0x626 0x629 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [subR32R32Effect, Effect.components, Component.Covers]) _)
    hout r3 c3 h3.rip
  change (subR32R32Effect 0x100626 3 10 9 s3).Holds s3 s4 at h4
  obtain ⟨s5, a5, r5, c5, h5⟩ := circuit_instruction
    (shr_r32_imm8_rex_effect_step 0x100629 0x41 0xea 8
      (by unfold RexNoWPrefix; decide +kernel) rfl rfl)
    0x629 0x62d (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [shrR32Effect, Effect.components, Component.Covers]) _)
    hout r4 c4 h4.rip
  change (shrR32Effect 0x100629 4 10 8 s4).Holds s4 s5 at h5
  obtain ⟨s6, a6, r6, c6, h6⟩ := circuit_instruction
    (and_r10b_7_effect_step 0x10062d)
    0x62d 0x631 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [andR8Imm8Effect, Effect.components, Component.Covers]) _)
    hout r5 c5 h5.rip
  change (andR8Imm8Effect 0x10062d 4 10 7 s5).Holds s5 s6 at h6
  obtain ⟨s7, a7, r7, c7, h7⟩ := circuit_instruction
    (add_r10b_r9b_effect_step 0x100631)
    0x631 0x634 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    (fun _ ↦ rfl)
    (fun _ ↦ Effect.Avoids.of_noMem
      (by simp [addR8R8Effect, Effect.components, Component.Covers]) _)
    hout r6 c6 h6.rip
  change (addR8R8Effect 0x100631 10 9 s6).Holds s6 s7 at h7
  refine ⟨s7, ?_, r7, c7, h7.rip, ?_, ?_⟩
  · exact (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7
  · exact (((((h1.agrees.trans h2.agrees).trans h3.agrees).trans h4.agrees).trans
      h5.agrees).trans h6.agrees).trans h7.agrees |>.mono (by
        simp [Effect.components, andR32Imm8Effect, shrR32Effect, orR32Imm8Effect,
          movR32Imm32Effect, subR32R32Effect, andR8Imm8Effect, addR8R8Effect])
  · have hbyte : (Operand.reg 9 : Operand 32).read s = b.toBitVec.setWidth 32 := by
      have h64 : (Operand.reg 9 : Operand 64).read s = b.toBitVec.setWidth 64 := hb
      simpa using circuit_read h64 32
    have w1 := circuit_read h1.writes 32
    have w2 := circuit_read h2.writes 32
    have w3 := circuit_read h3.writes 32
    have keep9_3 := h3.agrees.read (n := 32) (r := 9)
      (by simp [movR32Imm32Effect, Effect.components])
    have w4 := circuit_read h4.writes 32
    have w5 := circuit_read h5.writes 8
    have w6 := circuit_read h6.writes 8
    have keep9 := ((h3.agrees.trans h4.agrees).trans h5.agrees).trans h6.agrees
      |>.read (n := 8) (r := 9) (by
        simp [Effect.components, movR32Imm32Effect, subR32R32Effect, shrR32Effect,
          andR8Imm8Effect])
    have w2byte := circuit_read h2.writes 8
    rw [addR8R8Effect.read8 h7, keep9]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      at w1 w2 w3 w4
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), mergeGPR8_setWidth]
      at w5 w6 w2byte
    rw [w6, w5, w4, w3, keep9_3, w2, w1, hbyte, w2byte, w1, hbyte]
    rfl

theorem highCircuit_advances [Bindings] {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) {s : RamState} (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x1005f5)
    (b : UInt8) (hb : s.regValue .r9 = b.toBitVec.setWidth 64) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x100614 ∧
      AgreesExcept [.reg 10, .reg 11, .flags, .rip] s t ∧
      (Operand.reg 11 : Operand 8).read t =
        (Standards.RFC.BaseEncodings.Alphabet.base16Upper.character (b.toNat / 16)).toBitVec := by
  obtain ⟨t, ha, hr, hc, hip, hf, hv⟩ := highCircuit_advances_raw hout hr hc hip b hb
  refine ⟨t, ha, hr, hc, hip, hf, ?_⟩
  rw [hv]
  exact congrArg UInt8.toBitVec (nibbleCharacter_high b)

theorem lowCircuit_advances [Bindings] {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) {s : RamState} (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x100618)
    (b : UInt8) (hb : s.regValue .r9 = b.toBitVec.setWidth 64) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x100634 ∧
      AgreesExcept [.reg 9, .reg 10, .flags, .rip] s t ∧
      (Operand.reg 10 : Operand 8).read t =
        (Standards.RFC.BaseEncodings.Alphabet.base16Upper.character (b.toNat % 16)).toBitVec := by
  obtain ⟨t, ha, hr, hc, hip, hf, hv⟩ := lowCircuit_advances_raw hout hr hc hip b hb
  refine ⟨t, ha, hr, hc, hip, hf, ?_⟩
  rw [hv]
  exact congrArg UInt8.toBitVec (nibbleCharacter_low b)

end Base16ct.Proofs.EncodeStr.Upper
