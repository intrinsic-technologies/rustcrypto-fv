import Sha1.Proofs.Buffered.Update.Slices.Full.Contracts
import Sha1.Proofs.Buffered.Update.Slices.CompressionFrame
import Sha1.Proofs.Buffered.Update.Slices.Mathematics
import Sha1.Proofs.Buffered.Update.Slices.Counter
import Sha1.Proofs.Buffered.Update.Slices.Frame

namespace Sha1.Proofs.Buffered.Update.Slices.Full

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine (program_text_slice)
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return)

private theorem register_state_address (s : RamState) :
    stackPtr s + 0x120 = UpdateKind.updateFinalize.context s + 72 := by
  rw [UpdateKind.context, BitVec.add_assoc]
  rfl

private theorem prepare_args [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x101d6d) :
    ∃ t, Advances boundary (1 + 1) s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101d78 ∧ AgreesExcept [.reg 7, .reg 6, .rip] s t ∧
      t.regValue .rdi = stackPtr s + 0x120 ∧
      t.regValue .rsi = (Operand.reg 14 : Operand 64).read s := by
  let am : AddrMode := .sib 4 none 0 (.d32 0x120)
  have hb : CodeIn (codeRange 0x101d6d (0x48 :: 0x8d :: am.modrm 7 :: am.tail)) s := by
    rw [show 0x48 :: 0x8d :: am.modrm 7 :: am.tail =
      [0x48, 0x8d, 0xbc, 0x24, 0x20, 1, 0, 0] by decide +kernel]
    exact program_text_slice hc 0x1d6d 8 (by decide +kernel)
  obtain ⟨u, ha, hu, he⟩ := (lea_r64_effect_step 0x101d6d 0x48
    (by decide) 7 am (by decide) (by decide) (by decide)).advances hr hb hip
    (text_address_ne_return hout 0x1d75 (by decide +kernel))
  have hlu : AgreesExcept [.reg 7, .rip] s u := he.agrees
  have hcu := hlu.codeIn (by simp [Component.Covers]) hc
  have hb' : CodeIn (codeRange 0x101d75 [0x4c, 0x89, 0xf6]) u :=
    program_text_slice hcu 0x1d75 3 (by decide +kernel)
  obtain ⟨t, ha', ht, he'⟩ := (mov_r64_r64_effect_step 0x101d75 0x4c 0xf6
    (by decide) (by decide)).advances hu hb' he.rip
    (text_address_ne_return hout 0x1d78 (by decide +kernel))
  have hlt : AgreesExcept [.reg 6, .rip] u t := he'.agrees
  have hct := hlt.codeIn (by simp [Component.Covers]) hcu
  refine ⟨t, ha.trans ha', ht, hct, he'.rip, (hlu.trans hlt).mono (by simp), ?_, ?_⟩
  · change (Operand.reg 7 : Operand 64).read t = _
    exact (hlt.read (by decide)).trans he.writes
  · change (Operand.reg 6 : Operand 64).read t = _
    exact he'.writes.trans (hlu.read (by decide))

theorem batch [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {offset : Nat} (h : UpdatePre .updateFinalize boundary message input s)
    (b : BatchReady boundary message input s offset u)
    (hInputNonzero : (UpdateKind.inputRegion .updateFinalize s input).start ≠ 0) :
    ∃ v, TailReady boundary message input s offset v := by
  let consumed := message ++ input.extract 0 offset
  let suffix := input.extract offset input.size
  have hp : consumed.size = message.size + offset := by
    simp only [consumed, ByteArray.size_append, ByteArray.size_extract,
      Nat.min_eq_left b.offsetBound, Nat.sub_zero]
  have hs : suffix.size = input.size - offset := by simp only [suffix, ByteArray.size_extract, Nat.min_self]
  have hsplit : consumed ++ suffix = message ++ input := by
    simp only [consumed, suffix]
    rw [ByteArray.append_assoc, ← ByteArray.extract_eq_extract_append_extract
      offset (Nat.zero_le offset) b.offsetBound, ByteArray.extract_zero_size]
  have halign : consumed.size % 64 = 0 := hp ▸ b.aligned
  have hcount : (message ++ input).size / 64 =
      (message.size + offset) / 64 + (input.size - offset) / 64 := by
    rw [ByteArray.size_append]
    have := b.offsetBound
    have := b.aligned
    omega
  by_cases hz : (input.size - offset) / 64 = 0
  · refine ⟨u, ⟨b.toBatchFrame, ?_, b.aligned, ?_, ?_⟩⟩
    · simpa only [hz, ite_true] using b.rip
    · have he := absorbedHash_append_short consumed suffix (by rw [halign, hs]; omega)
      rw [hsplit] at he
      simpa only [absorbedStateBytes, he] using b.state
    · rw [hcount, hz, Nat.add_zero]
      exact b.counter
  have hsp := stack_same b.agrees
  have hrip : u.RIP = 0x101d65 := by simpa only [hz, ite_false] using b.rip
  obtain ⟨v, hav, hrv, hcv, hip, ha, hwrite⟩ :=
    Slices.add_counter b.ready b.code h.boundaryOutside hrip (counter_writable h b.agrees)
  obtain ⟨w, haw, hrw, hcw, hiw, hag, hdi, hsi⟩ := prepare_args hrv hcv h.boundaryOutside hip
  have hspv : stackPtr v = stackPtr u := ha.read (n := 64) (r := 4) (by simp)
  have hag' : AgreesExcept (UpdateKind.updateFinalize.changes s) v w :=
    hag.mono (by simp [UpdateKind.changes])
  have hsw : AgreesExcept (UpdateKind.updateFinalize.changes s) s w :=
    ((b.agrees.trans (counter_agrees hsp ha)).trans hag').mono (by simp)
  have hdiw : w.regValue .rdi = UpdateKind.updateFinalize.context s + 72 := by
    rw [hdi, hspv, hsp, register_state_address]
  have hsiw : w.regValue .rsi =
      (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 offset := by
    rw [hsi, ha.read (n := 64) (r := 14) (by simp), b.pointer]
  have hdxw : w.regValue .rdx = BitVec.ofNat 64 ((input.size - offset) / 64) := by
    change (Operand.reg 2 : Operand 64).read w = _
    rw [hag.read (n := 64) (r := 2) (by decide), ha.read (n := 64) (r := 2) (by simp),
      b.blockCount]
  have hkeepMem : w.external = v.external := hag.external (by simp [Component.Covers])
  have hhash := counter_preserves_bytes (base := UpdateKind.updateFinalize.context s)
    (off := 72) (by simpa only [hsp, counter_address] using ha) b.state (by decide) (by decide)
  let blocks := fullBytes suffix
  have hblocks : blocks.size = 64 * ((input.size - offset) / 64) := by
    simp only [blocks, size_fullBytes, hs]
  have hoff : offset + blocks.size ≤ input.size := by
    rw [hblocks]
    have := b.offsetBound
    omega
  have hin : ((Operand.reg 14 : Operand 64).read s).toNat + input.size < 2^32 := h.inputBounded
  have hsrcNat := toNat_add_ofNat ((Operand.reg 14 : Operand 64).read s) offset
    (by have := b.offsetBound; omega)
  have hbytes : (Compress.inputRegion w blocks).HasBytes w.external blocks := by
    have hExtract : blocks = input.extract offset (offset + blocks.size) := by
      rw [hblocks]
      simp only [blocks, fullBytes, Wrapper.Absorb.fullBlocks, hs, suffix,
        ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left (hblocks ▸ hoff)]
    have hb := Update.hasBytes_extract (inputBytes_of_agrees h hsw) offset (offset + blocks.size)
    rw [← hExtract] at hb
    simpa only [Compress.inputRegion, registerRegion, hsiw, hsrcNat,
      UpdateKind.inputRegion, UpdateKind.inputRegister] using hb
  have hdx : 64 * (w.regValue .rdx).toNat = blocks.size := by
    rw [hdxw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hblocks]
  obtain ⟨t, hc⟩ := compress h hsw (stack_same hsw) hrw hcw
    (hsw.directionFlagClear (by simp [UpdateKind.changes, UpdateKind.workRegisters]) ⟨h.df⟩).df
    hiw (.inr rfl) hdiw hdx (.inr ⟨offset, hsiw, hoff, hInputNonzero⟩) hbytes
    (hash := absorbedHash consumed) (by rw [hkeepMem]; exact hhash)
  have hpw : (Operand.reg 14 : Operand 64).read w = (Operand.reg 14 : Operand 64).read u :=
    (hag.read (by decide)).trans (ha.read (by simp))
  have hsizew : (Operand.reg 5 : Operand 64).read w = (Operand.reg 5 : Operand 64).read u :=
    (hag.read (by decide)).trans (ha.read (by simp))
  have htc := compression_agrees hc.agrees
  obtain ⟨fu, hau⟩ := b.advances
  obtain ⟨ft, hat⟩ := hc.advances
  refine ⟨t, ⟨⟨⟨fu + 1 + (1 + 1) + ft, ((hau.trans hav).trans haw).trans hat⟩,
    hc.ready, hc.code, (hsw.trans htc).mono (by simp), b.offsetBound, ?_, ?_⟩,
    hc.rip, b.aligned, ?_, ?_⟩⟩
  · rw [hc.agrees.read (n := 64) (r := 14) (by simp [compressChanges]), hpw, b.pointer]
  · rw [hc.agrees.read (n := 64) (r := 5) (by simp [compressChanges]), hsizew, b.size]
  · have he := absorbedHash_append_blocks consumed suffix halign
    rw [hsplit] at he
    simpa only [absorbedStateBytes, he, blocks] using hc.state
  · rw [counter_preserved h.stackLow h.stackHigh hc.agrees]
    change memLoad w.external _ 64 = _
    rw [hkeepMem]
    rw [hsp, counter_address, b.counter, b.blockCount, ← BitVec.ofNat_add] at hwrite
    rw [hcount]
    exact hwrite

end Sha1.Proofs.Buffered.Update.Slices.Full
