import K256.Proofs.Sec1.Affine.Frame
import K256.Proofs.Sec1.Buffers

namespace K256.Proofs.Sec1.Affine

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common
open Standards.SECG.ECC

structure CoordinateMemory (s : RamState) (bytes : ByteArray) (mem : Ram) : Prop where
  stack : Writable Extracted.programImage mem ((activation s).rsp - 136 - 8 - 1048) 1048
  slot : Readable mem ((activation s).rsp - 136 - 8) 8
  output : Writable Extracted.programImage mem ((activation s).rsp - 136) 89
  input : Readable mem ((activation s).rsi + 1) 64
  image : ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2
  room : 1048 ≤ ((activation s).rsp - 136 - 8).toNat
  aligned : ((activation s).rsp - 136 - 8).toNat % 16 = 8
  above : ((activation s).rsp - 136).toNat + 89 ≤ ((activation s).rsi + 1).toNat
  stackEnd : ((activation s).rsp - 136 - 8 - 1048).toNat + 1056 = ((activation s).rsp - 136).toNat
  words : ∀ off : Nat, off + 32 ≤ bytes.size →
    let word := scalarWord mem ((activation s).rsi + BitVec.ofNat 64 off)
    Encoding.octetsToNat (bytes.extract off (off+32)) =
      ((word 3).toNat * 2^64 + (word 2).toNat) * 2^128 + (word 1).toNat * 2^64 + (word 0).toNat

theorem coordinateMemory_of_packing {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count}
    {m written : Ram} (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (e : EntryAt s bytes args m)
    (size : bytes.size ≤ 65)
    (frame : RamWriteFrame m written [⟨((activation s).rsp - 145).toNat,145⟩]) :
    CoordinateMemory s bytes written := by
  let fr := activation s
  let sp := s.regValue .rsp
  have rsp : fr.rsp = sp - 608 := by
    change sp - 600 - 8 = sp - 608
    simp only [BitVec.sub_sub, BitVec.reduceAdd]
    rfl
  have scratch : fr.rsp - 145 = sp - 753 := by
    simp only [rsp, BitVec.sub_sub, BitVec.reduceAdd]
    rfl
  have bottom : fr.rsp - 136 - 8 - 1048 = sp - 1800 := by
    simp only [rsp, BitVec.sub_sub, BitVec.reduceAdd]
    rfl
  have slot : fr.rsp - 136 - 8 = sp - 752 := by
    simp only [rsp, BitVec.sub_sub, BitVec.reduceAdd]
    rfl
  have output : fr.rsp - 136 = sp - 744 := by
    simp only [rsp, BitVec.sub_sub, BitVec.reduceAdd]
    rfl
  have source : fr.rsi = sp - 596 := by
    change sp - 600 + 4 = sp - 596
    rw [show (600 : BitVec 64) = 596 + 4 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have input : fr.rsi + 1 = sp - 595 := by
    rw [source, show (596 : BitVec 64) = 595 + 1 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have room : 1928 ≤ sp.toNat := call.stackAvailable.2.2.1
  have align : sp.toNat % 16 = 8 := call.stackAvailable.2.2.2
  have offset (n : BitVec 64) (hn : n.toNat ≤ 1928) :
      (sp - n).toNat = sp.toNat - n.toNat := rootStackOffset call n hn
  have full := (e.stackFrame call).trans frame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨r, hr, within⟩ := Parser.stackRange (off := 753) (n := 145) call
      (by decide) (by decide)
    refine ⟨r, hr, ?_, ?_⟩
    · change r.start ≤ (fr.rsp - 145).toNat
      rw [scratch]
      exact within.1
    · change (fr.rsp - 145).toNat + 145 ≤ r.start + r.size
      rw [scratch]
      exact within.2.1)
  have writable (n k : Nat) (depth : n ≤ 1928) (fits : k ≤ n + 8) (pos : 0 < k) :
      Writable Extracted.programImage written (sp - BitVec.ofNat 64 n) k :=
    (Wrapper.stackWritable call depth fits pos).of_frame full
  have padded : Readable written fr.rsi 65 := by
    rw [source]
    exact (writable 596 65 (by decide) (by decide) (by decide)).readable
  have sourceLow := padded.low
  have packed : (⟨fr.rsi.toNat, bytes.size⟩ : MemoryRegion).HasBytes written bytes := by
    refine ⟨rfl, fun i => ?_⟩
    have hi : i.val < 65 := Nat.lt_of_lt_of_le i.isLt size
    let addr := fr.rsi + BitVec.ofNat 64 i.val
    have addrNat : addr.toNat = fr.rsi.toNat + i.val := by
      dsimp only [addr]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := i.val) (by omega), Nat.mod_eq_of_lt (by omega)]
    have preserved : Outside [⟨(fr.rsp - 145).toNat, 145⟩] addr 1 := by
      refine ⟨by rw [addrNat]; omega, ?_⟩
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      right
      change (fr.rsp - 145).toNat + 145 ≤ addr.toNat
      rw [addrNat, scratch, source, offset 753 (by decide), offset 596 (by decide)]
      change sp.toNat - 753 + 145 ≤ sp.toNat - 596 + i.val
      omega
    have content := e.input i.val hi
    change memByte m addr = bytes.data[i.val]?.getD 0 at content
    have present : (written[addr]?).isSome := padded.present i.val hi
    change written[BitVec.ofNat 64 (fr.rsi.toNat + i.val)]? = some bytes[i.val]
    rw [K256.Proofs.ofNat_toNat_add]
    change written[addr]? = _
    change (m[addr]?).getD 0 = _ at content
    rw [← frame.outside addr preserved] at content
    have hi' : i.val < bytes.data.size := i.isLt
    rw [Array.getElem?_eq_getElem hi', Option.getD_some,
      ← ByteArray.getElem_eq_getElem_data] at content
    rw [← content]
    exact (Option.getD_of_ne_none (Option.ne_none_iff_isSome.mpr present) 0).symm
  refine ⟨?_, ?_, ?_, ?_, (Parser.inputs_of_stackFrame call full).2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bottom]
    exact writable 1800 1048 (by decide) (by decide) (by decide)
  · rw [slot]
    exact (writable 752 8 (by decide) (by decide) (by decide)).readable
  · rw [output]
    exact writable 744 89 (by decide) (by decide) (by decide)
  · rw [input]
    exact (writable 595 64 (by decide) (by decide) (by decide)).readable
  · rw [slot, offset 752 (by decide)]
    change 1048 ≤ sp.toNat - 752
    omega
  · rw [slot, offset 752 (by decide)]
    change (sp.toNat - 752) % 16 = 8
    omega
  · rw [output, input, offset 744 (by decide), offset 595 (by decide)]
    change sp.toNat - 744 + 89 ≤ sp.toNat - 595
    omega
  · rw [bottom, output, offset 1800 (by decide), offset 744 (by decide)]
    change sp.toNat - 1800 + 1056 = sp.toNat - 744
    omega
  · intro off h
    simpa only [K256.Proofs.ofNat_toNat_add] using octetsToNat_extract_eq_words packed h

end K256.Proofs.Sec1.Affine
