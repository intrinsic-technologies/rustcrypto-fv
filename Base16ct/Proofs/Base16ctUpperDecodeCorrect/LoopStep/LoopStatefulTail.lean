import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.LoopTailStore
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {lengthWritten : Prop}

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 100000 in
theorem decode_tail_concrete [bindings : Bindings] {initial s : RamState}
    {input : List UInt8} {capacity count : Nat} {boundary : ReturnBoundary} {high low : UInt8}
    (hvalid : ValidCall (decodeRoutine alphabet) initial input capacity lengthWritten)
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 138#64) (hret : ¬ InProgram boundary.rip)
    (hcount : count < capacity)
    (hrdx : AddrMode.reg64 1 s = AddrMode.reg64 1 initial)
    (hrsi : AddrMode.reg64 0 s = BitVec.ofNat 64 count)
    (halloc : (outputRegion initial capacity).Allocated s.external)
    (hhigh : (Operand.reg 8#5 : Operand 32).read s = decodeHighNibble [alphabet] high)
    (hlow : (Operand.reg 10#5 : Operand 32).read s = low.toBitVec.setWidth 32) :
    ∃ t, Advances boundary 25 s t ∧ EntryReady programImage t ∧
      t.RIP = (if AddrMode.reg64 9 s = BitVec.ofNat 64 count + 1#64
        then (decodeAddress alphabet) + 228#64 else (decodeAddress alphabet) + 48#64) ∧
      AgreesExcept [.reg 0, .reg 3, .reg 5, .reg 6, .reg 10, .reg 11, .flags, .rip,
        .mem (lowerStoreAM.addrAt s 3) 1] s t ∧
      t.external = memStore s.external (lowerStoreAM.addrAt s 3)
        ((decodePair [alphabet] high low).setWidth 8) ∧
      AddrMode.reg64 0 t = BitVec.ofNat 64 (count + 1) ∧
      AddrMode.reg64 6 t = (((Operand.reg 6#5 : Operand 32).read s) |||
        ((decodePair [alphabet] high low).extractLsb' 8 8).setWidth 32).setWidth 64 := by
  obtain ⟨u, hau, hu, hpu, hfu, hvu⟩ := decode_tail_value hentry hp hret hhigh hlow
  have hdx : AddrMode.reg64 1 u = AddrMode.reg64 1 s := hfu.read (by decide)
  have hsi : AddrMode.reg64 0 u = AddrMode.reg64 0 s := hfu.read (by decide)
  have hax : AddrMode.reg64 9 u = AddrMode.reg64 9 s := hfu.read (by decide)
  have hcx : (Operand.reg 6#5 : Operand 32).read u =
      (Operand.reg 6#5 : Operand 32).read s := hfu.read (by decide)
  have hm : u.external = s.external := by
    apply hfu.external
    intro c hc x
    cases c <;> simp_all [Component.Covers]
  have hal : (outputRegion initial capacity).Allocated u.external := hm ▸ halloc
  have hpre := decode_storePre_from_call hvalid hpu (hdx.trans hrdx) (hsi.trans hrsi) hal hcount
    (by intro j; cases alphabet <;> finite_cases j <;> first
      | exact ⟨0x88, by decide +kernel⟩
      | exact ⟨0x1c, by decide +kernel⟩
      | exact ⟨0x01, by decide +kernel⟩)
  have hav := decode_storeAvoid_from_call (p := decodeAddress alphabet + 208#64) hvalid (hdx.trans hrdx) (hsi.trans hrsi) hcount
  obtain ⟨t, hat, ht, hpt, hft, hmt, hsit, hcxt⟩ :=
    decode_tail_store hu hpre hret hav hvu
  have haddr : lowerStoreAM.addrAt u 3 = lowerStoreAM.addrAt s 3 := by
    simp only [lowerStoreAM, AddrMode.addrAt, AddrMode.addr, Disp.value]
    rw [hdx, hsi]
  have hf : AgreesExcept
      [.reg 0, .reg 3, .reg 5, .reg 6, .reg 10, .reg 11, .flags, .rip,
        .mem (lowerStoreAM.addrAt s 3) 1] s t := by
    rw [haddr] at hft
    apply (hfu.trans hft).mono
    intro c hc
    simpa [or_assoc, or_left_comm, or_comm] using hc
  refine ⟨t, hau.trans hat, ht, ?_, hf, ?_, ?_, ?_⟩
  · simpa only [hax, hsi, hrsi] using hpt
  · simpa only [hm, haddr] using hmt
  · rw [hsi, hrsi] at hsit
    simpa only [BitVec.ofNat_add] using hsit
  · simpa only [hcx] using hcxt

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
