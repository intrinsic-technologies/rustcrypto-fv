import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.LoopStatefulMiddle
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.LoopStatefulTail

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {lengthWritten : Prop}

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 100000 in
theorem decode_loop_step_values [bindings : Bindings]
    {initial s : RamState} {input : List UInt8} {capacity count : Nat}
    {boundary : ReturnBoundary} {high low : UInt8}
    (hvalid : ValidCall (decodeRoutine alphabet) initial input capacity lengthWritten)
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 48#64) (hret : ¬ InProgram boundary.rip)
    (hcount : count < capacity)
    (hrdx : AddrMode.reg64 1 s = AddrMode.reg64 1 initial)
    (hrsi : AddrMode.reg64 0 s = BitVec.ofNat 64 count)
    (halloc : (outputRegion initial capacity).Allocated s.external)
    (hload1 : MemReadable s ((AddrMode.sib 7 (some 0) 1#2 .none).addrAt s 5) 1)
    (hload2 : MemReadable s ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addrAt s 6) 1)
    (hfirst : (Operand.mem ((AddrMode.sib 7 (some 0) 1#2 .none).addrAt s 5) :
      Operand 8).read s = high.toBitVec)
    (hsecond : (Operand.mem ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addrAt s 6) :
      Operand 8).read s = low.toBitVec) :
    ∃ t, Advances boundary 46 s t ∧ EntryReady programImage t ∧
      t.RIP = (if AddrMode.reg64 9 s = BitVec.ofNat 64 count + 1#64
        then (decodeAddress alphabet) + 228#64 else (decodeAddress alphabet) + 48#64) ∧
      AgreesExcept [.reg 0, .reg 3, .reg 5, .reg 6, .reg 8, .reg 10, .reg 11, .flags, .rip,
        .mem (lowerStoreAM.addrAt s 3) 1] s t ∧
      t.external = memStore s.external (lowerStoreAM.addrAt s 3)
        ((decodePair [alphabet] high low).setWidth 8) ∧
      AddrMode.reg64 0 t = BitVec.ofNat 64 (count + 1) ∧
      AddrMode.reg64 6 t = (((Operand.reg 6#5 : Operand 32).read s) |||
        ((decodePair [alphabet] high low).extractLsb' 8 8).setWidth 32).setWidth 64 := by
  obtain ⟨u, hau, hru, hcu, hpu, hfu, h8, h9, h10⟩ :=
    decode_loop_prefix_value hentry hp hload1 hret
  have heu := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hentry hru hcu hfu
  have hmu : u.external = s.external := by
    apply hfu.external
    intro c hc x
    cases c <;> simp_all [Component.Covers]
  have hrdiu : AddrMode.reg64 7 u = AddrMode.reg64 7 s := hfu.read (by decide)
  have hrsiu : AddrMode.reg64 0 u = AddrMode.reg64 0 s := hfu.read (by decide)
  have haddr2 : (AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addrAt u 6 =
      (AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addrAt s 6 := by
    simp only [AddrMode.addrAt, AddrMode.addr, hrdiu, hrsiu]
  have hload2u : MemReadable u ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addrAt u 6) 1 := by
    rw [haddr2]
    exact hload2.of_external_eq hmu
  have hfirstu : (Operand.reg 8#5 : Operand 32).read u = high.toBitVec.setWidth 32 := by
    rw [← hfirst]
    exact h8
  rw [hfirstu] at h9 h10
  obtain ⟨v, hav, hev, hpv, hfv, hv8, hv9⟩ :=
    decode_middle_stateful heu hpu hret hload2u hfirstu h9 h10
  have hfs : AgreesExcept [.reg 8, .reg 10, .reg 11, .reg 3, .flags, .rip] s v := by
    apply (hfu.trans hfv).mono
    intro c hc
    simpa [or_assoc, or_left_comm, or_comm] using hc
  have hmv : v.external = s.external := by
    apply hfs.external
    intro c hc x
    cases c <;> simp_all [Component.Covers]
  have hlow : (Operand.reg 10#5 : Operand 32).read v = low.toBitVec.setWidth 32 := by
    change (Operand.reg 10#5 : Operand 32).read v =
      ((Operand.mem ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addrAt u 6) : Operand 8).read u).setWidth 32 at hv9
    rw [haddr2] at hv9
    simp only [Operand.read, hmu] at hv9
    change (Operand.reg 10#5 : Operand 32).read v =
      ((Operand.mem ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addrAt s 6) : Operand 8).read s).setWidth 32 at hv9
    simpa only [hsecond] using hv9
  have hdx : AddrMode.reg64 1 v = AddrMode.reg64 1 s := hfs.read (by decide)
  have hsi : AddrMode.reg64 0 v = AddrMode.reg64 0 s := hfs.read (by decide)
  have hax : AddrMode.reg64 9 v = AddrMode.reg64 9 s := hfs.read (by decide)
  have hcx : (Operand.reg 6#5 : Operand 32).read v =
      (Operand.reg 6#5 : Operand 32).read s := hfs.read (by decide)
  have hallocv : (outputRegion initial capacity).Allocated v.external := hmv ▸ halloc
  obtain ⟨t, hat, het, hpt, hft, hmt, hsit, hcxt⟩ := decode_tail_concrete hvalid hev hpv hret
    hcount (hdx.trans hrdx) (hsi.trans hrsi) hallocv hv8 hlow
  have haddr : lowerStoreAM.addrAt v 3 = lowerStoreAM.addrAt s 3 := by
    simp only [lowerStoreAM, AddrMode.addrAt, AddrMode.addr, hdx, hsi]
  have hframe : AgreesExcept
      [.reg 0, .reg 3, .reg 5, .reg 6, .reg 8, .reg 10, .reg 11, .flags, .rip,
        .mem (lowerStoreAM.addrAt s 3) 1] s t := by
    rw [haddr] at hft
    apply (hfs.trans hft).mono
    intro c hc
    simpa [or_assoc, or_left_comm, or_comm] using hc
  refine ⟨t, (hau.trans hav).trans hat, het, ?_, hframe, ?_, hsit, ?_⟩
  · simpa only [hax] using hpt
  · simpa only [hmv, haddr] using hmt
  · simpa only [hcx] using hcxt

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
