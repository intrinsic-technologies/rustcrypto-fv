import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Bulk
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Filled

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem longInput [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info previous : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (positive : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (hmac : HmacAt s (stackPtr s + 272) key previous)
    (pc : s.RIP = if previous.size % 64 = 0 then 0x10f7f5 else 0x10f74b)
    (src : s.regValue .rbx = ptr) (len : s.regValue .rbp = BitVec.ofNat 64 info.size)
    (index : s.regValue .r14 = BitVec.ofNat 64 (previous.size % 64))
    (room : s.regValue .rdx = BitVec.ofNat 64 (64 - previous.size % 64))
    (remaining : s.regValue .r15 = BitVec.ofNat 64 (info.size - (64 - previous.size % 64)))
    (fits : 64 - previous.size % 64 ≤ info.size) (memcpy : s.regValue .r12 = 0x10dd60) :
    ∃ t, SavedFrame entry t boundary length ∧ (∃ fuel, Advances boundary fuel s t) ∧
      t.RIP = 0x10f7de ∧ t.regValue .r12 = s.regValue .r12 ∧ t.regValue .r13 = s.regValue .r13 ∧
      MemoryWriteFrame s t (longRegions s) ∧ HmacAt t (stackPtr t + 272) key (previous ++ info) := by
  by_cases aligned : previous.size % 64 = 0
  · have bound := pre.lengthFits
    have val : (s.regValue .rbp).toNat = info.size := by
      rw [len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    have enough : 64 ≤ info.size := by omega
    obtain ⟨fu, u, runU, readyU, effect⟩ := alignedDispatch
      (supportedMachine_readyToStep saved.machine) saved.loaded pre.call.outerBoundary
      (by simpa only [aligned, ↓reduceIte] using pc) (by omega)
    have ag : AgreesExcept [.reg 15,.reg 2,.flags,.rip] s u := effect.agrees
    have empty : ∀ c ∈ ([.reg 15,.reg 2,.flags,.rip] : List Component), ∀ a, ¬ c.Covers a := by
      simp [Component.Covers]
    have frameU : MemoryWriteFrame s u (longRegions s) := ag.memoryWriteFrame
      (fun c hc a ha ↦ (empty c hc a ha).elim)
    have savedU := savedOfLocal pre positive limit saved runU readyU ag
      (fun c hc a ha ↦ (empty c hc a ha).elim) (by decide)
    have sp : stackPtr u = stackPtr s := ag.read (n := 64) (r := 4) (by decide)
    have hmacU : HmacAt u (stackPtr u + 272) key previous := by
      rw [sp]
      exact hmac.of_copy (fun i _ ↦ ag.byte (fun c hc ↦ empty c hc _))
    have regs : u.regValue .r15 = s.regValue .rbp ∧ u.regValue .rdx = s.regValue .rbp >>> 6 := effect.writes
    have count : u.regValue .rdx = BitVec.ofNat 64 (info.size / 64) := by
      rw [regs.2, len]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt bound]
      omega
    obtain ⟨t, savedT, ⟨ft, runT⟩, pcT, copyT, tableT, frameT, hmacT⟩ := bulkInfoBlocks
      (offset := 0) pre positive limit savedU hmacU aligned (Nat.zero_le _) (by
        simpa only [Nat.sub_zero, ite_eq_right (show info.size / 64 ≠ 0 by omega)] using (show u.RIP = 0x10f796 from effect.rip))
      (by
        rw [show ptr + BitVec.ofNat 64 0 = ptr from BitVec.add_zero _]
        exact (ag.read (n := 64) (r := 3) (by decide)).trans src)
      (by simpa only [Nat.sub_zero] using regs.1.trans len)
      (by simpa only [Nat.sub_zero] using count)
      ((ag.read (n := 64) (r := 12) (by decide)).trans memcpy)
    refine ⟨t, savedT, ⟨fu+ft,runU.trans runT⟩, pcT, copyT.trans (ag.read (n := 64) (r := 12) (by decide)),
      tableT.trans (ag.read (n := 64) (r := 13) (by decide)), memoryWriteFrame_trans frameU ?_, ?_⟩
    · simpa only [longRegions, sp] using frameT
    · simpa only [ByteArray.extract_zero_size] using hmacT
  · let consumed := 64 - previous.size % 64
    have size : (info.extract 0 consumed).size = consumed := by
      rw [ByteArray.size_extract]
      dsimp only [consumed]
      omega
    obtain ⟨u, savedU, ⟨fu,runU⟩, pcU, hmacU, srcU, lenU, countU, copyU, tableU, frameU⟩ :=
      fillInfoBlock pre positive limit saved (by simpa only [ite_eq_right aligned] using pc)
        hmac src index room remaining fits memcpy
    obtain ⟨t, savedT, ⟨ft,runT⟩, pcT, copyT, tableT, frameT, hmacT⟩ := bulkInfoBlocks
      (offset := consumed) pre positive limit savedU hmacU (by
        rw [ByteArray.size_append, size]
        dsimp only [consumed]
        omega) fits pcU srcU lenU countU (copyU.trans memcpy)
    have sp : stackPtr u = stackPtr s := savedU.sp.trans saved.sp.symm
    refine ⟨t, savedT, ⟨fu+ft,runU.trans runT⟩, pcT, copyT.trans copyU, tableT.trans tableU,
      memoryWriteFrame_trans frameU ?_, ?_⟩
    · simpa only [longRegions, sp] using frameT
    · simpa only [consumed, ByteArray.append_assoc, ByteArray.extract_append_extract, Nat.zero_min,
        Nat.max_eq_right fits, ByteArray.extract_zero_size] using hmacT

end Hkdf.Proofs.NewExpand.Expand.Info
