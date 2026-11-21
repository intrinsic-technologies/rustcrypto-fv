import Hkdf.Proofs.NewExpand.Extract.Update.Copy
import Hkdf.Proofs.NewExpand.Extract.Update.Tail

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copyTail [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray}
    (pre : ExtractPre initial boundary salt ikm) (frame : Frame initial s boundary)
    (path : CopyPath) (rip : s.RIP = path.pc)
    (src : s.regValue path.source = initial.regValue .rcx + BitVec.ofNat 64 (64 * (ikm.size / 64)))
    (len : s.regValue .r14 = BitVec.ofNat 64 (ikm.size % 64))
    (fields : HashFields s (base initial + 120) (salt.getD (RFC5869.defaultSalt .sha256)) ikm) :
    ∃ t, Frame initial t boundary ∧ t.RIP = path.copyPc + (6 : BitVec 64) ∧
      t.regValue .r14 = BitVec.ofNat 64 (ikm.size % 64) ∧
      HashFields t (base initial + 120) (salt.getD (RFC5869.defaultSalt .sha256)) ikm ∧
      (⟨(base initial + 120).toNat,ikm.size % 64⟩ : MemoryRegion).HasBytes t.external
        (SHA256.remainderBytes ikm) ∧
      t.external[base initial + 183]? = s.external[base initial + 183]? := by
  obtain ⟨u, run, ready, ripU, rdi, rsi, rdx, args⟩ := arguments path
    (supportedMachine_readyToStep frame.machine) frame.loaded pre.call.outerBoundary rip
  have noMem : ∀ c ∈ [Component.reg 7,.reg 6,.reg 2,.rip], ∀ a, ¬ c.Covers a := by simp [Component.Covers]
  have frameU := registerFrame pre frame run ready args noMem (by decide) (by decide) (by decide) (by decide)
  have total : 64 * (ikm.size / 64) + ikm.size % 64 = ikm.size := by omega
  obtain ⟨t, frameT, ripT, lenT, copied, writes⟩ := Update.copy pre frameU path ripU
    (rdi.trans (congrArg (· + (120 : BitVec 64)) frame.rsp)) (rsi.trans src) (rdx.trans len)
    (Nat.le_of_eq total) (Nat.mod_lt _ (by decide))
  have bytes (i : Nat) (lo : ikm.size % 64 ≤ i) (hi : i < 144) :
      t.external[base initial + 120 + BitVec.ofNat 64 i]? =
        s.external[base initial + 120 + BitVec.ofNat 64 i]? :=
    (afterCopy pre.call.stack writes i lo hi).trans (by rw [args.external noMem])
  refine ⟨t, frameT, ripT, lenT.trans ((args.read (n := 64) (r := 14) (by decide)).trans len),
    fields.preserved (fun i hi ha => bytes i (by omega) ha), ?_, ?_⟩
  · simpa only [SHA256.remainderBytes, total] using copied
  · simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
      bytes 63 (by omega) (by decide)

end Hkdf.Proofs.NewExpand.Extract.Update
