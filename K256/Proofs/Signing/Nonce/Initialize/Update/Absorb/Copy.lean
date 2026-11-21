import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Frame
import K256.Proofs.Verify.Core.Lincomb.CopyCall

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

theorem spNat {fr : Activation} {input : Input} (env : Environment fr input) :
    (sp fr).toNat = fr.rsp.toNat - 712 := by
  have dep := env.depth
  exact BitVec.toNat_sub_of_le (show (712 : BitVec 64) ≤ fr.rsp from (by change 712 ≤ fr.rsp.toNat; omega))

theorem spAddNat {fr : Activation} {input : Input} (env : Environment fr input)
    (off : Nat) (bound : off ≤ 712) :
    (sp fr + BitVec.ofNat 64 off).toNat = (sp fr).toNat + off := by
  have base := spNat env
  have lim := env.limit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 4096 in
theorem stackWritable {fr : Activation} {input : Input} {m : Ram} {rs : List MemoryRegion}
    (env : Environment fr input) (written : RamWriteFrame fr.original m rs)
    {p : BitVec 64} {n : Nat} (lo : fr.low.toNat ≤ p.toNat) (hi : p.toNat + n ≤ fr.rsp.toNat) :
    Writable Extracted.programImage m p n := by
  have dep := env.depth
  have base := BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)
  change (fr.rsp - 1920).toNat = fr.rsp.toNat - 1920 at base
  rw [env.low,base] at lo
  apply (env.stack.of_frame written).sub
  · change (fr.rsp - 1920).toNat ≤ p.toNat; rw [base]; exact lo
  · rw [base]; omega

abbrev copyRegions (sp dst : BitVec 64) (len : Nat) : List MemoryRegion :=
  [⟨(sp - 8).toNat,8⟩, ⟨dst.toNat,len⟩]

theorem copyCall {fr : Activation} {input : Input} {caller m : Ram} {a c : Verify.Core.Registers}
    {site after : Label} {ret src : BitVec 64} {off len : Nat} {rs : List MemoryRegion}
    (env : Environment fr input) (written : RamWriteFrame fr.original m rs)
    (fits : off + len ≤ 664) (small : ret.toNat < 2^32)
    (called : program.runBlock (dialect Extracted.programImage) ⟨site,a,caller⟩ =
      .call ⟨.l12a820,c,memStore m (sp fr - 8) ret⟩ (Verify.Core.Lincomb.callResume after ret))
    (rsp : c[4].get 64 = sp fr - 8) (di : c[7].get 64 = sp fr + BitVec.ofNat 64 off)
    (si : c[6].get 64 = src) (dx : c[2].get 64 = BitVec.ofNat 64 len) (df : c[22].get 1 = 0)
    (source : Readable m src len) (separate : src.toNat + len ≤ (sp fr).toNat + off ∨
      (sp fr).toNat + off + len ≤ src.toNat) :
    let dst := sp fr + BitVec.ofNat 64 off
    let n := memCopy (memStore m (sp fr - 8) ret) dst src len
    ∃ b, Verify.Core.Reaches site a caller after b n ∧ b[4] = ⟨64, sp fr⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,9,10,11,12,13,14,15,22,39,50,51] → b[i] = c[i]) ∧
      RamWriteFrame m n (copyRegions (sp fr) dst len) := by
  dsimp only
  let dst := sp fr + BitVec.ofNat 64 off
  let slot := sp fr - 8
  have dep := env.depth
  have limit := env.limit
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)]
    rfl
  have base := spNat env
  have dest : dst.toNat = (sp fr).toNat + off := spAddNat env off (by omega)
  have slotAddr : slot.toNat = (sp fr).toNat - 8 := BitVec.toNat_sub_of_le
    (show (8 : BitVec 64) ≤ sp fr from (by change 8 ≤ (sp fr).toNat; omega))
  have wdst : Writable Extracted.programImage m dst len := stackWritable env written (by omega) (by omega)
  have wslot : Writable Extracted.programImage m slot 8 := stackWritable env written (by omega) (by omega)
  have tag : memLoad (memStore m slot ret) slot 64 = ret := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have size : (BitVec.ofNat 64 len).toNat = len := Nat.mod_eq_of_lt (by omega)
  have distinct : RangeApart dst len slot 8 := by
    intro i hi j hj eq
    have h := congrArg BitVec.toNat eq
    rw [toNat_add_ofNat dst i (by omega),toNat_add_ofNat slot j (by omega)] at h
    omega
  obtain ⟨out, run, mem, returned, _, back, kept⟩ := Verify.Hash.Update.memcpy di si dx rsp df
    (by rw [size]; exact source.memStore slot ret) (by rw [size]; exact wdst.memStore slot ret)
    (by rw [size]; exact dest ▸ separate) (by rw [size]; exact distinct)
    (wslot.readable.memStore slot ret) (by rw [tag]; exact small)
  have mem' : out.store = memCopy (memStore m slot ret) dst src len := by simpa only [size] using mem
  have reached := Verify.Core.Lincomb.reachesCall called run (returned.trans (congrArg (fun x => some (Value.mk 64 x)) tag))
  refine ⟨out.values, mem' ▸ reached, back.trans (by rw [BitVec.sub_add_cancel]), kept, ?_⟩
  have push : RamWriteFrame m (memStore m slot ret) (copyRegions (sp fr) dst len) := by
    apply (RamWriteFrame.refl _ _).memStore
    exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _,by change slot.toNat + 8 ≤ 2^64; omega⟩
  apply Sec1.Wrapper.Copy.memCopy_frame push
  exact ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),Nat.le_refl _,Nat.le_refl _,by change dst.toNat + len ≤ 2^64; omega⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb
