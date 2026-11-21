import K256.Proofs.Ecdh.Decode.Convert.Barrier
import K256.Proofs.Ecdh.Decode.Convert.State
import K256.Proofs.Ecdh.LIR.Fn10fa10.Frame

namespace K256.Proofs.Ecdh.Decode.Convert

open X86.Machine X86.UserProcess X86Proofs K256.Spec.Program K256.Proofs.CFG
open K256.Proofs.Refine K256.Proofs.Lift Ecdh.LIR

theorem afterBarrier {fr : Activation} {a b : Values Value Reg.count} {m : Ram}
    (entry : Atom.All Extracted.programImage a fr.original (Fn10fa10.frameAt .l10fa10 fr))
    (flag : b[7].get 8 = inputFlag fr) (sp : b[4] = ⟨64, fr.rsp - 96⟩)
    (bx : b[3] = ⟨64, fr.rdi⟩) (coords : coordinates fr b m)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i])
    (widths : ParseSignature.ArgumentWidths b) (writes : RamWriteFrame fr.original m [fr.region])
    (ret : memLoad m (fr.rsp - 96) 64 = 0x10fa68)
    (saved : ∀ k r : Nat, (k,r) ∈ [(48,3),(40,12),(32,13),(24,14),(16,15),(8,5)] →
      memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r) :
    ∃ o, program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,b,m⟩, []⟩ o ∧
      o.tag = some ⟨64,0x10fa68⟩ ∧
      Atom.All Extracted.programImage o.values o.store (Fn10fa10.frameAt .l10fa68 fr) ∧
      coordinates fr o.values o.store ∧ o.values[0].get 8 = inputFlag fr ∧
      ParseSignature.ArgumentWidths o.values ∧ RamWriteFrame fr.original o.store [fr.region] := by
  simp only [Fn10fa10.frameAt, Fn10fa10.frameAtG1, Atom.All, Atom.Holds] at entry
  obtain ⟨_,df,_,_,_,_,_,_,_,_,_,_,_,_,mx,ft,fc,rd,hr,retLow,wr,room,align,_⟩ := entry
  have window := wr.of_frame writes
  have addr (k : Nat) (hk : k ≤ 97) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have kn : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, kn]; omega), kn]
  have low := rd.low
  have slot : Readable m (fr.rsp - 96) 8 :=
    window.readable.of_offsets (addr_sub fr.rsp 96) (addr_sub fr.rsp 97) (by decide)
  have pos : fr.rsp - 96 - 1 = fr.rsp - 97 := by bv_omega
  have byte : Writable Extracted.programImage m (fr.rsp - 96 - 1) 1 := by
    rw [pos]
    exact window.sub (Nat.le_refl _) (by omega)
  obtain ⟨o,exec,tag,os,oflag,frame,kept⟩ := convertBarrier (sp := fr.rsp - 96) (congrArg (Value.get 64) sp)
    byte slot ret (by decide)
  have base : (fr.rsp - 97).toNat = fr.rsp.toNat - 97 := addr 97 (by decide)
  have slotBase : (fr.rsp - 88).toNat = fr.rsp.toNat - 88 := addr 88 (by decide)
  rw [pos] at frame
  have whole : RamWriteFrame fr.original o.store [fr.region] := writes.trans frame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_,?_⟩
    · change fr.low.toNat ≤ (fr.rsp - 97).toNat
      rw [base]
      omega
    · change (fr.rsp - 97).toNat + 1 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      rw [base]
      omega)
  have saved' (k r : Nat) (hk : k ≤ 88) (hr : (k,r) ∈ [(48,3),(40,12),(32,13),(24,14),(16,15),(8,5)]) :
      memLoad o.store (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r := by
    rw [frame.memLoad_eq, saved k r hr]
    refine ⟨?_, fun reg hreg => ?_⟩
    · rw [addr k (by omega)]
      change _ + 8 ≤ 2^64
      omega
    · obtain rfl := List.mem_singleton.mp hreg
      right
      change (fr.rsp - 97).toNat + 1 ≤ _
      rw [base, addr k (by omega)]
      omega
  refine ⟨o,exec,tag,?_,?_,?_,?_,whole⟩
  · simp only [Fn10fa10.frameAt, Fn10fa10.frameAtG1, Atom.All, Atom.Holds]
    rw [show fr.rsp - 96 + 8 = fr.rsp - 88 by bv_omega] at os
    refine ⟨os,(kept _ (by decide)).trans ((keep _ (by decide)).trans df),
      (kept _ (by decide)).trans bx,(kept _ (by decide)).trans ((keep _ (by decide)).trans mx),
      (kept _ (by decide)).trans ((keep _ (by decide)).trans ft),
      (kept _ (by decide)).trans ((keep _ (by decide)).trans fc),
      saved' 48 3 (by decide) (by decide), saved' 40 12 (by decide) (by decide),
      saved' 32 13 (by decide) (by decide), saved' 24 14 (by decide) (by decide),
      saved' 16 15 (by decide) (by decide), saved' 8 5 (by decide) (by decide),
      rd.of_frame whole,?_,retLow,wr.of_frame whole,room,align,trivial⟩
    rw [whole.memLoad_eq, hr]
    refine ⟨by change _ + 8 ≤ 2^64; omega, fun reg hreg => ?_⟩
    obtain rfl := List.mem_singleton.mp hreg
    right
    change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ fr.rsp.toNat
    omega
  · obtain ⟨r13,bp,r14,r15,r12,ys⟩ := coords
    refine ⟨(kept 13 (by decide)).trans r13,(kept 5 (by decide)).trans bp,
      (kept 14 (by decide)).trans r14,(kept 15 (by decide)).trans r15,(kept 12 (by decide)).trans r12,?_⟩
    intro i hi
    rw [frame.memLoad_eq, ys i hi]
    have hn : (BitVec.ofNat 64 (8*i)).toNat = 8*i := Nat.mod_eq_of_lt (by omega)
    have idx : (wordAddr (fr.rsp - 88) 64 i).toNat = fr.rsp.toNat - 88 + 8*i := by
      simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, hn, slotBase]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨by rw [idx]; change _ + 8 ≤ 2^64; omega, fun reg hreg => ?_⟩
    obtain rfl := List.mem_singleton.mp hreg
    right
    change (fr.rsp - 97).toNat + 1 ≤ _
    rw [base, idx]
    omega
  · rw [oflag]
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_eq] using flag
  · intro i hi
    rw [kept i (by
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega)]
    exact widths i hi

end K256.Proofs.Ecdh.Decode.Convert
