import K256.Proofs.Verify.Core.Lincomb.Stack

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)


abbrev workWrites (fr : Activation) (depth off len : Nat) : List MemoryRegion :=
  [scratch (workSp fr) depth, ⟨(slot fr off).toNat, len⟩]

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}
    (e : Entry fr a p digest r s)

include e

theorem workNat : (workSp fr).toNat = fr.rsp.toNat - 10952 := by
  rw [workSp, localSp, BitVec.sub_sub]
  exact ScalarProduct.belowNat e (off := 10952) (by decide)

theorem belowWorkNat {depth : Nat} (small : depth ≤ 1504) :
    (workSp fr - BitVec.ofNat 64 depth).toNat = (workSp fr).toNat - depth := by
  have room := e.stackRoom
  have base := workNat e
  have d : (BitVec.ofNat 64 depth).toNat = depth := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, d]; omega), d]

theorem workWrite {n : Ram} (whole : RamWriteFrame fr.original n [fr.region])
    {k len : Nat} (valid : k + len ≤ 10952) :
    Writable Extracted.programImage n (slot fr k) len := by
  have pos := slotNat e (k := k) (by omega)
  have bottom := e.low_toNat
  have room := e.stackRoom
  exact (e.stack.of_frame whole).sub (by omega) (by omega)

theorem belowWrite {n : Ram} (whole : RamWriteFrame fr.original n [fr.region])
    {depth : Nat} (small : depth ≤ 1504) :
    Writable Extracted.programImage n (workSp fr - BitVec.ofNat 64 depth) depth := by
  have pos := belowWorkNat e small
  have bot := e.low_toNat
  have room := e.stackRoom
  have base := workNat e
  exact (e.stack.of_frame whole).sub (by omega) (by omega)

theorem routineEntry {y : Registers} {n : Ram} {depth : Nat}
    (whole : RamWriteFrame fr.original n [fr.region]) (fits : depth + 8 ≤ 1504)
    (rsp : y[4] = ⟨64,workSp fr - 8⟩)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → y[i].width = 64)
    (df : y[22] = ⟨1,0⟩) (mx : y[39].width = 32) (ft : y[50].width = 16) (fc : y[51].width = 16)
    (low : (memLoad n (workSp fr - 8) 64).toNat < 2^32) :
    RoutineEntry y n (workSp fr - 8) depth := by
  have base := workNat e
  have room := e.stackRoom
  have pos := belowWorkNat e (depth := 8) (by decide)
  change (workSp fr - 8).toNat = _ at pos
  have aligned : fr.rsp.toNat % 16 = 8 := by
    have ent := e.atoms
    simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at ent
    exact ent.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rsp,widths,df,mx,ft,fc,by omega,by omega,?_,
    (belowWrite e whole (depth := 8) (by decide)).readable,low,e.loaded_of_frame whole⟩
  have eq : workSp fr - 8 - BitVec.ofNat 64 depth = workSp fr - BitVec.ofNat 64 (depth+8) := by
    rw [BitVec.ofNat_add]
    bv_omega
  rw [eq]
  exact (belowWrite e whole fits).sub (Nat.le_refl _) (Nat.add_le_add_left (by omega) _)

theorem workWithin {depth off len : Nat} (hd : depth ≤ 1504) (hk : off + len ≤ 0x28e0) :
    RegionsWithin (workWrites fr depth off len) (writes fr) := by
  have base := workNat e
  have bot := e.low_toNat
  have room := e.stackRoom
  have pos := slotNat e (k := off) (by omega)
  have top := ScalarProduct.belowNat e (off := 488) (by decide)
  change (localSp fr).toNat = _ at top
  intro reg hr
  refine ⟨_, List.mem_cons_self .., ?_⟩
  simp only [workWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only [scratch] <;> omega

theorem workOutside {depth off len k size : Nat} (hd : depth ≤ 1504)
    (hk : k + size ≤ 10952) (ho : off + len ≤ 10952) (apart : k + size ≤ off ∨ off + len ≤ k) :
    Outside (workWrites fr depth off len) (slot fr k) size := by
  have base := workNat e
  have pos := slotNat e (k := k) (by omega)
  have dst := slotNat e (k := off) (by omega)
  have room := e.stackRoom
  have high := e.low
  refine ⟨by omega, ?_⟩
  intro reg hr
  simp only [workWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only [scratch] <;> omega

theorem CallerFrame.next {b c d : Registers} {m n t : Ram} (f : CallerFrame fr c b m n)
    {depth off len : Nat} (hd : depth ≤ 1504) (lo : 8 ≤ off) (hi : off + len ≤ 0x28a8)
    (frame : RamWriteFrame n t (workWrites fr depth off len))
    (sp : d[4] = ⟨64, workSp fr⟩)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → d[i].width = 64)
    (fixed : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → d[i] = b[i]) :
    CallerFrame fr c d m t := by
  have same (k : Nat) (hk : k + 8 ≤ 10952) (ha : k + 8 ≤ off ∨ off + len ≤ k) :
      memLoad t (slot fr k) 64 = memLoad n (slot fr k) 64 :=
    frame.memLoad_eq (workOutside e hd hk (by omega) ha)
  refine ⟨sp, widths, fun i h => (fixed i h).trans (f.fixedRegs i h), ?_, ?_,
    (same 0x28d8 (by decide) (by omega)).trans f.ret, f.frame.trans frame (workWithin e hd (by omega))⟩
  · have eq := same 0 (by decide) (by omega)
    simp only [slot, BitVec.add_zero] at eq
    exact eq.trans f.dest
  · intro i
    have h := i.isLt
    rw [same _ (by omega) (by omega)]
    exact f.saved i

end K256.Proofs.Verify.Core.Lincomb
