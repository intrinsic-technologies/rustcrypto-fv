import K256.Proofs.Verify.Core.Lincomb.GeneratorPath.State
import K256.Proofs.Verify.Core.Lincomb.Geometry
import K256.Proofs.Verify.Hash.Mark.ZeroFill

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC

abbrev PreservedByFill (b a : Registers) :=
  ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]

theorem fillDigits {fr : Activation} {a x : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s off : Nat} {n : Ram} {ret : BitVec 64} (e : Entry fr a p digest r s)
    (whole : RamWriteFrame fr.original n [fr.region]) (args : FillArguments fr x (slot fr off))
    (bound : off + 265 ≤ 10952) (low : ret.toNat < 2^32)
    (word : memLoad n (workSp fr - 8) 64 = ret) :
    ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l12a700, x, n⟩ = .returned out ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, workSp fr⟩ ∧ PreservedByFill out.values x ∧
      RamWriteFrame n out.store [⟨(slot fr off).toNat, 265⟩] ∧ DigitBytes out.store (slot fr off + 8) [] := by
  have wr := workWrite e whole bound
  have rd := (belowWrite e whole (depth := 8) (by decide)).readable
  have base := workNat e
  have before := belowWorkNat e (depth := 8) (by decide)
  change (workSp fr - 8).toNat = _ at before
  have addr := slotNat e (k := off) (by omega)
  have room := e.stackRoom
  have apart : Outside [ParseSignature.buffer (slot fr off) 265] (workSp fr - 8) 8 := by
    refine ⟨by exact Nat.le_trans rd.low (by decide), fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inl (by change _ ≤ (slot fr off).toNat; omega)
  obtain ⟨out, run, tag, sp, keep, frame, zeros⟩ :=
    Hash.Mark.zeroFill Common.fnCode_subset_programImage args.sp args.count args.zero args.dstReg
      args.df wr ⟨rd.low, rd.present⟩ low word apart
  refine ⟨out, run, tag, sp, ?_, frame, ?_⟩
  · intro ⟨i, hi⟩ live
    apply keep i _ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at live ⊢
    omega
  · intro i
    have hi := i.isLt
    have zero := zeros (8 + i.val) (by change 8 + i.val < 265; omega)
    rw [BitVec.ofNat_add] at zero
    rw [memLoad_8, BitVec.add_assoc]
    exact congrArg UInt8.toBitVec zero

end K256.Proofs.Verify.Core.Lincomb
