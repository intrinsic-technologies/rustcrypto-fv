import K256.Proofs.Generate.Generator.Multiply.Add
import K256.Proofs.Verify.Core.Lincomb.Loop.Select
import K256.Proofs.Verify.Core.Lincomb.Loop.Step.Add
import K256.Proofs.Verify.Core.Lincomb.Loop.Step.Lookup
import K256.Proofs.Verify.Core.Lincomb.Loop.Step.Memory
import K256.Proofs.Verify.Core.Lincomb.Loop.Step.Operand
import K256.Proofs.Verify.Core.Lincomb.Loop.Step.Reload

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Curve

theorem applyDigit {a b : Registers} {m n : Ram} {sp dst table : BitVec 64}
    {p value : Curve.Point} {u v k : Nat} (j : Fin 4) (entry : RoutineEntry a m sp 0x478)
    (hu : u < domain.n) (hv : v < domain.n) (hp : Curve.onCurve domain p)
    (read : Readable m table 0x1340) (apart : Outside [scratch sp 0x478, ⟨dst.toNat, 120⟩] table 0x1340)
    (generator : Prepared m table (table + 0x780) domain.G u)
    (peer : Prepared m (table + 0x9a0) (table + 0x1120) p v) (bound : k < 129)
    (state : Column a m sp dst table k value b n) (cursor : Cursor sp table j (j.val%2) b n) :
    ∃ c store, Reaches .l11034e b n .l11037b c store ∧
      Column a m sp dst table k (Curve.add domain value
        (selectDigit (combinationBases p u v j) ((Naf.digits (combinationScalars u v j))[k]?.getD 0))) c store ∧
      Cursor sp table j (j.val%2+1) c store := by
  let d := ((Naf.digits (combinationScalars u v j))[k]?).getD 0
  change ∃ c store, Reaches .l11034e b n .l11037b c store ∧
    Column a m sp dst table k (Curve.add domain value (selectDigit (combinationBases p u v j) d)) c store ∧
    Cursor sp table j (j.val%2+1) c store
  obtain ⟨digit, valid, operand⟩ := columnOperand j hu hv hp apart state.frame generator peer bound
  have workspace : Writable Extracted.programImage n (baseSp sp) 0x1a8 :=
    (entry.stack.of_frame state.frame).of_offsets (x := sp) (c := -0x1d8) (d := -0x478)
      (by unfold baseSp; bv_omega) (by bv_omega) (by decide)
  have header : LoadOk n (baseSp sp + 24) 8 := LoadOk.of_offsets workspace.readable (x := baseSp sp)
    (c := 24) (d := 0) rfl (BitVec.add_zero _).symm (by decide)
  obtain ⟨s, path, col, cur, src, byte, wide, widths⟩ := lookupDigit (d := d) j state cursor header
    (lookupLoad (read.of_frame state.frame) j bound) digit valid
  by_cases zero : d = 0
  · rw [ite_eq_left zero] at path
    have val : Curve.add domain value (selectDigit (combinationBases p u v j) d) = value := by
      rw [zero]
      cases value <;> rfl
    rw [val]
    exact ⟨s,n,path,col,cur⟩
  · rw [ite_eq_right zero] at path
    obtain ⟨q,qv,qs,eq⟩ := operand zero
    have index : d.natAbs/2 < 8 := by
      have ⟨_,lo,hi⟩ := valid.resolve_left zero
      omega
    obtain ⟨rd,sep⟩ := packMemory entry state.frame read apart j (d.natAbs/2) index
    obtain ⟨t,mem,pack,packed⟩ := packDigit valid zero index byte (congrArg (Value.get 64) col.rsp) src
      (congrArg (Value.get 1) ((col.control 22 (by decide)).trans entry.df)) widths workspace rd sep qs
    obtain ⟨left,ls,lv,lval⟩ := col.point
    obtain ⟨c,store,addPath,rsp,keep,stored,frame⟩ := packedAdd entry col cur packed ls wide
    have signedValid : (if d < 0 then q.neg else q).valid := by
      split
      · exact q.neg_valid qv
      · exact qv
    have correct := left.add_correct _ lv signedValid
    obtain ⟨b',n',reload,post,cursor'⟩ := reloadDigit entry col cur rsp keep stored correct.1 frame
    rw [correct.2,lval,eq] at post
    exact ⟨b',n',path.trans (pack.trans (addPath.trans reload)),post,cursor'⟩

end K256.Proofs.Verify.Core.Lincomb.Loop
