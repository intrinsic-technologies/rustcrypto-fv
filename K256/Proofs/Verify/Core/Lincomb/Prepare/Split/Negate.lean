import K256.Proofs.Verify.Core.Lincomb.Interface
import K256.Proofs.Verify.Core.Lincomb.Transfer
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.ScalarNeg

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (scalarWords)
open Standards.SECG.DomainParameters.Secp256k1

theorem negateScalar {a : Registers} {m : Ram} {sp dst src : BitVec 64} {x : Nat}
    (entry : RoutineEntry a m sp 48) (widths : ParseSignature.ArgumentWidths a)
    (di : a[7].get 64 = dst) (si : a[6].get 64 = src)
    (read : Readable m src 32) (write : Writable Extracted.programImage m dst 32)
    (srcAbove : sp.toNat + 8 ≤ src.toNat) (dstAbove : sp.toNat + 8 ≤ dst.toNat)
    (apart : dst.toNat + 32 ≤ src.toNat ∨ src.toNat + 32 ≤ dst.toNat)
    (order : a[2].get 64 = 0x2021a0) (bound : x < domain.n)
    (input : WordsAt m src 64 (scalarWords x)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l110b80,a,m⟩,[]⟩ out ∧
      RoutineReturn a m sp 48 [⟨dst.toNat,32⟩] out ∧
      WordsAt out.store dst 64 (scalarWords (if x = 0 then 0 else domain.n - x)) ∧ ParseSignature.ArgumentWidths out.values := by
  let fr : Activation := ⟨m, sp, memLoad m sp 64, sp - 48,
    a[3].get 64, a[5].get 64, a[12].get 64, a[13].get 64, a[14].get 64, a[15].get 64,
    dst, src, a[2].get 64, a[1].get 64, a[8].get 64, a[9].get 64,
    a[39].get 32, a[50].get 16, a[51].get 16, default⟩
  have canon (v : Value) {w : Nat} (eqw : v.width = w) : v = ⟨w,v.get w⟩ := by
    cases v with | mk width bits => subst w; simp [Value.get]
  have gp (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) :=
    canon _ (entry.saved i hi)
  have arg (i : Fin Reg.count) (hi : i.val ∈ Activation.argumentNumbers) :=
    canon _ (widths i hi)
  have base : (sp - 48).toNat = sp.toNat - 48 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr entry.room)
  have atoms : Atom.All Extracted.programImage a m (Generate.LIR.Fn110b80.frameAt .l110b80 fr) := by
    refine ⟨entry.rsp,entry.df,arg 1 (by decide),arg 2 (by decide),
      gp 3 (by decide),gp 5 (by decide),?_,?_,arg 8 (by decide),arg 9 (by decide),
      gp 12 (by decide),gp 13 (by decide),gp 14 (by decide),gp 15 (by decide),
      canon _ entry.mxcsr,canon _ entry.ftw,canon _ entry.fcw,entry.returnSlot,rfl,
      entry.returnLow,entry.stack,?_,entry.aligned,trivial⟩
    · exact (arg 6 (by decide)).trans (congrArg (Value.mk 64) si)
    · exact (arg 7 (by decide)).trans (congrArg (Value.mk 64) di)
    · change (sp - 48).toNat + 48 ≤ sp.toNat
      rw [base]
      have := entry.room
      omega
  obtain ⟨out,run,tag,post,returnedWidths,frame,stored⟩ :=
    Generate.Generator.Multiply.Prepare.scalarNegCall (fr := fr) atoms entry.image
      read write srcAbove dstAbove apart.symm order bound input
  obtain ⟨rsp,df,bx,bp,v12,v13,v14,v15,mx,ft,fc,_⟩ := post
  have shared : (Generate.LIR.Label.l110b80, Label.l110b80) ∈ sharedEntry :=
    .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  refine ⟨out, transfer shared run, ⟨tag,rsp,?_,?_⟩, stored, returnedWidths⟩
  · rintro ⟨i, hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    exact bx.trans (gp 3 (by decide)).symm
    exact bp.trans (gp 5 (by decide)).symm
    exact v12.trans (gp 12 (by decide)).symm
    exact v13.trans (gp 13 (by decide)).symm
    exact v14.trans (gp 14 (by decide)).symm
    exact v15.trans (gp 15 (by decide)).symm
    exact df.trans entry.df.symm
    exact mx.trans (canon _ entry.mxcsr).symm
    exact ft.trans (canon _ entry.ftw).symm
    exact fc.trans (canon _ entry.fcw).symm
  · unfold scratch
    exact frame

end K256.Proofs.Verify.Core.Lincomb.Prepare
