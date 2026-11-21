import K256.Proofs.Verify.Core.Lincomb.Interface
import K256.Proofs.Verify.Core.Lincomb.Transfer
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Call

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (Projective)

theorem add {a : Registers} {m : Ram} {sp dst src : BitVec 64} {p q : Projective}
    (entry : RoutineEntry a m sp 0x218) (widths : ParseSignature.ArgumentWidths a)
    (di : a[7].get 64 = dst) (si : a[6].get 64 = src)
    (read : Readable m src 120) (write : Writable Extracted.programImage m dst 120)
    (srcAbove : sp.toNat + 8 ≤ src.toNat) (dstAbove : sp.toNat + 8 ≤ dst.toNat)
    (apart : dst.toNat + 120 ≤ src.toNat ∨ src.toNat + 120 ≤ dst.toNat)
    (left : p.Stored m dst) (right : q.Stored m src) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a410,a,m⟩,[]⟩ out ∧
      RoutineReturn a m sp 0x218 [⟨dst.toNat,120⟩] out ∧
      (p.add q).Stored out.store dst ∧ ParseSignature.ArgumentWidths out.values := by
  let fr : Activation := ⟨m, sp, memLoad m sp 64, sp - 0x218,
    a[3].get 64, a[5].get 64, a[12].get 64, a[13].get 64, a[14].get 64, a[15].get 64,
    dst, src, a[2].get 64, a[1].get 64, a[8].get 64, a[9].get 64,
    a[39].get 32, a[50].get 16, a[51].get 16, default⟩
  have canon (v : Value) {w : Nat} (eqw : v.width = w) : v = ⟨w,v.get w⟩ := by
    cases v with | mk width bits => subst w; simp [Value.get]
  have gp (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) :=
    canon _ (entry.saved i hi)
  have arg (i : Fin Reg.count) (hi : i.val ∈ Activation.argumentNumbers) :=
    canon _ (widths i hi)
  have base : (sp - 0x218).toNat = sp.toNat - 0x218 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr entry.room)
  have atoms : Atom.All Extracted.programImage a m (Generate.LIR.Fn10a410.frameAt .l10a410 fr) := by
    refine ⟨entry.rsp,entry.df,arg 1 (by decide),arg 2 (by decide),
      gp 3 (by decide),gp 5 (by decide),?_,?_,arg 8 (by decide),arg 9 (by decide),
      gp 12 (by decide),gp 13 (by decide),gp 14 (by decide),gp 15 (by decide),
      canon _ entry.mxcsr,canon _ entry.ftw,canon _ entry.fcw,entry.returnSlot,rfl,
      entry.returnLow,entry.stack,?_,entry.aligned,trivial⟩
    · exact (arg 6 (by decide)).trans (congrArg (Value.mk 64) si)
    · exact (arg 7 (by decide)).trans (congrArg (Value.mk 64) di)
    · change (sp - 0x218).toNat + 0x218 ≤ sp.toNat
      rw [base]
      have := entry.room
      omega
  obtain ⟨out,run,tag,post,returnedWidths,stored,frame⟩ :=
    Generate.Generator.Multiply.addCall Common.fnCode_subset_programImage fr a m p q atoms
      read write srcAbove dstAbove apart left right
  obtain ⟨rsp,df,bx,bp,v12,v13,v14,v15,mx,ft,fc,_⟩ := post
  have shared : (Generate.LIR.Label.l10a410, Label.l10a410) ∈ sharedEntry :=
    List.Mem.tail _ (List.Mem.tail _ (.head _))
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
    rw [← base]
    exact frame

end K256.Proofs.Verify.Core.Lincomb.Loop
