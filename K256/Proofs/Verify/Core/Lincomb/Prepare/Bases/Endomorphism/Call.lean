import K256.Proofs.Verify.Core.Lincomb.Interface
import K256.Proofs.Verify.Core.Lincomb.Transfer
import K256.Proofs.Ecdh.Multiply.Endomorphism
import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.Endomorphism.Machine
import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.State

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (Projective)

open Lean Elab Command in
local elab "open_peer_result" : command => do
  let name := mkPrivateNameCore `K256.Proofs.Ecdh.Multiply.Endomorphism
    `K256.Proofs.Generate.Generator.Multiply.Prepare.peerResult
  modifyScope fun scope =>
    { scope with openDecls := .explicit `peerResult name :: scope.openDecls }

open_peer_result

theorem endomorphismCall {a : Registers} {m : Ram} {sp dst src : BitVec 64} {p : Projective}
    (entry : RoutineEntry a m sp 128)
    (di : a[7] = ⟨64,dst⟩) (si : a[6] = ⟨64,src⟩)
    (read : Readable m src 120) (write : Writable Extracted.programImage m dst 120)
    (srcApart : src.toNat + 120 ≤ sp.toNat - 128 ∨ sp.toNat + 8 ≤ src.toNat)
    (dstAbove : sp.toNat + 8 ≤ dst.toNat)
    (apart : src.toNat + 120 ≤ dst.toNat ∨ dst.toNat + 120 ≤ src.toNat)
    (valid : p.valid) (point : p.Stored m src) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10e010,a,m⟩,[]⟩ out ∧
      RoutineReturn a m sp 128 [⟨dst.toNat,120⟩] out ∧
      PointValueAt out.store dst (Generate.Curve.endomorphism p.value) := by
  let fr : Activation := ⟨m, sp, memLoad m sp 64, sp - 128,
    a[3].get 64, a[5].get 64, a[12].get 64, a[13].get 64, a[14].get 64, a[15].get 64,
    dst, src, a[2].get 64, a[1].get 64, a[8].get 64, a[9].get 64,
    a[39].get 32, a[50].get 16, a[51].get 16, default⟩
  have canon (v : Value) {w : Nat} (eqw : v.width = w) : v = ⟨w,v.get w⟩ := by
    cases v with | mk width bits => subst w; simp [Value.get]
  have gp (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) :=
    canon _ (entry.saved i hi)
  have base : (sp - 128).toNat = sp.toNat - 128 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr entry.room)
  have atoms : Atom.All Extracted.programImage a m (Endomorphism.inputAtoms fr) := by
    refine ⟨entry.rsp,entry.df,
      gp 3 (by decide),gp 5 (by decide),si,di,
      gp 12 (by decide),gp 13 (by decide),gp 14 (by decide),gp 15 (by decide),
      canon _ entry.mxcsr,canon _ entry.ftw,canon _ entry.fcw,entry.returnSlot,rfl,
      entry.returnLow,entry.stack,?_,entry.aligned,trivial⟩
    · change (sp - 128).toNat + 128 ≤ sp.toNat
      rw [base]
      have := entry.room
      omega
  obtain ⟨x,y,z,wx,wy,wz,rx,ry,rz⟩ := point.coordinates
  obtain ⟨out,run,tag,post,_,frame,wx',wy',wz'⟩ :=
    Endomorphism.runPeer (fr := fr) atoms read write srcApart dstAbove apart wx wy wz
  obtain ⟨u,uv,us,ue⟩ := peerResult valid wx' wy' wz' rx ry rz
  obtain ⟨rsp,df,bx,bp,v12,v13,v14,v15,mx,ft,fc,_⟩ := post
  have shared : (Generate.LIR.Label.l10e010, Label.l10e010) ∈ sharedEntry :=
    .tail _ (.tail _ (.tail _ (.head _)))
  refine ⟨out, transfer shared run, ⟨tag,rsp,?_,?_⟩, ⟨u,uv,ue,us⟩⟩
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
