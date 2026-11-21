import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Sites

import K256.Proofs.Verify.Core.Lincomb.Transfer
import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Execution
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Execution
import K256.Proofs.Generate.Generator.Multiply.Split.Rounding.Execution

namespace K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Multiply.Split (ScalarRoutine add mul round)
open Generate.Generator.Multiply.Split.Caller (Site boundedInputs)

private def layout : Site → Generate.LIR.Label → Activation → List Atom
  | .addFirst | .addSecond => Generate.LIR.Fn1109b0.frameAt
  | .roundFirst | .roundSecond => Generate.LIR.Fn11b8f0.frameAt
  | _ => Generate.LIR.Fn1099c0.frameAt

private def usesOrder : Site → Bool
  | .addFirst | .addSecond => true
  | _ => false

private def result : Site → Nat → Nat → Nat
  | .addFirst | .addSecond => fun x y => (x + y) % domain.n
  | .roundFirst | .roundSecond => Generate.Curve.mulShift384
  | _ => fun x y => (x * y) % domain.n

theorem execute (site : Site) {a : Registers} {n : Ram} {stack dst xptr yptr : BitVec 64}
    {d : Nat} (entry : RoutineEntry a n stack site.window)
    (di : a[7] = ⟨64,dst⟩) (si : a[6] = ⟨64,xptr⟩) (dx : a[2] = ⟨64,yptr⟩)
    (widths : ParseSignature.ArgumentWidths a)
    (order : site = .addFirst ∨ site = .addSecond → a[1].get 64 = 0x2021a0)
    (bound : d < domain.n) (rx : Readable n xptr 32) (ry : Readable n yptr 32)
    (write : Writable Extracted.programImage n dst 32) (above : stack.toNat + 8 ≤ dst.toNat)
    (apart : ∀ p ∈ [xptr,yptr],
      (p.toNat + 32 ≤ stack.toNat - site.window ∨ stack.toNat + 8 ≤ p.toNat) ∧
      (p.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ p.toNat))
    (wx : WordsAt n xptr 64 (scalarWords (site.x d)))
    (wy : WordsAt n yptr 64 (scalarWords (site.y d))) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨callee site,a,n⟩,[]⟩ out ∧
      RoutineReturn a n stack site.window [⟨dst.toNat,32⟩] out ∧
      WordsAt out.store dst 64 (scalarWords (site.value d)) ∧
      ParseSignature.ArgumentWidths out.values := by
  let fr : Activation := ⟨n, stack, memLoad n stack 64, stack - BitVec.ofNat 64 site.window,
    a[3].get 64, a[5].get 64, a[12].get 64, a[13].get 64, a[14].get 64, a[15].get 64,
    dst, xptr, yptr, a[1].get 64, a[8].get 64, a[9].get 64,
    a[39].get 32, a[50].get 16, a[51].get 16, default⟩
  let info := { Generate.LIR.Fn1109b0.frameInfo with stackBytes := some site.window }
  have canon (v : Value) {w : Nat} (eqw : v.width = w) : v = ⟨w,v.get w⟩ := by
    cases v with | mk width bits => subst w; simp only [Value.get_mk]
  have gp (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) :=
    canon _ (entry.saved i hi)
  have arg (i : Fin Reg.count) (hi : i.val ∈ Activation.argumentNumbers) :=
    canon _ (widths i hi)
  have room := entry.room
  have windowNat : (BitVec.ofNat 64 site.window).toNat = site.window := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt room stack.isLt)]
  have low : fr.low.toNat + site.window ≤ stack.toNat := by
    change (stack - BitVec.ofNat 64 site.window).toNat + site.window ≤ _
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [windowNat]; exact room)), windowNat]
    omega
  have nonzero : info.window ≠ 0 := by
    change site.window ≠ 0
    cases site <;> decide
  have commonEntry : Atom.All Extracted.programImage a n (info.entryAtoms fr) := by
    simp only [FrameInfo.entryAtoms, FrameInfo.frameAtoms, FrameInfo.entryFrame,
      FrameInfo.stackAtoms, ite_eq_right nonzero]
    exact ⟨entry.rsp,entry.df,arg 1 (by decide),dx,gp 3 (by decide),gp 5 (by decide),
      si,di,arg 8 (by decide),arg 9 (by decide),gp 12 (by decide),gp 13 (by decide),
      gp 14 (by decide),gp 15 (by decide),canon _ entry.mxcsr,canon _ entry.ftw,
      canon _ entry.fcw,entry.returnSlot,rfl,entry.returnLow,entry.stack,low,entry.aligned,trivial⟩
  have atoms : Atom.All Extracted.programImage a n (layout site site.callee fr) := by
    cases site <;> exact commonEntry
  have runSite :
      ScalarRoutine site.callee (layout site) Generate.LIR.Fn1109b0.doneAt site.window
        (usesOrder site) (result site) := by
    cases site <;> first | exact add | exact mul | exact round add
  have orderArg : usesOrder site = true → fr.rcx = 0x2021a0 := by
    cases site <;> intro h
    all_goals first | contradiction | exact order (by decide)
  have resultValue : result site (site.x d) (site.y d) = site.value d := by
    cases site with
    | addFirst => exact Nat.add_mod_mod ..
    | addSecond =>
      simp only [result, Site.x, Site.y, Site.value, Generate.Curve.splitSecond,
        Nat.mod_add_mod, Nat.add_mod_mod]
    | _ => rfl
  obtain ⟨hx,hy⟩ := boundedInputs site bound
  obtain ⟨out,run,tag,post,returnedWidths,stored,frame⟩ :=
    runSite atoms entry.image orderArg hx hy rx ry write above apart wx wy
  obtain ⟨rsp,df,bx,bp,v12,v13,v14,v15,mx,ft,fc,_⟩ := post
  have shared : (site.callee, callee site) ∈ sharedEntry := by
    cases site <;> (repeat first | exact .head _ | apply List.Mem.tail)
  rw [resultValue] at stored
  refine ⟨out, transfer shared run, ⟨tag,rsp,?_,frame⟩, stored, returnedWidths⟩
  rintro ⟨i,hi⟩ h
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

end K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls
