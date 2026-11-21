import K256.Proofs.Verify.Core.Lincomb.Stack
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)


theorem finish {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s : Nat} {m n : Ram} (e : Entry fr a p digest r s)
    (saved : CallerFrame fr c b m n) (whole : RamWriteFrame fr.original n [fr.region]) :
    ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l10fca6,b,n⟩ = .returned out ∧
      out.store = n ∧ out.tag = some ⟨64,0x10526c⟩ ∧ out.values[4] = ⟨64,localSp fr⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = c[i] := by
  have load (k : Nat) (hk : k + 8 ≤ 0x28e0) : LoadOk n (slot fr k) 8 := by
    have pos := slotNat e (k := k) (by omega)
    have bottom := e.low_toNat
    have room := e.stackRoom
    have w : Writable _ n (slot fr k) 8 := (e.stack.of_frame whole).sub (by omega) (by omega)
    exact ⟨w.readable.low, w.readable.present⟩
  have sp := congrArg (Value.get 64) saved.sp
  change b[4].get 64 = workSp fr at sp
  have last : (memLoad n (workSp fr + 0x28d8) 64).toNat < 2^32 := by
    change (memLoad n (slot fr 0x28d8) 64).toNat < _
    rw [saved.ret]
    decide
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [sp, BitVec.add_assoc, last]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; exact load _ (by decide))
    rfl
  case post =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · exact congrArg (fun x : BitVec 64 => some (Value.mk 64 x)) saved.ret
    · change (⟨64,workSp fr + 0x28e0⟩ : Value) = _
      rw [workSp, BitVec.sub_add_cancel]
    · rintro ⟨i,hi⟩ live
      simp only [List.mem_cons, List.not_mem_nil, or_false] at live
      rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact saved.saved 0
      · exact saved.saved 5
      · exact saved.saved 1
      · exact saved.saved 2
      · exact saved.saved 3
      · exact saved.saved 4
      · exact saved.fixedRegs 22 (by decide)
      · exact saved.fixedRegs 39 (by decide)
      · exact saved.fixedRegs 50 (by decide)
      · exact saved.fixedRegs 51 (by decide)

end K256.Proofs.Verify.Core.Lincomb
