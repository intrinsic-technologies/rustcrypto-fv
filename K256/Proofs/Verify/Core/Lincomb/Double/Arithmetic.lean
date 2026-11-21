import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Endpoints
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Finish
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Output
import K256.Proofs.Verify.Core.Lincomb.Recode.Memory
import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Segments

namespace K256.Proofs.Verify.Core.Lincomb.Double

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Field Common.Point
open Generate.Generator.Multiply (Projective PointWordsAt)

theorem arithmeticBody {initial a : Registers} {orig m : Ram} {sp dst : BitVec 64}
    {p : Projective} {w : PointWords}
    (entry : RoutineEntry initial orig sp 0x298)
    (rsp : a[4] = ⟨64, sp - 0x228⟩)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → a[i] = initial[i])
    (frame : RamWriteFrame orig m [scratch sp 0x298])
    (saved : ∀ i : Fin 6, let r := (#v[5,15,14,13,12,3] : Vector (Fin Reg.count) 6)[i]
      (⟨64, memLoad m (sp - BitVec.ofNat 64 (8*(i.val+1))) 64⟩ : Value) = initial[r])
    (destPtr : memLoad m (sp - 0x228 + 0x1a0) 64 = dst)
    (destWrite : Writable Extracted.programImage orig dst 120)
    (dest : Outside [scratch sp 0x298, ⟨sp.toNat, 8⟩] dst 120)
    (words : PointWordsAt m (sp - 0x228 + 0x128) w)
    (repr : Projective.WordsRepr w p)
    (yy : ∀ i : Fin 5, memLoad m ((sp - 0x228) + (#v[0x20,0x28,0x48,0x60,0x40] : Vector (BitVec 64) 5)[i]) 64 =
      (squareWords w.y)[i])
    (zz : WordsAt m (sp - 0x228 + 0x1d0) 64 (squareWords w.z)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l110d64, a, m⟩, []⟩ out ∧
      RoutineReturn initial orig sp 0x298 [⟨dst.toNat,120⟩] out ∧
      ParseSignature.ArgumentWidths out.values ∧ p.double.Stored out.store dst := by
  let q := sp - 0x228
  let yy' := squareWords w.y
  let zz' := squareWords w.z
  have window : Writable Extracted.programImage m q 0x1f8 :=
    (Recode.stackSlot entry (off := 0x228) (by decide) (by decide)).of_frame frame
  have atoms := Arithmetic.entryAtoms window words yy zz
  have seed : ValuesMatch (Arithmetic.values a w yy' zz' q) a := by
    intro i
    simp only [Arithmetic.values, i.isLt, dite_true, Fin.getElem_fin]
  obtain ⟨b,n,run,vals,tail,fr⟩ := Arithmetic.segments rsp seed atoms
  obtain ⟨x,z,y,width⟩ := Arithmetic.finalWords vals tail
  have identical (i : Fin Reg.count) :
      b[i.val]'(by have h := i.isLt; change i.val < 53 at h; omega) = a[i] := by
    let j : Fin 3504 := ⟨i.val, by have h := i.isLt; change i.val < 53 at h; omega⟩
    have h := vals j
    simpa only [j, Arithmetic.values, i.isLt, dite_true, Fin.getElem_fin] using h
  have room := entry.room
  have high := entry.returnSlot.low
  have qnat : q.toNat = sp.toNat - 0x228 := BitVec.toNat_sub_of_le (by exact show 0x228 ≤ sp.toNat by omega)
  have addrNat : (q + 0x1a0).toNat = sp.toNat - 0x228 + 0x1a0 := by
    rw [BitVec.toNat_add, qnat]
    change (_ + 0x1a0) % 2^64 = _
    rw [Nat.mod_eq_of_lt (by omega)]
  have frame' : RamWriteFrame orig n [scratch sp 0x298] := by
    apply frame.trans fr
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, .head _, ?_⟩
    change sp.toNat - 0x298 ≤ q.toNat ∧ q.toNat + 0x1a0 ≤ sp.toNat - 0x298 + 0x298
    rw [qnat]
    omega
  have preserve {addr : Word} (lo : sp.toNat - 0x228 + 0x1a0 ≤ addr.toNat)
      (hi : addr.toNat + 8 ≤ 2^64) : memLoad n addr 64 = memLoad m addr 64 := by
    apply fr.memLoad_eq
    refine ⟨hi, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change q.toNat + 0x1a0 ≤ addr.toNat
    rwa [qnat]
  have ptr := (preserve (addr := q+0x1a0) (by rw [addrNat]; omega) (by rw [addrNat]; omega)).trans destPtr
  have loadSaved (i : Fin 6) :
      memLoad n (sp - BitVec.ofNat 64 (8*(i.val+1))) 64 =
        memLoad m (sp - BitVec.ofNat 64 (8*(i.val+1))) 64 := by
    have h := i.isLt
    have natOff : (BitVec.ofNat 64 (8*(i.val+1))).toNat = 8*(i.val+1) := Nat.mod_eq_of_lt (by omega)
    have eqn := BitVec.toNat_sub_of_le (x := sp) (y := BitVec.ofNat 64 (8*(i.val+1)))
      (by change (BitVec.ofNat 64 (8*(i.val+1))).toNat ≤ sp.toNat; rw [natOff]; omega)
    rw [natOff] at eqn
    exact preserve (by rw [eqn]; omega) (by rw [eqn]; omega)
  have output : Projective.WordsRepr (Arithmetic.outputWords w yy' zz' q) p.double := by
    rw [Arithmetic.outputWords_eq repr]
    obtain ⟨hx,hy,hz⟩ := DoubleWords.double_repr repr.x repr.y repr.z
    exact ⟨hx,hy,hz⟩
  obtain ⟨out,done,returned,widths,result⟩ := finishArithmetic entry ((identical 4).trans rsp)
    (fun i hi => (identical i).trans (keep i hi)) frame'
    (fun i => by rw [loadSaved]; exact saved i) ptr destWrite dest x z y width output
  exact ⟨out, Recode.done (run.trans done), returned, widths, result⟩

end K256.Proofs.Verify.Core.Lincomb.Double
