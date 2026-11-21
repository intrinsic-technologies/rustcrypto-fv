import K256.Proofs.Verify.Choice
import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.Shift.State

namespace K256.Proofs.Signing.Nonce.Initialize.DigestShift

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine Verify.LIR Verify.Core

private theorem apart (base d e : BitVec 64)
    (h : 8 ≤ (e - d).toNat ∧ 8 ≤ (d - e).toNat) :
    RangeApart (base + d) 8 (base + e) 8 := by
  apply RangeApart.of_diff
  simpa only [show base + e - (base + d) = e - d by bv_omega,
    show base + d - (base + e) = d - e by bv_omega] using h

local macro "shift_load" : tactic => `(tactic|
  simp (disch := first | exact apart _ _ _ (by decide) | decide) only
    [memLoad_memStore_same,memLoad_memStore_of_rangeApart])

theorem saveRegisters {base : BitVec 64} {a : Registers} {m : Ram}
    (area : Writable Extracted.programImage m base 216)
    (sp : a[4] = ⟨64,base+72⟩) (shift : a[2] = ⟨64,0⟩) :
    ∃ (c : Registers) (p : Ram), program.runBlock (dialect Extracted.programImage) ⟨.l1065b0,a,m⟩ = .jump ⟨.l1065ca,c,p⟩ ∧
      RamWriteFrame m p [⟨(base + 24).toNat,48⟩] ∧
      (∀ (i : Fin 6), memLoad p (base + BitVec.ofNat 64 (24 + i.val * 8)) 64 =
        a[(#v[3,12,13,14,15,5] : Vector (Fin Reg.count) 6)[i]].get 64) ∧
      c[4] = ⟨64,base⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [2,6,7,22,39,50,51] → c[i] = a[i]) := by
  have lim := area.readable.low
  have rsp : a[4].get 64 = base + 72 := congrArg (Value.get 64) sp
  have z : a[2].get 64 = 0 := congrArg (Value.get 64) shift
  have cmp : (cmpSpec (0 : BitVec 32) 256).CF = true := by decide
  refine ⟨?_,?_,?step,?post⟩
  case step =>
    cfg_eval [rsp,z,cmp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1065b0)
    rfl
  case post =>
    refine ⟨?_,?_,?_,?_⟩
    · slot_state region
    · intro i
      finite_cases i
      · change memLoad _ (base + 24) 64 = a[3].get 64
        shift_load
      · change memLoad _ (base + 32) 64 = a[12].get 64
        shift_load
      · change memLoad _ (base + 40) 64 = a[13].get 64
        shift_load
      · change memLoad _ (base + 48) 64 = a[14].get 64
        shift_load
      · change memLoad _ (base + 56) 64 = a[15].get 64
        shift_load
      · change memLoad _ (base + 64) 64 = a[5].get 64
        shift_load
    · rfl
    · rintro ⟨i,_⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem copyWords {base : BitVec 64} {a : Registers} {m : Ram}
    {w : Vector (BitVec 64) 4} (area : Writable Extracted.programImage m base 216)
    (sp : a[4].get 64 = base + 80) (shift : a[5] = ⟨64,0⟩)
    (words : WordsAt m (base + 184) 64 w) :
    ∃ (b : Registers) (n : Ram), program.runBlock (dialect Extracted.programImage) ⟨.l101072,a,m⟩ =
        .call ⟨.l1065b0,b,n⟩ (Verify.resumeAt .l1010ae 0x1010ae) ∧
      RamWriteFrame m n (footprint base) ∧ memLoad n (base + 72) 64 = 0x1010ae ∧
      WordsAt n (base + 152) 64 w ∧ b[4] = ⟨64,base + 72⟩ ∧
      b[6] = ⟨64,base + 152⟩ ∧ b[7] = ⟨64,base + 88⟩ ∧ b[2] = ⟨64,0⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  have z : a[5].get 64 = 0 := congrArg (Value.get 64) shift
  have lim := area.readable.low
  refine ⟨?_,?_,?call,?post⟩
  case call =>
    cfg_eval [sp,z]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l101072)
    rfl
  case post =>
    refine ⟨?_,?_,?_,rfl,rfl,rfl,rfl,?_⟩
    · unfold footprint
      slot_state region
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      have input := words i hi
      rcases cases with rfl|rfl|rfl|rfl <;>
        simpa (disch := first | exact apart _ _ _ (by decide) | decide) only
          [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.reduceOfNat,Lift.reduceAddOffset,
           memLoad_memStore_same,memLoad_memStore_of_rangeApart] using input
    · rintro ⟨i,_⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem enter {base : BitVec 64} {a : Registers} {m : Ram}
    {w : Vector (BitVec 64) 4} (area : Writable Extracted.programImage m base 216)
    (sp : a[4].get 64 = base + 80) (shift : a[5] = ⟨64,0⟩)
    (words : WordsAt m (base + 184) 64 w) :
    ∃ b n c p, program.runBlock (dialect Extracted.programImage) ⟨.l101072,a,m⟩ =
        .call ⟨.l1065b0,b,n⟩ (Verify.resumeAt .l1010ae 0x1010ae) ∧
      Reaches .l1065b0 b n .l1065ca c p ∧ RamWriteFrame m p (footprint base) ∧
      Saved base a p ∧ WordsAt p (base + 152) 64 w ∧ c[4] = ⟨64,base⟩ ∧
      c[6] = ⟨64,base + 152⟩ ∧ c[7] = ⟨64,base + 88⟩ ∧ c[2] = ⟨64,0⟩ ∧ FlagsKept a c := by
  obtain ⟨b,n,call,copied,ret,limbs,bsp,src,dst,zero,preserved⟩ :=
    copyWords area sp shift words
  obtain ⟨c,p,jump,writes,saved,csp,kept⟩ := saveRegisters (area.of_frame copied) bsp zero
  have bound := area.readable.low
  have above : (base + 24).toNat = base.toNat + 24 := by
    simp only [BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow]; omega
  have total := copied.trans writes (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,by simp only [above]; omega,by simp only [above]; omega⟩)
  refine ⟨b,n,c,p,call,.single ?_,total,?_,?_,csp,(kept 6 (by decide)).trans src,
    (kept 7 (by decide)).trans dst,(kept 2 (by decide)).trans zero,?_⟩
  · change (program.runBlock _ _).next _ [] = _
    rw [jump]
    rfl
  · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · exact (saved 0).trans (congrArg (Value.get 64) (preserved 3 (by decide)))
    · exact (saved 1).trans (congrArg (Value.get 64) (preserved 12 (by decide)))
    · exact (saved 2).trans (congrArg (Value.get 64) (preserved 13 (by decide)))
    · exact (saved 3).trans (congrArg (Value.get 64) (preserved 14 (by decide)))
    · exact (saved 4).trans (congrArg (Value.get 64) (preserved 15 (by decide)))
    · exact (saved 5).trans (congrArg (Value.get 64) (preserved 5 (by decide)))
    · apply (writes.memLoad_eq ?_).trans ret
      simp only [Outside,List.mem_singleton,forall_eq,above,BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow,Nat.reduceDiv]
      omega
  · apply WordsAt.of_frame limbs writes (by decide)
    simp only [Outside,List.mem_singleton,forall_eq,above,BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow,Nat.reduceDiv,Nat.reduceMul]
    omega
  · intro i hi
    have mem₁ : i.val ∈ [2,6,7,22,39,50,51] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega
    have mem₂ : i.val ∈ [3,5,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega
    exact (kept i mem₁).trans (preserved i mem₂)

end K256.Proofs.Signing.Nonce.Initialize.DigestShift
