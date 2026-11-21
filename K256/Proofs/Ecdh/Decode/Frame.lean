import K256.Proofs.Ecdh.Decode.Child
import K256.Proofs.Ecdh.Decode.Affine.Frame

namespace K256.Proofs.Ecdh.Decode

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

theorem readableWithSlot {m : Ram} {base slot : BitVec 64} {n : Nat}
    (lower : Readable m base n) (upper : Readable m slot 8)
    (adj : base.toNat+n = slot.toNat) : Readable m base (n+8) := by
  refine ⟨by have := upper.low; omega, ?_⟩
  intro i hi
  by_cases before : i < n
  · exact lower.present i before
  · have p := upper.present (i-n) (by omega)
    have eq : slot = base + BitVec.ofNat 64 n := by
      apply BitVec.eq_of_toNat_eq
      have hlow := lower.low
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
        Nat.mod_eq_of_lt (by omega), adj]
    rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)] at p
    exact p

theorem afterAffine {fr : Activation} {a : Values Value Reg.count} {m n : Ram}
    (room : fr.low.toNat+1464 ≤ fr.rsp.toNat) (slot : Readable fr.original fr.rsp 8)
    (pack : RamWriteFrame fr.original m [Packing.window (workSP fr)])
    (child : RamWriteFrame m n (Affine.writes (affineActivation fr a m))) :
    RamWriteFrame fr.original n [fr.region] ∧
    memLoad n (workSP fr+264) 64 = memLoad fr.original fr.rsp 64 ∧
    ∀ off : BitVec 64, 240 ≤ off.toNat → off.toNat ≤ 256 →
      memLoad n (workSP fr+off) 64 = memLoad m (workSP fr+off) 64 := by
  let sp := workSP fr
  have start : (sp-8-1192).toNat = fr.rsp.toNat-1464 := by
    rw [show sp-8-1192 = fr.rsp-1464 by dsimp only [sp,workSP]; bv_omega,
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1464 ≤ fr.rsp.toNat; omega))]
    rfl
  have mid : (sp-8).toNat = fr.rsp.toNat-272 := by
    rw [show sp-8 = fr.rsp-272 by dsimp only [sp,workSP]; bv_omega,
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 272 ≤ fr.rsp.toNat; omega))]
    rfl
  have dataPos : (sp+144).toNat = fr.rsp.toNat-120 := workSP_offset room 144 (by decide)
  have pf : RamWriteFrame fr.original m [fr.region] := by
    apply (RamWriteFrame.refl _ _).trans pack
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_singleton_self _,?_,?_⟩
    · change fr.low.toNat ≤ (sp-8).toNat; omega
    · change (sp-8).toNat+272 ≤ fr.low.toNat+(fr.rsp.toNat-fr.low.toNat); omega
  have total : RamWriteFrame fr.original n [fr.region] := by
    apply pf.trans child
    intro r hr
    simp only [Affine.writes,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> refine ⟨_,List.mem_singleton_self _,?_,?_⟩
    · change fr.low.toNat ≤ (sp-8-1192).toNat; omega
    · change (sp-8-1192).toNat+1192 ≤ fr.low.toNat+(fr.rsp.toNat-fr.low.toNat); omega
    · change fr.low.toNat ≤ (sp+144).toNat; omega
    · change (sp+144).toNat+89 ≤ fr.low.toNat+(fr.rsp.toNat-fr.low.toNat); omega
  refine ⟨total,?_,?_⟩
  · rw [show workSP fr+264 = fr.rsp by unfold workSP; bv_omega]
    apply total.memLoad_eq
    refine ⟨by have := slot.low; change _+8 ≤ 2^64; omega, ?_⟩
    rintro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by change fr.low.toNat+(fr.rsp.toNat-fr.low.toNat) ≤ fr.rsp.toNat; omega)
  · intro off lo hi
    have diff : ((264 : BitVec 64)-off).toNat = 264-off.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change _ ≤ 264; omega))
    have nat := workSP_offset room off (by rw [diff]; omega)
    rw [diff] at nat
    apply child.memLoad_eq
    refine ⟨by have := slot.low; change _+8 ≤ 2^64; omega, ?_⟩
    intro r hr
    simp only [Affine.writes,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact Or.inr (by change (sp-8-1192).toNat+1192 ≤ _; omega)
    · exact Or.inr (by change (sp+144).toNat+89 ≤ _; omega)

end K256.Proofs.Ecdh.Decode
