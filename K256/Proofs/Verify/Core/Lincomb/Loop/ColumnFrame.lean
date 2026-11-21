import K256.Proofs.Verify.Core.Lincomb.Loop.Column

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem Column.withRegs {a b c : Registers} {m n : Ram} {sp dst table : BitVec 64}
    {k : Nat} {p : Curve.Point} (s : Column a m sp dst table k p b n)
    (keep : ∀ i : Fin Reg.count, i.val ∈ [4,5,8,9,22,39,50,51] → c[i] = b[i]) :
    Column a m sp dst table k p c n := by
  refine ⟨⟨(keep 4 (by decide)).trans s.rsp,s.dest,s.rbx,s.r12,s.r13,s.r14,s.r15,s.rbp,
    ?_,s.frame⟩,(keep 5 (by decide)).trans s.last,(keep 8 (by decide)).trans s.back,
    (keep 9 (by decide)).trans s.counter,s.savedCounter,s.savedFront,s.savedNext,s.savedBack,s.point,s.inactive⟩
  intro i hi
  exact (keep i ((by decide : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] →
    i.val ∈ [4,5,8,9,22,39,50,51]) i hi)).trans (s.control i hi)

theorem Column.setDigits {a b : Registers} {m n : Ram} {sp dst table : BitVec 64}
    {k : Nat} {p : Curve.Point} (s : Column a m sp dst table k p b n)
    (entry : RoutineEntry a m sp 0x478) (digits : BitVec 64) :
    Column a m sp dst table k p b (memStore n (baseSp sp + 24) digits) := by
  have room := entry.room
  have low := entry.returnSlot.low
  have subNat (off : BitVec 64) (h : off.toNat ≤ 0x478) :
      (sp - off).toNat = sp.toNat - off.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have addNat (off : BitVec 64) (h : off.toNat ≤ 0x1d8) :
      (baseSp sp + off).toNat = sp.toNat - 0x1d8 + off.toNat := by
    rw [baseSp, BitVec.toNat_add, subNat _ (by decide), Nat.mod_eq_of_lt (by omega)]
    rfl
  let pos := baseSp sp + 24
  have posNat : pos.toNat = sp.toNat - 0x1d8 + 24 := addNat _ (by decide)
  let area : MemoryRegion := ⟨pos.toNat,8⟩
  have written : RamWriteFrame n (memStore n pos digits) [area] :=
    (RamWriteFrame.refl _ _).memStore digits ⟨area,.head _,Nat.le_refl _,Nat.le_refl _,by omega⟩
  have outside (ptr : BitVec 64) (len : Nat) (h : ptr.toNat + len ≤ pos.toNat ∨ pos.toNat + 8 ≤ ptr.toNat)
      (hi : ptr.toNat + len ≤ 2^64) : Outside [area] ptr len :=
    ⟨hi, fun _ hm => List.mem_singleton.mp hm ▸ h⟩
  have below (off : BitVec 64) (h : off.toNat ≤ 48) : Outside [area] (sp-off) 8 := by
    have addr := subNat off (by omega)
    apply outside <;> omega
  have slot (off : BitVec 64) (len : Nat) (h : off.toNat + len ≤ 0x1d8)
      (sep : off.toNat + len ≤ 24 ∨ 32 ≤ off.toNat) : Outside [area] (baseSp sp + off) len := by
    have addr := addNat off (by omega)
    apply outside <;> omega
  have same (off : BitVec 64) (h : off.toNat ≤ 48) :=
    written.memLoad_eq (k := 64) (below off h)
  have word (off : BitVec 64) (h : off.toNat + 8 ≤ 0x1d8)
      (sep : off.toNat + 8 ≤ 24 ∨ 32 ≤ off.toNat) :=
    written.memLoad_eq (k := 64) (slot off 8 h sep)
  have current := word 0 (by decide) (by decide)
  rw [show baseSp sp + (0 : BitVec 64) = baseSp sp by bv_omega] at current
  refine ⟨⟨s.rsp,(word _ (by decide) (by decide)).trans s.dest,
    (same _ (by decide)).trans s.rbx,(same _ (by decide)).trans s.r12,
    (same _ (by decide)).trans s.r13,(same _ (by decide)).trans s.r14,
    (same _ (by decide)).trans s.r15,(same _ (by decide)).trans s.rbp,s.control,
    s.frame.trans written ?_⟩,s.last,s.back,s.counter,(word _ (by decide) (by decide)).trans s.savedCounter,
    (word _ (by decide) (by decide)).trans s.savedFront,(word _ (by decide) (by decide)).trans s.savedNext,
    current.trans s.savedBack,?_,?_⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,.head _,by change sp.toNat - 0x478 ≤ pos.toNat; omega,
      by change pos.toNat + 8 ≤ sp.toNat - 0x478 + 0x478; omega⟩
  · obtain ⟨q,stored,valid,val⟩ := s.point
    exact ⟨q,stored.of_frame written (slot _ _ (by decide) (by decide)),valid,val⟩
  · rw [written.memLoad_eq (k := 8) (slot 0x28 1 (by decide) (by decide))]
    exact s.inactive

end K256.Proofs.Verify.Core.Lincomb.Loop
