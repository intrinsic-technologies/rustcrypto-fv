import K256.Proofs.Verify.Core.Lincomb.Recode.Memory

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def savedRegs : Vector (Fin Reg.count) 6 := #v[5,15,14,13,12,3]

def SavedAt (a : Registers) (sp : BitVec 64) (m : Ram) : Prop :=
  ∀ i : Fin 6, memLoad m (sp - BitVec.ofNat 64 (8*(i.val+1))) 64 = a[savedRegs[i]].get 64

theorem saveValue {a : Registers} {m : Ram} {sp : BitVec 64} {depth : Nat}
    (entry : RoutineEntry a m sp depth) {i : Fin Reg.count}
    (hi : i.val ∈ [3,5,12,13,14,15]) : (⟨64, a[i].get 64⟩ : Value) = a[i] := by
  have wid := entry.saved i hi
  cases h : a[i] with
  | mk w bits =>
    rw [h] at wid
    change w = 64 at wid
    cases wid
    rfl

theorem subNat {sp off : BitVec 64} (h : off.toNat ≤ sp.toNat) :
    (sp-off).toNat = sp.toNat-off.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem scratchContains {sp child : BitVec 64} {depth size : Nat}
    (room : size ≤ child.toNat) (start : sp.toNat - depth ≤ child.toNat - size)
    (stop : child.toNat ≤ sp.toNat) :
    ∀ r ∈ [scratch child size], (scratch sp depth).start ≤ r.start ∧
      r.start + r.size ≤ (scratch sp depth).start + (scratch sp depth).size := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  change sp.toNat - depth ≤ child.toNat - size ∧ child.toNat - size + size ≤ sp.toNat - depth + depth
  omega

theorem outsideReturn {sp : BitVec 64} {depth : Nat}
    (low : sp.toNat+8 ≤ 2^32) (room : depth ≤ sp.toNat) :
    Outside [scratch sp depth] sp 8 :=
  ⟨by omega, fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    right
    change sp.toNat-depth+depth ≤ sp.toNat
    omega⟩

theorem imageFromFrame {a : Registers} {m m' : Ram} {sp : BitVec 64} {depth : Nat}
    (entry : RoutineEntry a m sp depth) (frame : RamWriteFrame m m' [scratch sp depth]) :
    ∀ v ∈ Extracted.programImage, m'[v.1]? = some v.2 := by
  intro v hv
  rw [frame.outside _ ?_, entry.image v hv]
  refine ⟨by have := v.1.isLt; omega, ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  have room := entry.room
  have baseNat : (sp - BitVec.ofNat 64 depth).toNat = sp.toNat - depth := by
    have := sp.isLt
    have hdepth : (BitVec.ofNat 64 depth).toNat = depth := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [subNat (by omega), hdepth]
  change v.1.toNat + 1 ≤ sp.toNat-depth ∨ sp.toNat-depth+depth ≤ v.1.toNat
  by_cases lower : v.1.toNat < sp.toNat-depth
  · exact Or.inl (by omega)
  by_cases upper : sp.toNat ≤ v.1.toNat
  · exact Or.inr (by omega)
  exfalso
  have lb : (sp-BitVec.ofNat 64 depth).toNat ≤ v.1.toNat := by rw [baseNat]; omega
  have off : v.1.toNat - (sp-BitVec.ofNat 64 depth).toNat < depth := by rw [baseNat]; omega
  apply entry.stack.notCode v hv _ off
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.1.isLt; omega),
    Nat.mod_eq_of_lt (by have := v.1.isLt; omega)]
  omega

end K256.Proofs.Verify.Core.Lincomb.Recode
