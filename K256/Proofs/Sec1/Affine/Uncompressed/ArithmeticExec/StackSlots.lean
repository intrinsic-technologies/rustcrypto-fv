import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Sec1.LIR.Defs4

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR

abbrev slotAddr (sp : BitVec 64) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => sp
  | _ + 1 => sp + BitVec.ofNat 64 (8 * i)

structure SlotState (code : CodeMap) (initial current : Ram) (sp : BitVec 64)
    (slots : Nat → BitVec 64) : Prop where
  writable : Writable code current (sp - 8) 208
  frame : RamWriteFrame initial current [⟨(sp - 8).toNat, 208⟩]
  load : ∀ i < 25, memLoad current (slotAddr sp i) 64 = slots i

namespace SlotState

variable {code : CodeMap} {initial current : Ram} {sp : BitVec 64}
  {slots : Nat → BitVec 64}

theorem start (h : Writable code initial (sp - 8) 208) :
    SlotState code initial initial sp
      (fun i => memLoad initial (slotAddr sp i) 64) :=
  ⟨h, RamWriteFrame.refl _ _, fun _ _ => rfl⟩

private theorem slot_toNat (low : (sp - 8).toNat + 208 ≤ 2 ^ 32) {i : Nat} (hi : i < 25) :
    (slotAddr sp i).toNat = (sp - 8).toNat + (8 + 8 * i) := by
  have haddr : slotAddr sp i = (sp - 8) + BitVec.ofNat 64 (8 + 8 * i) := by
    have hslot : slotAddr sp i = sp + BitVec.ofNat 64 (8 * i) := by
      cases i with
      | zero => exact (BitVec.add_zero sp).symm
      | succ _ => rfl
    rw [hslot, BitVec.ofNat_add]
    bv_omega
  rw [haddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 + 8 * i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem region (low : (sp - 8).toNat + 208 ≤ 2 ^ 32)
    {addr : BitVec 64} (first : (sp - 8).toNat ≤ addr.toNat)
    (last : addr.toNat + 8 ≤ (sp - 8).toNat + 208) :
    InRegions [⟨(sp - 8).toNat, 208⟩] addr 8 :=
  ⟨_, List.mem_cons_self, first, last, by omega⟩

theorem loadOk (h : SlotState code initial current sp slots) {i : Nat} (hi : i < 25) :
    LoadOk current (slotAddr sp i) 8 := by
  have haddr := slot_toNat h.writable.readable.low hi
  exact LoadOk.of_region h.writable.readable (by omega) (by omega)

theorem write (h : SlotState code initial current sp slots) {i : Nat} (hi : i < 25)
    (word : BitVec 64) :
    SlotState code initial (memStore current (slotAddr sp i) word) sp
      (fun j => if j = i then word else slots j) := by
  have low := h.writable.readable.low
  have ai := slot_toNat low hi
  refine ⟨h.writable.memStore _ _, h.frame.memStore _ (region low (by omega) (by omega)), ?_⟩
  intro j hj
  by_cases heq : j = i
  · subst j
    rw [ite_eq_left rfl]
    exact memLoad_memStore_same current _ word (by decide) (by decide)
  · have aj := slot_toNat low hj
    rw [ite_eq_right heq, memLoad_memStore_of_rangeApart]
    · exact h.load j hj
    · apply RangeApart.of_toNat <;> omega

theorem push (h : SlotState code initial current sp slots) (word : BitVec 64) :
    SlotState code initial (memStore current (sp - 8) word) sp slots := by
  have low := h.writable.readable.low
  refine ⟨h.writable.memStore _ _, h.frame.memStore _ (region low (Nat.le_refl _) (by omega)), ?_⟩
  intro i hi
  have ai := slot_toNat low hi
  rw [memLoad_memStore_of_rangeApart]
  · exact h.load i hi
  · apply RangeApart.of_toNat <;> omega

private theorem arithmeticBlockLength : bytes_l11f8f6.length = 0x9a2 := by
  decide +kernel

private theorem arithmeticStoreOk {addr pc : BitVec 64} {len : Nat}
    (h : Writable code current addr 8) (cover : ∀ e ∈ fnCode, e ∈ code)
    (within : (pc - 0x11f8f6).toNat + len ≤ 0x9a2) :
    StoreOk code current addr 8 pc len := by
  have guard := ParseSignature.storeOk_of_codeRange h
    (fun e he => cover e (code_l11f8f6 e he)) (by rwa [arithmeticBlockLength])
  have eqAddr : 0x11f8f6 + BitVec.ofNat 64 (pc - 0x11f8f6).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rwa [eqAddr] at guard

theorem storeOk (h : SlotState code initial current sp slots) {i : Nat} (hi : i < 25)
    (cover : ∀ e ∈ fnCode, e ∈ code) {pc : BitVec 64} {len : Nat}
    (within : (pc - 0x11f8f6).toNat + len ≤ 0x9a2) :
    StoreOk code current (slotAddr sp i) 8 pc len := by
  have ai := slot_toNat h.writable.readable.low hi
  exact arithmeticStoreOk (h.writable.sub (by omega) (by omega)) cover within

theorem pushOk (h : SlotState code initial current sp slots)
    (cover : ∀ e ∈ fnCode, e ∈ code) {pc : BitVec 64} {len : Nat}
    (within : (pc - 0x11f8f6).toNat + len ≤ 0x9a2) :
    StoreOk code current (sp - 8) 8 pc len :=
  arithmeticStoreOk (h.writable.sub (Nat.le_refl _) (by omega)) cover within

end SlotState

end K256.Proofs.Sec1.Affine.Uncompressed
