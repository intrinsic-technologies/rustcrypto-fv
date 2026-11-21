import P256.Proofs.Program.Input

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem loadBytes_ok_copy {source target : Ram} {a b : BitVec 64} {count : Nat}
    (copied : ∀ i < count, target[b + BitVec.ofNat 64 i]? = source[a + BitVec.ofNat 64 i]?)
    {value : BitVec 64} (loaded : loadBytes source a count = .ok value) :
    loadBytes target b count = .ok value := by
  have go (remaining : Nat) : ∀ current shift accumulator,
      current + remaining ≤ count →
      loadBytes.loop source a remaining current shift accumulator = .ok value →
      loadBytes.loop target b remaining current shift accumulator = .ok value := by
    induction remaining with
    | zero => intros; assumption
    | succ remaining ih =>
      intro current shift accumulator bound loaded
      have hc := copied current (by omega)
      simp only [loadBytes.loop, addAddress, fromNat] at loaded ⊢
      rw [hc]
      cases hb : source[a + BitVec.ofNat 64 current]? with
      | none => simp only [hb] at loaded; contradiction
      | some byte =>
        simp only [hb] at loaded ⊢
        exact ih _ _ _ (by omega) loaded
  exact go count 0 0 0 (by omega) loaded

theorem hasBytes_copy {source target : Ram} {a b : BitVec 64} {count : Nat}
    {input : ByteArray}
    (bytes : (MemoryRegion.mk a.toNat count).HasBytes source input)
    (copied : ∀ i < count, target[b + BitVec.ofNat 64 i]? = source[a + BitVec.ofNat 64 i]?) :
    (MemoryRegion.mk b.toNat count).HasBytes target input := by
  have size : input.size = count := bytes.1
  refine ⟨size, ?_⟩
  intro i
  change target[BitVec.ofNat 64 (b.toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, copied i.val (by have := i.isLt; omega)]
  have h := bytes.2 i
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

theorem copied_sub {source target : Ram} {a b : BitVec 64} {count offset len : Nat}
    (copied : ∀ i < count, target[b + BitVec.ofNat 64 i]? = source[a + BitVec.ofNat 64 i]?)
    (bound : offset + len ≤ count) :
    ∀ i < len, target[b + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      source[a + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact copied (offset + i) (by omega)

end P256.Proofs.Program
