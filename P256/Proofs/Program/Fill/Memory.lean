import X86Proofs.Program.ReadWrite.WriteFrame
import P256.Proofs.Program.Interface
import P256.Proofs.Common.Machine.CallReturn
import P256.Proofs.Program.Code
import P256.Proofs.Program.Memory
import P256.Proofs.Common.Memory.Fill.Memory

set_option autoImplicit false

namespace P256.Proofs.Common.Memory.Fill

open P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {b : ReturnBoundary}
  {entry : BitVec 64} {inputBytes n reserve count more : Nat}

theorem destinationContains (hp : CalleePre s b entry inputBytes n reserve)
    {i : Nat} (hi : i < n) :
    (registerRegion s .rdi n).Contains (s.regValue .rdi + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add hp.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem FillState.loaded (hp : CalleePre s b entry inputBytes n reserve)
    (h : FillState s t count) (hc : count ≤ n) : ProgramLoaded t := by
  intro address byte hb
  refine (h.agrees.byte ?_).trans (hp.loaded address byte hb)
  intro c hmem hcov
  simp only [fillComponents, registerComponents, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;>
    try exact hcov
  obtain ⟨i, hi, rfl⟩ := hcov
  exact hp.avoids (registerRegion s .rdi n) (by simp)
    _ (destinationContains hp (by omega)) (.inl ⟨byte, hb⟩)

theorem FillState.destinationReadable (hp : CalleePre s b entry inputBytes n reserve)
    (h : FillState s t count) (hc : count + more ≤ n) :
    MemReadable t (t.regValue .rdi) more := by
  have hl : (s.regValue .rdi).toNat + n < 2^32 := hp.outputBounded
  have htn : (t.regValue .rdi).toNat = (s.regValue .rdi).toNat + count := by
    rw [h.rdi, toNat_add_ofNat _ _ (by omega)]
  refine ⟨by omega, ?_⟩
  intro i hi
  rw [h.rdi, add_ofNat_add_ofNat]
  apply h.agrees.grow
  exact Option.isSome_iff_exists.mpr
    (hp.outputAllocated _ (destinationContains hp (by omega)))

theorem FillState.destinationTables (hp : CalleePre s b entry inputBytes n reserve)
    (h : FillState s t count) (hc : count + more ≤ n) (hpos : 0 < more) :
    (t.regValue .rdi).toNat + more ≤ 0x1000 ∨ 0x3000 ≤ (t.regValue .rdi).toNat := by
  apply P256.Proofs.Program.tables_interval_of_not_reserved hpos (h.destinationReadable hp hc).low
  intro i hi hin
  have hcontains : (registerRegion s .rdi n).Contains
      (t.regValue .rdi + BitVec.ofNat 64 i).toNat := by
    rw [h.rdi, add_ofNat_add_ofNat]
    exact destinationContains hp (by omega)
  apply hp.avoids (registerRegion s .rdi n) (by simp) _ hcontains
  right
  exact hin

theorem FillState.destinationCodeApart {p : BitVec 64} {bytes : List UInt8}
    (hp : CalleePre s b entry inputBytes n reserve)
    (h : FillState s t count) (hc : count + more ≤ n)
    (hcode : ∀ i < bytes.length, InProgram (p + BitVec.ofNat 64 i)) :
    RangeApart (t.regValue .rdi) more p bytes.length := by
  intro i hi j hj he
  have hcontains : (registerRegion s .rdi n).Contains
      (t.regValue .rdi + BitVec.ofNat 64 i).toNat := by
    rw [h.rdi, add_ofNat_add_ofNat]
    exact destinationContains hp (by omega)
  exact hp.avoids (registerRegion s .rdi n) (by simp) _ hcontains
    (.inl (he ▸ hcode j hj))

end P256.Proofs.Common.Memory.Fill
