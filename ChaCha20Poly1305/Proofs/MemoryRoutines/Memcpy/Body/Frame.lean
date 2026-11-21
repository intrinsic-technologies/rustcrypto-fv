import ChaCha20Poly1305.Proofs.MemoryRoutines.Ranges

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Memcpy

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Common

def copyChanges (dst : BitVec 64) (count : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .flags, .rip, .mem dst count]

theorem copyChanges_trans {s t u : RamState} {dst : BitVec 64} {head tail : Nat}
    (ha : AgreesExcept (copyChanges dst head) s t)
    (hb : AgreesExcept (copyChanges (dst + BitVec.ofNat 64 head) tail) t u) :
    AgreesExcept (copyChanges dst (head + tail)) s u := by
  apply (ha.trans hb).widen
  · intro c hc hm
    simp only [List.mem_append] at hc
    rcases hc with hc | hc <;>
      simp only [copyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    all_goals
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [copyChanges, Component.isMem]
  · intro x c hc hcover
    refine ⟨.mem dst (head + tail), by simp [copyChanges], ?_⟩
    simp only [List.mem_append] at hc
    rcases hc with hc | hc <;>
      simp only [copyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        try exact hcover.elim
      obtain ⟨i, hi, he⟩ := hcover
      exact ⟨i, by omega, he⟩
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        try exact hcover.elim
      obtain ⟨i, hi, he⟩ := hcover
      refine ⟨head + i, by omega, ?_⟩
      rw [he, add_ofNat_add_ofNat]

theorem copyChanges_code {s t : RamState} {dst : BitVec 64} {count : Nat}
    (ha : AgreesExcept (copyChanges dst count) s t) (hw : WritableRange s dst count)
    (hc : CodeIn Extracted.programImage s) : CodeIn Extracted.programImage t := by
  apply CodeIn.of_agreesExcept ha _ hc
  intro x hx c hc hcover
  simp only [copyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcover.elim
  obtain ⟨i, hi, he⟩ := hcover
  exact hw.code i hi (he ▸ Machine.inProgram_of_mem hx)

theorem copyChanges_source {s t : RamState} {head : Nat} (hp : MemcpyPre s)
    (hh : head ≤ (rdx.read s).toNat)
    (ha : AgreesExcept (copyChanges (rdi.read s) head) s t) :
    ∀ i < (rdx.read s).toNat, t.external[rsi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  intro i hi
  apply ha.byte
  intro c hc hcover
  simp only [copyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcover.elim
  obtain ⟨j, hj, he⟩ := hcover
  have hsl := hp.src.low
  have hdl := hp.dst.readable.low
  have hdis := hp.disjoint
  have hn := congrArg BitVec.toNat he
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem copyChanges_prefix {s t : RamState} {dst : BitVec 64} {head tail : Nat}
    (hlow : dst.toNat + head + tail ≤ 2^32)
    (ha : AgreesExcept (copyChanges (dst + BitVec.ofNat 64 head) tail) s t) :
    ∀ i < head, t.external[dst + BitVec.ofNat 64 i]? =
      s.external[dst + BitVec.ofNat 64 i]? := by
  intro i hi
  apply ha.byte
  intro c hc hcover
  simp only [copyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact hcover.elim
  obtain ⟨j, hj, he⟩ := hcover
  rw [add_ofNat_add_ofNat] at he
  have hn := congrArg BitVec.toNat he
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem copyChanges_callChanges {s t : RamState}
    (ha : AgreesExcept (copyChanges (rdi.read s) (rdx.read s).toNat) s t) :
    AgreesExcept (callChanges s) s t := by
  apply ha.mono
  simp [copyChanges, callChanges]

end ChaCha20Poly1305.Proofs.MemoryRoutines.Memcpy
