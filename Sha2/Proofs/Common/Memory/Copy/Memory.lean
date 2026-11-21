import Sha2.Proofs.Common.Machine.Interfaces
import Sha2.Proofs.Common.Machine.Entry
import Sha2.Proofs.Common.Machine.CallReturn
import X86Proofs.Instructions.Movs.Execution

set_option autoImplicit false

open Sha2.Proofs.Common.Machine (CalleePre memoryRegion_contains_add)

namespace Sha2.Proofs.Common.Memory.Copy

open Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def registerComponents : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 8, .flags, .rip]

def copyComponents (s : RamState) (count : Nat) : List Component :=
  registerComponents ++ [.reg 6, .reg 7, .mem (s.regValue .rdi) count]

structure CopyState [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rsi : t.regValue .rsi = s.regValue .rsi + BitVec.ofNat 64 count
  rdi : t.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 count
  copy : ∀ i < count,
    t.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rsi + BitVec.ofNat 64 i]?
  agrees : AgreesExcept (copyComponents s count) s t

theorem CopyState.start [Bindings] {s : RamState} (h : ReadyToStep s) : CopyState s s 0 :=
  ⟨h, by simp, by simp, by intro i hi; omega, AgreesExcept.refl _ _⟩

theorem CopyState.registers [Bindings] {s t u : RamState} {count : Nat}
    (h : CopyState s t count) (hr : ReadyToStep u)
    (he : AgreesExcept registerComponents t u) : CopyState s u count := by
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · exact (he.read (n := 64) (r := 6) (by decide)).trans h.rsi
  · exact (he.read (n := 64) (r := 7) (by decide)).trans h.rdi
  · intro i hi
    exact (he.byte (by simp [registerComponents, Component.Covers])).trans (h.copy i hi)
  · exact (h.agrees.trans he).mono (by
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc
      · exact hc
      · exact List.mem_append_left _ hc)

theorem sourceLow [Bindings] {s : RamState} {b : ReturnBoundary} {n reserve : Nat}
    (h : CalleePre s b 0x10dd60 n n reserve) : (s.regValue .rsi).toNat + n < 2^32 :=
  h.inputBounded

theorem destinationLow [Bindings] {s : RamState} {b : ReturnBoundary} {n reserve : Nat}
    (h : CalleePre s b 0x10dd60 n n reserve) : (s.regValue .rdi).toNat + n < 2^32 :=
  h.outputBounded

theorem sourceDestinationDisjoint [Bindings] {s : RamState} {b : ReturnBoundary} {n reserve : Nat}
    (h : CalleePre s b 0x10dd60 n n reserve) :
    (s.regValue .rsi).toNat + n ≤ (s.regValue .rdi).toNat ∨
    (s.regValue .rdi).toNat + n ≤ (s.regValue .rsi).toNat := by
  have hd := h.separation ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  change (registerRegion s .rsi n).Disjoint (registerRegion s .rdi n) at hd
  by_cases hn : n = 0
  · omega
  by_cases hbefore : (s.regValue .rsi).toNat + n ≤ (s.regValue .rdi).toNat
  · exact .inl hbefore
  right
  apply Nat.le_of_not_lt
  intro hafter
  have hin : (registerRegion s .rsi n).Contains
      (max (s.regValue .rsi).toNat (s.regValue .rdi).toNat) := by
    dsimp only [registerRegion, MemoryRegion.Contains]
    omega
  apply hd _ hin
  dsimp only [registerRegion, MemoryRegion.Contains]
  omega

theorem CopyState.append [Bindings] {s t u : RamState} {b : ReturnBoundary}
    {n reserve count more : Nat} (hp : CalleePre s b 0x10dd60 n n reserve)
    (h : CopyState s t count) (hcount : count + more ≤ n)
    (hr : ReadyToStep u)
    (hs : u.regValue .rsi = t.regValue .rsi + BitVec.ofNat 64 more)
    (hd : u.regValue .rdi = t.regValue .rdi + BitVec.ofNat 64 more)
    (hc : ∀ i < more, u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
      t.external[t.regValue .rsi + BitVec.ofNat 64 i]?)
    (he : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (t.regValue .rdi) more, .rip] t u) :
    CopyState s u (count + more) := by
  have hsl := sourceLow hp
  have hdl := destinationLow hp
  have hsep := sourceDestinationDisjoint hp
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · rw [hs, h.rsi, add_ofNat_add_ofNat]
  · rw [hd, h.rdi, add_ofNat_add_ofNat]
  · intro i hi
    by_cases hold : i < count
    · refine (he.byte ?_).trans (h.copy i hold)
      intro c hmem hcover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> try exact hcover
      obtain ⟨j, hj, hjEq⟩ := hcover
      rw [h.rdi, add_ofNat_add_ofNat] at hjEq
      have hn := congrArg BitVec.toNat hjEq
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
      omega
    · have hb := hc (i-count) (by omega)
      rw [h.rdi, h.rsi, add_ofNat_add_ofNat, add_ofNat_add_ofNat,
        Nat.add_sub_cancel' (by omega)] at hb
      refine hb.trans (h.agrees.byte ?_)
      intro c hmem hcover
      simp only [copyComponents, registerComponents, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
        try exact hcover
      obtain ⟨j, hj, hjEq⟩ := hcover
      have hn := congrArg BitVec.toNat hjEq
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
      omega
  · refine (h.agrees.trans he).widen ?_ ?_
    · intro c hc hnm
      simp only [copyComponents, registerComponents, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
        (rfl | rfl | rfl | rfl | rfl) <;> simp_all [Component.isMem]
    · intro a c hc hcover
      refine ⟨.mem (s.regValue .rdi) (count+more), by simp [copyComponents], ?_⟩
      simp only [copyComponents, registerComponents, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
        (rfl | rfl | rfl | rfl | rfl) <;> try exact hcover.elim
      · obtain ⟨i, hi, rfl⟩ := hcover
        exact ⟨i, by omega, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := hcover
        exact ⟨count+i, by omega, by rw [h.rdi, add_ofNat_add_ofNat]⟩

theorem destinationContains [Bindings] {s : RamState} {b : ReturnBoundary}
    {n reserve i : Nat} (hp : CalleePre s b 0x10dd60 n n reserve) (hi : i < n) :
    (registerRegion s .rdi n).Contains (s.regValue .rdi + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add hp.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem CopyState.loaded [Bindings] {s t : RamState} {b : ReturnBoundary}
    {n reserve count : Nat} (hp : CalleePre s b 0x10dd60 n n reserve)
    (h : CopyState s t count) (hc : count ≤ n) : ProgramLoaded t := by
  intro address byte hb
  refine (h.agrees.byte ?_).trans (hp.loaded address byte hb)
  intro c hmem hcov
  simp only [copyComponents, registerComponents, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
    try exact hcov
  obtain ⟨i, hi, rfl⟩ := hcov
  exact hp.avoids (registerRegion s .rdi n) (by simp)
    _ (destinationContains hp (by omega)) (.inl ⟨byte, hb⟩)

theorem CopyState.sourceReadable [Bindings] {s t : RamState} {b : ReturnBoundary}
    {n reserve count more : Nat} (hp : CalleePre s b 0x10dd60 n n reserve)
    (h : CopyState s t count) (hc : count + more ≤ n) :
    MemReadable t (t.regValue .rsi) more := by
  have hl := sourceLow hp
  have htn : (t.regValue .rsi).toNat = (s.regValue .rsi).toNat + count := by
    rw [h.rsi, toNat_add_ofNat _ _ (by omega)]
  refine ⟨by omega, ?_⟩
  intro i hi
  rw [h.rsi, add_ofNat_add_ofNat]
  apply h.agrees.grow
  exact Option.isSome_iff_exists.mpr (hp.inputAllocated _
    (memoryRegion_contains_add (len := n) (i := count + i) hp.inputBounded
      (Nat.le_refl _) (Nat.le_refl _) (by omega)))

theorem CopyState.destinationReadable [Bindings] {s t : RamState} {b : ReturnBoundary}
    {n reserve count more : Nat} (hp : CalleePre s b 0x10dd60 n n reserve)
    (h : CopyState s t count) (hc : count + more ≤ n) :
    MemReadable t (t.regValue .rdi) more := by
  have hl := destinationLow hp
  have htn : (t.regValue .rdi).toNat = (s.regValue .rdi).toNat + count := by
    rw [h.rdi, toNat_add_ofNat _ _ (by omega)]
  refine ⟨by omega, ?_⟩
  intro i hi
  rw [h.rdi, add_ofNat_add_ofNat]
  apply h.agrees.grow
  exact Option.isSome_iff_exists.mpr
    (hp.outputAllocated _ (destinationContains hp (by omega)))

theorem CopyState.disjoint [Bindings] {s t : RamState} {b : ReturnBoundary}
    {n reserve count more : Nat} (hp : CalleePre s b 0x10dd60 n n reserve)
    (h : CopyState s t count) (hc : count + more ≤ n) :
    (t.regValue .rsi).toNat + more ≤ (t.regValue .rdi).toNat ∨
    (t.regValue .rdi).toNat + more ≤ (t.regValue .rsi).toNat := by
  have hsl := sourceLow hp
  have hdl := destinationLow hp
  have hsep := sourceDestinationDisjoint hp
  rw [h.rsi, h.rdi, toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]
  omega

theorem CopyState.destinationTables [Bindings] {s t : RamState} {b : ReturnBoundary}
    {n reserve count more : Nat} (hp : CalleePre s b 0x10dd60 n n reserve)
    (h : CopyState s t count) (hc : count + more ≤ n) (hpos : 0 < more) :
    (t.regValue .rdi).toNat + more ≤ 0x1000 ∨ 0x3000 ≤ (t.regValue .rdi).toNat := by
  apply Common.Machine.frames_of_not_reserved hpos (h.destinationReadable hp hc).low
  intro i hi hin
  have hcontains : (registerRegion s .rdi n).Contains
      (t.regValue .rdi + BitVec.ofNat 64 i).toNat := by
    rw [h.rdi, add_ofNat_add_ofNat]
    exact destinationContains hp (by omega)
  apply hp.avoids (registerRegion s .rdi n) (by simp) _ hcontains
  right
  exact hin

theorem CopyState.destinationCodeApart [Bindings] {s t : RamState} {b : ReturnBoundary}
    {n reserve count more : Nat} {p : BitVec 64} {bytes : List UInt8}
    (hp : CalleePre s b 0x10dd60 n n reserve)
    (h : CopyState s t count) (hc : count + more ≤ n)
    (hcode : ∀ i < bytes.length, InProgram (p + BitVec.ofNat 64 i)) :
    RangeApart (t.regValue .rdi) more p bytes.length := by
  intro i hi j hj he
  have hcontains : (registerRegion s .rdi n).Contains
      (t.regValue .rdi + BitVec.ofNat 64 i).toNat := by
    rw [h.rdi, add_ofNat_add_ofNat]
    exact destinationContains hp (by omega)
  exact hp.avoids (registerRegion s .rdi n) (by simp) _ hcontains
    (.inl (he ▸ hcode j hj))

end Sha2.Proofs.Common.Memory.Copy
