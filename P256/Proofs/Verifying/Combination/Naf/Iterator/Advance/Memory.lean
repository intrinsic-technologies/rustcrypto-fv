import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Prologue
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Guard
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Shift
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Select
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Full
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Empty

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

def coreComponents (a : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .flags, .rip,
    .mem a 8, .mem (a+8) 8, .mem (a+16) 8, .mem (a+24) 8, .mem (a+32) 8]

theorem core_frame {s t : RamState} {a : BitVec 64}
    (bounded : (⟨a.toNat,40⟩ : MemoryRegion).Bounded)
    (agrees : AgreesExcept (coreComponents a) s t) :
    MemoryWriteFrame s t #v[(⟨a.toNat,40⟩ : MemoryRegion)] := by
  apply agrees.memoryWriteFrame
  intro c hc address cover
  simp only [coreComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals obtain ⟨i, hi, rfl⟩ := cover
  all_goals refine ⟨⟨a.toNat,40⟩, by simp, ?_⟩
  · exact memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) (by change i < 40; omega)
  · have h := memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) (i := 8+i) (by change 8+i < 40; omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h
  · have h := memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) (i := 16+i) (by change 16+i < 40; omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h
  · have h := memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) (i := 24+i) (by change 24+i < 40; omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h
  · have h := memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) (i := 32+i) (by change 32+i < 40; omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h

theorem source_preserved {s t : RamState} {a source : BitVec 64} {n : Nat}
    (input : Nat256At s source n)
    (bounded : (⟨source.toNat,32⟩ : MemoryRegion).Bounded)
    (apart : (⟨source.toNat,32⟩ : MemoryRegion).Disjoint (⟨a.toNat,40⟩ : MemoryRegion))
    (frame : MemoryWriteFrame s t #v[(⟨a.toNat,40⟩ : MemoryRegion)]) : Nat256At t source n := by
  refine ⟨input.1, fun i hi => ?_⟩
  rw [frame _]
  · exact input.2 i hi
  · intro region hr hin
    have eq : region = (⟨a.toNat,40⟩ : MemoryRegion) := by simpa using hr
    subst region
    exact apart _ (memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi) hin

theorem state_of_external {s t : RamState} {a source : BitVec 64} {n k : Nat}
    (state : StateAt s a source n k) (mem : t.external = s.external) : StateAt t a source n k := by
  constructor
  · rw [mem]; exact state.pointer
  · rw [mem]; exact state.remaining
  · rw [mem]; exact state.index
  · rw [mem]; exact state.low
  · rw [mem]; exact state.high

theorem shift_read {s t : RamState} (effect : (shiftEffect s).Holds s t) (kept : BitVec 64)
    (h16 : OffsetsApart 16 8 kept 8) (h24 : OffsetsApart 24 8 kept 8) :
    memLoad t.external (s.regValue .rdi + kept) 64 = memLoad s.external (s.regValue .rdi + kept) 64 := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees effect.agrees
  intro i hi c hc cover
  simp only [shiftEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
    Operand.component, List.append_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨j,hj,eq⟩ := cover
    exact h16.ne (s.regValue .rdi) hj hi (by decide) eq.symm
  · obtain ⟨j,hj,eq⟩ := cover
    exact h24.ne (s.regValue .rdi) hj hi (by decide) eq.symm
  all_goals exact cover.elim

theorem full_read {s t : RamState} (effect : (fullEffect s).Holds s t) (kept : BitVec 64)
    (h32 : OffsetsApart 32 8 kept 8) (h0 : OffsetsApart 0 8 kept 8)
    (h8 : OffsetsApart 8 8 kept 8) :
    memLoad t.external (s.regValue .rdi + kept) 64 = memLoad s.external (s.regValue .rdi + kept) 64 := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees effect.agrees
  intro i hi c hc cover
  simp only [fullEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
    Operand.component, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨j,hj,eq⟩ := cover
    exact h32.ne (s.regValue .rdi) hj hi (by decide) eq.symm
  · obtain ⟨j,hj,eq⟩ := cover
    exact h0.ne (s.regValue .rdi) hj hi (by decide) (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using eq.symm)
  · obtain ⟨j,hj,eq⟩ := cover
    exact h8.ne (s.regValue .rdi) hj hi (by decide) eq.symm
  all_goals exact cover.elim

theorem empty_read {s t : RamState} (effect : (emptyEffect s).Holds s t) (kept : BitVec 64)
    (h32 : OffsetsApart 32 8 kept 8) :
    memLoad t.external (s.regValue .rdi + kept) 64 = memLoad s.external (s.regValue .rdi + kept) 64 := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees effect.agrees
  intro i hi c hc cover
  simp only [emptyEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
    Operand.component, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · obtain ⟨j,hj,eq⟩ := cover
    exact h32.ne (s.regValue .rdi) hj hi (by decide) eq.symm
  all_goals exact cover.elim

theorem word_four {n : Nat} (bound : n < 2^256) : word n 4 = 0 := by
  unfold word
  rw [show 64*4=256 from rfl, Nat.div_eq_of_lt bound]
  rfl

end P256.Proofs.Verifying.Combination.Naf.Iterator.Advance
