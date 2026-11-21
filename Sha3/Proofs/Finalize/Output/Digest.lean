import Sha3.Proofs.Finalize.Output.Blocks
import Sha3.Proofs.LaneMemory

namespace X86Proofs
open X86 X86.Machine

theorem memLoad32_eq_setWidth_memLoad64 (m : Ram) (address : BitVec 64) :
    memLoad m address 32 = (memLoad m address 64).setWidth 32 := by
  apply storedByte_injective (by decide)
  intro i hi
  have hwidth : 8 * i + 8 ≤ 32 := by omega
  have he : storedByte ((memLoad m address 64).setWidth 32) i =
      storedByte (memLoad m address 64) i := by
    simp only [storedByte_eq_extract, BitVec.extractLsb'_setWidth_of_le hwidth]
  rw [he, storedByte_memLoad m address i hi, storedByte_memLoad m address i (by omega)]
end X86Proofs

namespace Sha3.Proofs.Finalize.Output

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def outputChanges (out : BitVec 64) (count : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .mem out count, .rip]

theorem outputChanges_stackLoad {sp out : BitVec 64} {count span : Nat} {s t : RamState}
    (h : AgreesExcept (outputChanges out count) s t)
    (hapart : RangeApart out count sp span) (offset width : Nat)
    (hwidth : offset + width / 8 ≤ span) :
    (Operand.mem (sp + BitVec.ofNat 64 offset) : Operand width).read t =
      (Operand.mem (sp + BitVec.ofNat 64 offset) : Operand width).read s := by
  apply memLoad_congr
  intro j hj
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [h.byte]
  intro c hc hcover
  simp only [outputChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact hcover
  · exact hcover
  · exact hcover
  · obtain ⟨i, hi, he⟩ := hcover
    apply hapart i hi (offset + j) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc] using he.symm
  · exact hcover

theorem outputChanges_stack {out : BitVec 64} {count : Nat} {s t : RamState}
    (h : AgreesExcept (outputChanges out count) s t) : stackPtr t = stackPtr s :=
  h.read (n := 64) (r := 4) (by simp [outputChanges])

theorem output224Effect_agrees {p ptr out : BitVec 64} {s t : RamState}
    (h : (output224Effect p ptr out s).Holds s t) :
    AgreesExcept (outputChanges out 28) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [output224Effect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [outputChanges]
    · cases hm
    · cases hm
    · cases hm
    · cases hm
    · simp [outputChanges]
  · intro address c hc hcover
    simp only [output224Effect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcover.elim
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 28, by simp [outputChanges], ⟨0 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 28, by simp [outputChanges], ⟨8 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 28, by simp [outputChanges], ⟨16 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 28, by simp [outputChanges], ⟨24 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · exact hcover.elim

theorem output256Effect_agrees {p ptr out : BitVec 64} {s t : RamState}
    (h : (output256Effect p ptr out s).Holds s t) :
    AgreesExcept (outputChanges out 32) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [output256Effect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [outputChanges]
    · simp [outputChanges]
    · cases hm
    · cases hm
    · cases hm
    · cases hm
    · simp [outputChanges]
  · intro address c hc hcover
    simp only [output256Effect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcover.elim
    · exact hcover.elim
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 32, by simp [outputChanges], ⟨0 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 32, by simp [outputChanges], ⟨8 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 32, by simp [outputChanges], ⟨16 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 32, by simp [outputChanges], ⟨24 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · exact hcover.elim

theorem output384Effect_agrees {p ptr out : BitVec 64} {s t : RamState}
    (h : (output384Effect p ptr out s).Holds s t) :
    AgreesExcept (outputChanges out 48) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [output384Effect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [outputChanges]
    · simp [outputChanges]
    · cases hm
    · cases hm
    · cases hm
    · cases hm
    · cases hm
    · cases hm
    · simp [outputChanges]
  · intro address c hc hcover
    simp only [output384Effect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcover.elim
    · exact hcover.elim
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 48, by simp [outputChanges], ⟨0 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 48, by simp [outputChanges], ⟨8 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 48, by simp [outputChanges], ⟨16 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 48, by simp [outputChanges], ⟨24 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 48, by simp [outputChanges], ⟨32 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 48, by simp [outputChanges], ⟨40 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · exact hcover.elim

theorem output512Effect_agrees {p ptr out : BitVec 64} {s t : RamState}
    (h : (output512Effect p ptr out s).Holds s t) :
    AgreesExcept (outputChanges out 64) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [output512Effect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [outputChanges]
    · simp [outputChanges]
    · cases hm
    · cases hm
    · cases hm
    · cases hm
    · cases hm
    · cases hm
    · cases hm
    · cases hm
    · simp [outputChanges]
  · intro address c hc hcover
    simp only [output512Effect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcover.elim
    · exact hcover.elim
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 64, by simp [outputChanges], ⟨0 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 64, by simp [outputChanges], ⟨8 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 64, by simp [outputChanges], ⟨16 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 64, by simp [outputChanges], ⟨24 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 64, by simp [outputChanges], ⟨32 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 64, by simp [outputChanges], ⟨40 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 64, by simp [outputChanges], ⟨48 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem out 64, by simp [outputChanges], ⟨56 + i, by omega, ?_⟩⟩
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Nat.zero_add,
        BitVec.ofNat_eq_ofNat] using he
    · exact hcover.elim

theorem digestBytes_of_chunkLoads {s t : RamState} {out : BitVec 64}
    (a : Keccak.Lanes) (n : Nat) (hn : n ≤ 200)
    (hagrees : ∀ address : BitVec 64, (s.external[address]?).isSome → (t.external[address]?).isSome)
    (halloc : MemReadable s out n)
    (hloads : ∀ k (hk : 8 * k < n),
      memLoad t.external (out + BitVec.ofNat 64 (8 * k)) (8 * min 8 (n - 8 * k)) =
        (a ⟨k, by omega⟩).setWidth (8 * min 8 (n - 8 * k))) :
    ∀ i : Fin n, t.external[out + BitVec.ofNat 64 i.val]? =
      some (Absorption.digestLanes a n hn)[i.val] := by
  have hbytes : ∀ i < n, (t.external[out + BitVec.ofNat 64 i]?).isSome :=
    fun i hi ↦ hagrees _ (halloc.mem i hi)
  intro i
  have h := Bytes.of_isSome hbytes i.val i.isLt
  dsimp only at h
  rw [LaneMemory.memByte_eq_digestLanes_of_chunkLoads _ _ a n hn hloads i.val i.isLt] at h
  exact h

theorem digestBytes_of_copy {s t : RamState} {ptr out : BitVec 64}
    (a : Keccak.Lanes) (n : Nat) (hn : n ≤ 200)
    (hsource : MemReadable s ptr n) (hlanes : Permutation.memoryLanes ptr s = a)
    (hcopy : ∀ i < n, t.external[out + BitVec.ofNat 64 i]? =
      s.external[ptr + BitVec.ofNat 64 i]?) :
    ∀ i : Fin n, t.external[out + BitVec.ofNat 64 i.val]? =
      some (Absorption.digestLanes a n hn)[i.val] := by
  intro i
  rw [hcopy i.val i.isLt]
  have h := Bytes.of_isSome hsource.mem i.val i.isLt
  have hb := LaneMemory.storedByte_memoryLanes ptr s
    ⟨i.val / 8, by omega⟩ ⟨i.val % 8, by omega⟩
  have hi : 8 * (i.val / 8) + i.val % 8 = i.val := by omega
  simp only [hi, hlanes] at hb
  rw [LaneMemory.getElem_digestLanes_eq_storedByte a n hn i.val i.isLt, hb]
  exact h

theorem output224Effect_digest {p ptr out : BitVec 64} {s t : RamState}
    (a : Keccak.Lanes) (h : (output224Effect p ptr out s).Holds s t)
    (halloc : MemReadable s out 28) (hlanes : Permutation.memoryLanes ptr s = a) :
    ∀ i : Fin 28, t.external[out + BitVec.ofNat 64 i.val]? =
      some (Absorption.digestLanes a 28 (by decide))[i.val] := by
  have hall := h.writes
  simp only [output224Effect, Write.AllHold, ← memLoad_external] at hall
  obtain ⟨hr0, hw0, hw1, hw2, hw3⟩ := hall
  have hlane (i : Fin 25) :
      memLoad s.external (ptr + BitVec.ofNat 64 (8 * i.val)) 64 = a i := by
    simpa only [Permutation.memoryLanes, ← memLoad_external] using congrFun hlanes i
  apply digestBytes_of_chunkLoads a 28 (by decide) h.agrees.grow halloc
  intro k hk
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkCases with rfl | rfl | rfl | rfl
  · have hl := hlane ⟨0, by decide⟩
    simp only [Nat.reduceMul, BitVec.add_zero] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw0.trans hl
  · have hl := hlane ⟨1, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw1.trans hl
  · have hl := hlane ⟨2, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw2.trans hl
  · change memLoad t.external (out + 24) 32 = _
    rw [hw3, memLoad32_eq_setWidth_memLoad64]
    have hl := hlane ⟨3, by decide⟩
    simp only [Nat.reduceMul] at hl
    exact congrArg (BitVec.setWidth 32) hl

theorem output256Effect_digest {p ptr out : BitVec 64} {s t : RamState}
    (a : Keccak.Lanes) (h : (output256Effect p ptr out s).Holds s t)
    (halloc : MemReadable s out 32) (hlanes : Permutation.memoryLanes ptr s = a) :
    ∀ i : Fin 32, t.external[out + BitVec.ofNat 64 i.val]? =
      some (Absorption.digestLanes a 32 (by decide))[i.val] := by
  have hall := h.writes
  simp only [output256Effect, Write.AllHold, ← memLoad_external] at hall
  obtain ⟨hr0, hr1, hw0, hw1, hw2, hw3⟩ := hall
  have hlane (i : Fin 25) :
      memLoad s.external (ptr + BitVec.ofNat 64 (8 * i.val)) 64 = a i := by
    simpa only [Permutation.memoryLanes, ← memLoad_external] using congrFun hlanes i
  apply digestBytes_of_chunkLoads a 32 (by decide) h.agrees.grow halloc
  intro k hk
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkCases with rfl | rfl | rfl | rfl
  · have hl := hlane ⟨0, by decide⟩
    simp only [Nat.reduceMul, BitVec.add_zero] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw0.trans hl
  · have hl := hlane ⟨1, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw1.trans hl
  · have hl := hlane ⟨2, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw2.trans hl
  · have hl := hlane ⟨3, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw3.trans hl

theorem output384Effect_digest {p ptr out : BitVec 64} {s t : RamState}
    (a : Keccak.Lanes) (h : (output384Effect p ptr out s).Holds s t)
    (halloc : MemReadable s out 48) (hlanes : Permutation.memoryLanes ptr s = a) :
    ∀ i : Fin 48, t.external[out + BitVec.ofNat 64 i.val]? =
      some (Absorption.digestLanes a 48 (by decide))[i.val] := by
  have hall := h.writes
  simp only [output384Effect, Write.AllHold, ← memLoad_external] at hall
  obtain ⟨hr0, hr1, hw0, hw1, hw2, hw3, hw4, hw5⟩ := hall
  have hlane (i : Fin 25) :
      memLoad s.external (ptr + BitVec.ofNat 64 (8 * i.val)) 64 = a i := by
    simpa only [Permutation.memoryLanes, ← memLoad_external] using congrFun hlanes i
  apply digestBytes_of_chunkLoads a 48 (by decide) h.agrees.grow halloc
  intro k hk
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hkCases with rfl | rfl | rfl | rfl | rfl | rfl
  · have hl := hlane ⟨0, by decide⟩
    simp only [Nat.reduceMul, BitVec.add_zero] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw0.trans hl
  · have hl := hlane ⟨1, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw1.trans hl
  · have hl := hlane ⟨2, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw2.trans hl
  · have hl := hlane ⟨3, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw3.trans hl
  · have hl := hlane ⟨4, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw4.trans hl
  · have hl := hlane ⟨5, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw5.trans hl

theorem output512Effect_digest {p ptr out : BitVec 64} {s t : RamState}
    (a : Keccak.Lanes) (h : (output512Effect p ptr out s).Holds s t)
    (halloc : MemReadable s out 64) (hlanes : Permutation.memoryLanes ptr s = a) :
    ∀ i : Fin 64, t.external[out + BitVec.ofNat 64 i.val]? =
      some (Absorption.digestLanes a 64 (by decide))[i.val] := by
  have hall := h.writes
  simp only [output512Effect, Write.AllHold, ← memLoad_external] at hall
  obtain ⟨hr0, hr1, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hall
  have hlane (i : Fin 25) :
      memLoad s.external (ptr + BitVec.ofNat 64 (8 * i.val)) 64 = a i := by
    simpa only [Permutation.memoryLanes, ← memLoad_external] using congrFun hlanes i
  apply digestBytes_of_chunkLoads a 64 (by decide) h.agrees.grow halloc
  intro k hk
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hkCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hl := hlane ⟨0, by decide⟩
    simp only [Nat.reduceMul, BitVec.add_zero] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw0.trans hl
  · have hl := hlane ⟨1, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw1.trans hl
  · have hl := hlane ⟨2, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw2.trans hl
  · have hl := hlane ⟨3, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw3.trans hl
  · have hl := hlane ⟨4, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw4.trans hl
  · have hl := hlane ⟨5, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw5.trans hl
  · have hl := hlane ⟨6, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw6.trans hl
  · have hl := hlane ⟨7, by decide⟩
    simp only [Nat.reduceMul] at hl
    simpa [Nat.min_def, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.setWidth_eq] using hw7.trans hl

end Sha3.Proofs.Finalize.Output
