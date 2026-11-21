import Sha2.Proofs.Common.SHA256.Initialize.Proof.Layout

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Initialize

variable {v : Sha2.Proofs.Wrapper.Variant}

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

theorem packedWord_eq (i : Fin 4) : packedWord i v =
    (packedWords v)[i.val]! := rfl

theorem WordStore.components (p : BitVec 64) (b : WordStore v) (s : RamState) :
    (b.effect p s).components =
      (if b.loadConstant then [.reg (b.register.setWidth 5)] else []) ++
      [.mem (b.destination.read s) 8, .rip] := by
  cases loading : b.loadConstant <;> simp [WordStore.effect, loading, Effect.components]

theorem WordStore.written {p : BitVec 64} {b : WordStore v} {s t : RamState}
    (result : (b.effect p s).Holds s t) :
    memLoad t.external (b.destination.read s) 64 = packedWord b.index v := by
  cases loading : b.loadConstant
  · simpa [WordStore.effect, loading, Write.AllHold, Operand.read] using result.writes
  · have writes : (.reg (b.register.setWidth 5) : Operand 64).read t = packedWord b.index v ∧
        memLoad t.external (b.destination.read s) 64 = packedWord b.index v := by
      simpa [WordStore.effect, loading, Write.AllHold, Operand.read] using result.writes
    exact writes.2

theorem WordStore.mem_unchanged {p : BitVec 64} {b : WordStore v} {s t : RamState}
    (result : (b.effect p s).Holds s t) (a : BitVec 64)
    (apart : RangeApart (b.destination.read s) 8 a 8) :
    memLoad t.external a 64 = memLoad s.external a 64 := by
  apply Sha2.Proofs.Common.Encoding.Serialize.read_mem_of_agrees result.agrees
  intro i hi c hc
  rw [WordStore.components] at hc
  cases loading : b.loadConstant <;> simp only [loading, Bool.false_eq_true,
    ↓reduceIte, List.nil_append, List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  · rcases hc with rfl | rfl
    · exact fun ⟨j, hj, heq⟩ => apart j hj i hi heq.symm
    · simp [Component.Covers]
  · rcases hc with rfl | rfl | rfl
    · simp [Component.Covers]
    · exact fun ⟨j, hj, heq⟩ => apart j hj i hi heq.symm
    · simp [Component.Covers]

theorem Layout.prefixComponents_mono (l : Layout v) (base : BitVec 64) (i : Fin 4) :
    ∀ c ∈ l.prefixComponents base i.val, c ∈ l.prefixComponents base (i.val + 1) := by
  simp only [Layout.prefixComponents, l.prefix_succ i, List.filter_append,
    List.map_append, List.mem_append]
  intro c member
  exact member.elim (fun h => .inl (.inl h)) Or.inr

theorem WordStore.prefix_frame {l : Layout v} {base : BitVec 64} {i : Fin 4}
    {p : BitVec 64} {s t : RamState}
    (address : (l.words[i]).destination.read s =
      base + 64 + BitVec.ofNat 64 (8 * (l.words[i]).index.val))
    (result : ((l.words[i]).effect p s).Holds s t) :
    AgreesExcept (l.prefixComponents base (i.val + 1)) s t := by
  apply result.agrees.widen
  · intro c hc hm
    rw [WordStore.components, address] at hc
    cases loading : (l.words[i]).loadConstant <;> simp only [loading, Bool.false_eq_true,
      ↓reduceIte, List.nil_append, List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    · rcases hc with rfl | rfl
      · simp [Component.isMem] at hm
      · simp [Layout.prefixComponents]
    · rcases hc with rfl | rfl | rfl
      · change (l.words[i.val]).loadConstant = true at loading
        simp [Layout.prefixComponents, l.prefix_succ i, loading]
      · simp [Component.isMem] at hm
      · simp [Layout.prefixComponents]
  · intro x c hc cover
    rw [WordStore.components, address] at hc
    cases loading : (l.words[i]).loadConstant <;> simp only [loading, Bool.false_eq_true,
      ↓reduceIte, List.nil_append, List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    · rcases hc with rfl | rfl <;> try simp [Component.Covers] at cover
      obtain ⟨j, hj, rfl⟩ := cover
      refine ⟨.mem (base + 64) 32, by simp [Layout.prefixComponents],
        8 * (l.words[i]).index.val + j, by have := (l.words[i]).index.isLt; omega, ?_⟩
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rfl
    · rcases hc with rfl | rfl | rfl <;> try simp [Component.Covers] at cover
      all_goals
        obtain ⟨j, hj, rfl⟩ := cover
        refine ⟨.mem (base + 64) 32, by simp [Layout.prefixComponents],
          8 * (l.words[i]).index.val + j, by have := (l.words[i]).index.isLt; omega, ?_⟩
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        rfl

theorem Layout.mem_apart {l : Layout v} {base : BitVec 64} {s : RamState}
    (pre : Pre l base s) (i : Fin 4) :
    RangeApart (base + 64 + BitVec.ofNat 64 (8 * (l.words[i]).index.val)) 8
      l.start l.bytes.length := by
  intro a ha b hb equal
  apply pre.codeApart (64 + 8 * (l.words[i]).index.val + a)
    (by have := (l.words[i]).index.isLt; omega) b hb
  simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using equal

end Sha2.Proofs.Common.SHA256.Initialize
