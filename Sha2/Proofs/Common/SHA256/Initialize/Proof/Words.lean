import Sha2.Proofs.Common.SHA256.Initialize.Proof.Semantics

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Initialize

variable {v : Sha2.Proofs.Wrapper.Variant}

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

theorem words_run [Bindings] (boundary : ReturnBoundary) (l : Layout v)
    (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram l.start l.bytes.length)
    (base : BitVec 64) (s : RamState) (ready : ReadyToStep s)
    (code : CodeIn (codeRange l.start l.bytes) s) (pre : Pre l base s)
    (i : Nat) (hi : i ≤ 4) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn (codeRange l.start l.bytes) t ∧ t.RIP = l.wordPC i ∧
      AgreesExcept (l.prefixComponents base i) s t ∧
      (∀ j : Fin 4, j.val < i →
        memLoad t.external (base + 64 + BitVec.ofNat 64 (8 * (l.words[j]).index.val)) 64 =
          packedWord (l.words[j]).index v) ∧
      ∀ j : Fin 4, j.val < i → (l.words[j]).loadConstant = true →
        (∀ k : Fin 4, j.val < k.val → k.val < i → (l.words[k]).loadConstant = true →
          (l.words[k]).register ≠ (l.words[j]).register) →
        (.reg ((l.words[j]).register.setWidth 5) : Operand 64).read t =
          packedWord (l.words[j]).index v := by
  induction i with
  | zero =>
    refine ⟨0, s, rfl, ready, code, ?_, AgreesExcept.refl _ _, ?_, ?_⟩
    · simpa [Layout.wordPC] using pre.rip
    · intro j hj; omega
    · intro j hj; omega
  | succ i ih =>
    obtain ⟨fuel, t, run, readyT, codeT, rip, frame, packed, constants⟩ := ih (by omega)
    let k : Fin 4 := ⟨i, by omega⟩
    have address : (l.words[k]).destination.read t =
        base + 64 + BitVec.ofNat 64 (8 * (l.words[k]).index.val) := by
      rw [Address.read_eq (l.prefix_register frame _ (fun j _ hj =>
        pre.valid.independentWords j k hj)), pre.addresses k]
    have preWord := pre.words k
    have addresses : (l.words[k]).destination.read t = (l.words[k]).destination.read s :=
      address.trans (pre.addresses k).symm
    have wordPre : (l.words[k]).Pre (l.wordPC i) t := by
      refine ⟨rip, preWord.valid, preWord.independent, ?_, ?_, ?_⟩
      · intro loading
        rw [l.prefix_register frame _ (fun j hj loaded =>
          pre.valid.preservedValues j k hj loaded loading)]
        exact preWord.value loading
      · rw [addresses]
        exact ⟨⟨preWord.writable.low, fun a ha => frame.grow _ (preWord.writable.mem a ha)⟩,
          preWord.writable.tables⟩
      · rw [addresses]
        exact preWord.apart
    have insideWord : BlockInProgram (l.wordPC i) (l.words[k]).bytes.length := by
      intro a ha
      change InProgram (l.start + BitVec.ofNat 64 (l.offset i) + BitVec.ofNat 64 a)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      apply inside
      have bound := l.offset_le (i + 1)
      rw [l.offset_succ k] at bound
      change l.offset i + (l.words[k]).bytes.length ≤ l.bytes.length at bound
      omega
    obtain ⟨count, u, step, readyU, _, result⟩ := WordStore.run boundary (l.wordPC i)
      (l.words[k]) outside insideWord t readyT (l.wordCode k codeT) wordPre
    have codeU : CodeIn (codeRange l.start l.bytes) u := result.codeIn (by
      apply Effect.avoids_codeRange
      intro c hc a len eq
      rw [WordStore.components, address] at hc
      cases loading : (l.words[k]).loadConstant <;>
        simp only [loading, Bool.false_eq_true, ↓reduceIte, List.nil_append,
          List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      · rcases hc with rfl | rfl
        · cases eq; exact Layout.mem_apart pre k
        · cases eq
      · rcases hc with rfl | rfl | rfl
        · cases eq
        · cases eq; exact Layout.mem_apart pre k
        · cases eq) codeT
    refine ⟨fuel + count, u, run.trans step, readyU, codeU, ?_, ?_, ?_, ?_⟩
    · exact result.rip.trans (l.wordPC_succ k)
    · apply ((frame.mono (l.prefixComponents_mono base k)).trans
        (WordStore.prefix_frame address result)).mono
      intro c hc
      exact (List.mem_append.mp hc).elim id id
    · intro j hj
      by_cases equal : j.val = i
      · have jk : j = k := Fin.ext equal
        subst j
        simpa only [address] using WordStore.written result
      · have before : j.val < i := by omega
        rw [WordStore.mem_unchanged result _ ?_]
        · exact packed j before
        · rw [address]
          apply RangeApart.offsets (base + 64)
          · have := (l.words[k]).index.isLt; omega
          · have := (l.words[j]).index.isLt; omega
          · have orderK : (l.words[k]).index.val = 3-i := pre.valid.order k
            have orderJ : (l.words[j]).index.val = 3-j.val := pre.valid.order j
            left
            omega
    · intro j hj loading last
      by_cases equal : j.val = i
      · have jk : j = k := Fin.ext equal
        subst j
        have loaded : (l.words[k.val]).loadConstant = true := loading
        have writes : (.reg ((l.words[k]).register.setWidth 5) : Operand 64).read u =
            packedWord (l.words[k]).index v ∧
            memLoad u.external ((l.words[k]).destination.read t) 64 =
              packedWord (l.words[k]).index v := by
          simpa [WordStore.effect, loaded, Write.AllHold, Operand.read] using result.writes
        exact writes.1
      · have before : j.val < i := by omega
        have unchanged : (.reg ((l.words[j]).register.setWidth 5) : Operand 64).read u =
            (.reg ((l.words[j]).register.setWidth 5) : Operand 64).read t := by
          apply result.agrees.read
          rw [WordStore.components]
          cases current : (l.words[k]).loadConstant
          · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append,
              List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self, not_false_eq_true]
          · simp only [↓reduceIte, List.singleton_append, List.mem_cons,
              List.not_mem_nil, or_false, Component.reg.injEq, reduceCtorEq, or_false]
            exact Ne.symm (register_ne (last k before (by dsimp [k]; omega) current))
        rw [unchanged]
        exact constants j before loading (fun a after processed loaded =>
          last a after (by omega) loaded)

end Sha2.Proofs.Common.SHA256.Initialize
