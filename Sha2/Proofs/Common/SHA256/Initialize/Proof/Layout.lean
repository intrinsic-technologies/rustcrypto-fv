import Sha2.Proofs.Common.SHA256.Initialize.Proof.WordStore
import Sha2.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Initialize

variable {v : Sha2.Proofs.Wrapper.Variant}

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

abbrev Layout.prefix (l : Layout v) (i : Nat) : List (WordStore v) := l.words.toArray.toList.take i

def Layout.offset (l : Layout v) (i : Nat) : Nat :=
  ((l.prefix i).map WordStore.bytes |>.map List.length |>.sum)

def Layout.prefixComponents (l : Layout v) (base : BitVec 64) (i : Nat) : List Component :=
  ((l.prefix i).filter WordStore.loadConstant).map (fun b => .reg (b.register.setWidth 5)) ++
    [.mem (base + 64) 32, .rip]

theorem Layout.prefix_succ (l : Layout v) (i : Fin 4) :
    l.prefix (i.val + 1) = l.prefix i.val ++ [l.words[i]] := by
  simpa [Layout.prefix, ← Vector.getElem_toArray] using List.take_succ_eq_append_getElem
    (l := l.words.toArray.toList) (i := i.val) (by simp)

theorem Layout.offset_succ (l : Layout v) (i : Fin 4) :
    l.offset (i.val + 1) = l.offset i.val + (l.words[i]).bytes.length := by
  simp [Layout.offset, l.prefix_succ i]

theorem Layout.bytes_split (l : Layout v) (i : Nat) :
    l.bytes = (l.prefix i).flatMap WordStore.bytes ++
      (l.words.toArray.toList.drop i).flatMap WordStore.bytes ++ l.clear.bytes := by
  rw [Layout.bytes, ← List.flatMap_append, List.take_append_drop]

theorem Layout.offset_le (l : Layout v) (i : Nat) : l.offset i ≤ l.bytes.length := by
  rw [l.bytes_split i]
  simp only [List.length_append, List.length_flatMap, Layout.offset, List.map_map, Function.comp_def]
  omega

theorem Layout.wordPC_succ (l : Layout v) (i : Fin 4) :
    l.wordPC i.val + BitVec.ofNat 64 (l.words[i]).bytes.length = l.wordPC (i.val + 1) := by
  change l.start + BitVec.ofNat 64 (l.offset i.val) + _ =
    l.start + BitVec.ofNat 64 (l.offset (i.val + 1))
  rw [l.offset_succ i, BitVec.ofNat_add, BitVec.add_assoc]

theorem Layout.wordCode (l : Layout v) (i : Fin 4) {s : RamState}
    (code : CodeIn (codeRange l.start l.bytes) s) :
    CodeIn (codeRange (l.wordPC i.val) (l.words[i]).bytes) s := by
  apply code.mono
  rw [l.bytes_split (i.val + 1), l.prefix_succ i, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.append_assoc, List.append_assoc, codeRange_append l.start ((l.prefix i.val).flatMap WordStore.bytes)]
  rw [codeRange_append (l.start + _ ) (l.words[i]).bytes]
  change ∀ x ∈ codeRange (l.wordPC i.val) (l.words[i]).bytes,
    x ∈ _ ++ (_ ++ _)
  intro x h
  apply List.mem_append_right
  apply List.mem_append_left
  simpa only [Layout.wordPC, List.length_flatMap, List.map_map, Function.comp_def] using h

theorem Layout.prefix_member (l : Layout v) {i : Nat} {b : WordStore v}
    (h : b ∈ l.prefix i) : ∃ j : Fin 4, j.val < i ∧ l.words[j] = b := by
  obtain ⟨j, hj, hb⟩ := List.mem_take_iff_getElem.mp h
  have hjSmall : j < i := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
  have hjFour : j < 4 := by simpa using Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
  refine ⟨⟨j, hjFour⟩, hjSmall, ?_⟩
  exact hb

theorem Layout.prefix_register {l : Layout v} {base : BitVec 64} {i : Nat} {s t : RamState}
    (frame : AgreesExcept (l.prefixComponents base i) s t) (r : BitVec 4)
    (independent : ∀ j : Fin 4, j.val < i → (l.words[j]).loadConstant = true →
      (l.words[j]).register ≠ r) :
    (.reg (r.setWidth 5) : Operand 64).read t = (.reg (r.setWidth 5) : Operand 64).read s := by
  apply frame.read
  simp only [Layout.prefixComponents, List.mem_append, List.mem_map,
    List.mem_filter, List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq,
    reduceCtorEq, or_false, not_exists, not_and]
  intro b ⟨member, loading⟩ equal
  obtain ⟨j, hj, rfl⟩ := l.prefix_member member
  exact register_ne (independent j hj loading) equal

end Sha2.Proofs.Common.SHA256.Initialize
