import Sha2.Proofs.Common.SHA256.Initialize.Proof.Clear
import Sha2.Proofs.Common.SHA256.Initialize.Proof.Layout

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Initialize

variable {v : Sha2.Proofs.Wrapper.Variant}

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

theorem Clear.mem_unchanged {p : BitVec 64} {b : Clear} {s t : RamState}
    (result : (b.effect p s).Holds s t) (a : BitVec 64)
    (counter : RangeApart (b.counter.read s) 8 a 8)
    (tail : RangeApart (b.tail.read s) 1 a 8) :
    memLoad t.external a 64 = memLoad s.external a 64 := by
  apply Sha2.Proofs.Common.Encoding.Serialize.read_mem_of_agrees result.agrees
  intro i hi c hc
  simp [Clear.effect, Effect.components] at hc
  rcases hc with rfl | rfl | rfl
  · exact fun ⟨j, hj, heq⟩ => counter j hj i hi heq.symm
  · exact fun ⟨j, hj, heq⟩ => tail j hj i hi heq.symm
  · simp [Component.Covers]

theorem Clear.avoids {p q : BitVec 64} {b : Clear} {s : RamState} {bytes : List UInt8}
    (counter : RangeApart (b.counter.read s) 8 q bytes.length)
    (tail : RangeApart (b.tail.read s) 1 q bytes.length) :
    (b.effect p s).Avoids (codeRange q bytes) := by
  apply Effect.avoids_codeRange
  simpa [Clear.effect, Effect.components] using And.intro counter tail

theorem Layout.clearBytes (l : Layout v) :
    l.bytes = (l.prefix 4).flatMap WordStore.bytes ++ l.clear.bytes := by
  simp [Layout.bytes, Layout.prefix, List.take_of_length_le]

theorem Layout.clearCode (l : Layout v) {s : RamState}
    (code : CodeIn (codeRange l.start l.bytes) s) :
    CodeIn (codeRange (l.wordPC 4) l.clear.bytes) s := by
  apply code.mono
  rw [l.clearBytes, codeRange_append]
  intro x hx
  apply List.mem_append_right
  simpa only [Layout.wordPC, List.length_flatMap, List.map_map, Function.comp_def] using hx

theorem Layout.clear_finish (l : Layout v) :
    l.wordPC 4 + BitVec.ofNat 64 l.clear.bytes.length = l.finish := by
  rw [Layout.finish, l.clearBytes, List.length_append, BitVec.ofNat_add, ← BitVec.add_assoc]
  congr 1
  simp only [Layout.wordPC, List.length_flatMap, List.map_map, Function.comp_def]

theorem Layout.offset_clear (l : Layout v) :
    l.offset 4 + l.clear.bytes.length = l.bytes.length := by
  rw [l.clearBytes, List.length_append, List.length_flatMap]
  simp only [Layout.offset, List.map_map, Function.comp_def]

theorem Layout.prefix_all (l : Layout v) : l.prefix 4 = l.words.toArray.toList := by
  apply List.take_of_length_le
  simp

end Sha2.Proofs.Common.SHA256.Initialize
