import Md5.Proofs.Block.Rounds.Interface
import Md5.Proofs.Block.Bytes
import Md5.Proofs.Block.Preconditions

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem loopComponents_covers {stack address : BitVec 64} {c : Component}
    (hc : c ∈ loopComponents stack) (h : c.Covers address) :
    (Component.mem stack 0x88).Covers address := by
  simp only [loopComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> try exact False.elim h
  · obtain ⟨i, hi, he⟩ := h
    exact ⟨i, by omega, he⟩
  · obtain ⟨i, hi, he⟩ := h
    refine ⟨112 + i, by omega, ?_⟩
    simpa [BitVec.add_assoc, BitVec.ofNat_add] using he

theorem bytes_of_loop_frame {s t : RamState} {stack base : BitVec 64} {len : Nat}
    {value : Nat → UInt8} (h : Bytes s.external base len value)
    (hFrame : AgreesExcept (loopComponents stack) s t)
    (hApart : RangeApart stack 0x88 base len) : Bytes t.external base len value := by
  apply h.of_agreesExcept hFrame
  intro i hi c hc hCovers
  obtain ⟨j, hj, he⟩ := loopComponents_covers hc hCovers
  exact hApart j hj i hi he.symm

theorem loopComponents_control_apart (stack : BitVec 64) (i : Nat) (hi : i < 16) :
    ∀ c ∈ loopComponents stack, ¬ c.Covers (stack + 96 + BitVec.ofNat 64 i) := by
  intro c hc hCovers
  simp only [loopComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> try exact False.elim hCovers
  · obtain ⟨j, hj, he⟩ := hCovers
    have ha := RangeApart.offsets stack (a := 0) (b := 96) (len := 96) (count := 16)
      (by decide +kernel) (by decide +kernel) (.inl (by decide +kernel))
    apply ha j hj i hi
    simpa using he.symm
  · obtain ⟨j, hj, he⟩ := hCovers
    have ha := RangeApart.offsets stack (a := 112) (b := 96) (len := 24) (count := 16)
      (by decide +kernel) (by decide +kernel) (.inr (by decide +kernel))
    apply ha j hj i hi
    simpa using he.symm

theorem controlBytes_of_loop_frame {s t : RamState} {stack : BitVec 64}
    {value : Nat → UInt8} (h : Bytes s.external (stack + 96) 16 value)
    (hFrame : AgreesExcept (loopComponents stack) s t) :
    Bytes t.external (stack + 96) 16 value :=
  h.of_agreesExcept hFrame (loopComponents_control_apart stack)

theorem memLoad_control_of_loop_frame {s t : RamState} {stack : BitVec 64}
    (hFrame : AgreesExcept (loopComponents stack) s t) (offset : Nat)
    (hOffset : offset + 8 ≤ 16) :
    memLoad t.external (stack + 96 + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stack + 96 + BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
  apply hFrame.byte
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using
    loopComponents_control_apart stack (offset + i) (by omega)

end Md5.Proofs.Block
