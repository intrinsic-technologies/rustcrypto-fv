import Md5.Proofs.Block.Rounds.Interface
import Md5.Proofs.Block.Rounds.Program
import Md5.Proofs.Block.Rounds.Projection

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

private theorem loopComponents_covers {stack address : BitVec 64} {c : Component}
    (hc : c ∈ loopComponents stack) (hCov : c.Covers address) :
    ∃ i < 136, address = stack + BitVec.ofNat 64 i := by
  simp only [loopComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hCov.elim
  · obtain ⟨i, hi, he⟩ := hCov
    exact ⟨i, by omega, he⟩
  · obtain ⟨i, hi, he⟩ := hCov
    refine ⟨112 + i, by omega, ?_⟩
    change address = stack + BitVec.ofNat 64 112 + BitVec.ofNat 64 i at he
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

theorem LoopData.input_byte_of_agrees {stack input : BitVec 64}
    {buffer : Standards.RFC.MD5.Buffer} {words : Vector (BitVec 32) 16} {s t : RamState}
    (h : LoopData stack input buffer words s)
    (ha : AgreesExcept (loopComponents stack) s t) {i : Nat} (hi : i < 64) :
    t.external[input + BitVec.ofNat 64 i]? = s.external[input + BitVec.ofNat 64 i]? := by
  apply ha.byte
  intro c hc hCov
  obtain ⟨j, hj, he⟩ := loopComponents_covers hc hCov
  exact h.apart j hj i hi he.symm

theorem LoopData.of_agrees {stack input : BitVec 64}
    {buffer : Standards.RFC.MD5.Buffer} {words : Vector (BitVec 32) 16} {s t : RamState}
    (h : LoopData stack input buffer words s)
    (ha : AgreesExcept (loopComponents stack) s t) :
    LoopData stack input (Rounds.readWordBuffer (Rounds.readMachineWord stack input t)) words t := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_, ?_,
    ⟨h.frame.low, fun i hi ↦ ha.grow _ (h.frame.bytes i hi), h.frame.tables⟩,
    ⟨h.readable.low, fun i hi ↦ ha.grow _ (h.readable.mem i hi)⟩, ?_, h.apart, h.code⟩
  · exact (ha.read (r := 4) (n := 64) (by simp [loopComponents])).trans h.stackPointer
  · exact (ha.read (r := 6) (n := 64) (by simp [loopComponents])).trans h.inputPointer
  · intro i
    apply Eq.trans _ (h.inputWords i)
    apply memLoad_congr
    intro j hj
    change (t.external[input + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 j]?).getD 0 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      h.input_byte_of_agrees ha (by have := i.isLt; omega)]
    rfl

theorem LoopData.codeIn_of_agrees {stack input : BitVec 64}
    {buffer : Standards.RFC.MD5.Buffer} {words : Vector (BitVec 32) 16} {s t : RamState}
    (h : LoopData stack input buffer words s)
    (ha : AgreesExcept (loopComponents stack) s t)
    (hc : CodeIn Extracted.programImage s) : CodeIn Extracted.programImage t := by
  apply CodeIn.of_agreesExcept ha _ hc
  intro x hx c hc hCov
  obtain ⟨i, hi, he⟩ := loopComponents_covers hc hCov
  exact h.code i hi (he ▸ ⟨x.2, hx⟩)

namespace Rounds

theorem effect_single_agrees {s t : RamState} {e : Effect} {w : Write}
    (he : e.Holds s t) (hw : e.writes = [w]) :
    AgreesExcept [w.component, .flags, .rip] s t := by
  apply he.agrees.mono
  intro c hc
  cases hf : e.flags with
  | none =>
    have hc' : c = w.component ∨ c = .rip := by
      simpa [Effect.components, hw, hf] using hc
    rcases hc' with rfl | rfl <;> simp
  | some flags => simpa [Effect.components, hw, hf] using hc

private theorem loopComponents_reg (stack : BitVec 64) {dst : Nat}
    (hBound : dst < 16) (hSp : dst ≠ 4) (hSi : dst ≠ 6) :
    Component.reg (BitVec.ofNat 5 dst) ∈ loopComponents stack := by
  have hd : dst = 0 ∨ dst = 1 ∨ dst = 2 ∨ dst = 3 ∨ dst = 5 ∨ dst = 7 ∨
      dst = 8 ∨ dst = 9 ∨ dst = 10 ∨ dst = 11 ∨ dst = 12 ∨ dst = 13 ∨
      dst = 14 ∨ dst = 15 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loopComponents]

theorem effect_agrees_loop_reg {stack : BitVec 64} {s t : RamState} {e : Effect}
    {dst : Nat} {value : BitVec 64} (he : e.Holds s t)
    (hw : e.writes = [⟨.reg (BitVec.ofNat 5 dst), value⟩])
    (hBound : dst < 16) (hSp : dst ≠ 4) (hSi : dst ≠ 6) :
    AgreesExcept (loopComponents stack) s t := by
  apply (effect_single_agrees he hw).mono
  intro c hc
  simp only [Write.component_reg, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact loopComponents_reg stack hBound hSp hSi
  · simp [loopComponents]
  · simp [loopComponents]

private theorem loopComponents_scratch {stack address : BitVec 64} {offset length : Nat}
    (hBound : offset + length ≤ 96 ∨ 112 ≤ offset ∧ offset + length ≤ 136)
    (hCov : (Component.mem (stack + BitVec.ofNat 64 offset) length).Covers address) :
    ∃ c ∈ loopComponents stack, c.Covers address := by
  obtain ⟨i, hi, he⟩ := hCov
  rcases hBound with hBound | ⟨hLow, hBound⟩
  · refine ⟨.mem stack 96, by simp [loopComponents], offset + i, by omega, ?_⟩
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he
  · refine ⟨.mem (stack + 112) 24, by simp [loopComponents], offset + i - 112,
      by omega, ?_⟩
    change address = stack + BitVec.ofNat 64 112 + BitVec.ofNat 64 (offset + i - 112)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 112 + (offset + i - 112) = offset + i by omega]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

theorem effect_agrees_loop_stack {stack : BitVec 64} {s t : RamState} {e : Effect}
    {dst n : Nat} {value : BitVec n} (he : e.Holds s t)
    (hw : e.writes = [⟨.mem (stack + BitVec.ofNat 64 dst), value⟩])
    (hBound : dst + n / 8 ≤ 96 ∨ 112 ≤ dst ∧ dst + n / 8 ≤ 136) :
    AgreesExcept (loopComponents stack) s t := by
  apply (effect_single_agrees he hw).widen
  · intro c hc hn
    simp only [Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · contradiction
    · simp [loopComponents]
    · simp [loopComponents]
  · intro x c hc hCov
    simp only [Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact loopComponents_scratch hBound hCov
    · exact hCov.elim
    · exact hCov.elim

end Rounds
end Md5.Proofs.Block
