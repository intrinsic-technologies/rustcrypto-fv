import Sha1.Proofs.Compress.Machine.Interface
import Sha1.Proofs.Compress.Machine.Memory

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program Standards.NIST

structure FrameData (stack input : BitVec 64) (M : Vector (BitVec 32) 16) (s : RamState) : Prop where
  stackPointer : stackPtr s = stack
  writable : MemWritable s stack 160
  readable : MemReadable s input 64
  words : ∀ i : Fin 16,
    (Operand.mem (input + BitVec.ofNat 64 (4 * i.val)) : Operand 32).read s = bswapSpec M[i]
  apart : RangeApart stack 160 input 64
  code : ∀ i < 160, ¬ InProgram (stack + BitVec.ofNat 64 i)

theorem scratchComponents_covers {stack address : BitVec 64} {c : Component}
    (hc : c ∈ scratchComponents stack) (hCov : c.Covers address) :
    ∃ i < 160, address = stack + BitVec.ofNat 64 i := by
  simp only [scratchComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hCov.elim
  · obtain ⟨i, hi, he⟩ := hCov
    exact ⟨i, by omega, he⟩
  · obtain ⟨i, hi, he⟩ := hCov
    refine ⟨144 + i, by omega, ?_⟩
    change address = stack + BitVec.ofNat 64 144 + BitVec.ofNat 64 i at he
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

theorem FrameData.input_byte_of_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (h : FrameData stack input M s)
    (ha : AgreesExcept (scratchComponents stack) s t) {i : Nat} (hi : i < 64) :
    t.external[input + BitVec.ofNat 64 i]? = s.external[input + BitVec.ofNat 64 i]? := by
  apply ha.byte
  intro c hc hCov
  obtain ⟨j, hj, he⟩ := scratchComponents_covers hc hCov
  exact h.apart j hj i hi he.symm

theorem FrameData.of_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (h : FrameData stack input M s)
    (ha : AgreesExcept (scratchComponents stack) s t) :
    FrameData stack input M t := by
  refine ⟨(ha.read (r := 4) (n := 64) (by simp [scratchComponents])).trans h.stackPointer,
    ⟨h.writable.low, fun i hi ↦ ha.grow _ (h.writable.mem i hi), h.writable.tables⟩,
    ⟨h.readable.low, fun i hi ↦ ha.grow _ (h.readable.mem i hi)⟩, ?_, h.apart, h.code⟩
  intro i
  apply Eq.trans _ (h.words i)
  apply memLoad_congr
  intro j hj
  change (t.external[input + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 j]?).getD 0 = _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    h.input_byte_of_agrees ha (by have := i.isLt; omega)]
  rfl

theorem FrameData.codeIn_of_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (h : FrameData stack input M s)
    (ha : AgreesExcept (scratchComponents stack) s t)
    (hc : CodeIn Extracted.programImage s) : CodeIn Extracted.programImage t := by
  apply CodeIn.of_agreesExcept ha _ hc
  intro x hx c hc hCov
  obtain ⟨i, hi, he⟩ := scratchComponents_covers hc hCov
  exact h.code i hi (he ▸ ⟨x.2, hx⟩)

theorem FrameData.of_blockData {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s : RamState}
    (h : BlockData stack input H M s) : FrameData stack input M s :=
  ⟨h.stackPointer, h.writable, h.readable, h.words, h.apart, h.code⟩

theorem FrameData.readable_input {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s : RamState}
    (h : FrameData stack input M s) (offset length : Nat) (hb : offset + length ≤ 64) :
    MemReadable s (input + BitVec.ofNat 64 offset) length :=
  memReadable_slice h.readable offset length hb

theorem FrameData.readable_stack {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s : RamState}
    (h : FrameData stack input M s) (offset length : Nat) (hb : offset + length ≤ 160) :
    MemReadable s (stack + BitVec.ofNat 64 offset) length :=
  memReadable_slice h.writable.readable offset length hb

theorem FrameData.store_stack {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s : RamState}
    (h : FrameData stack input M s) {p : BitVec 64} {codeLen offset length : Nat}
    {addr : RamState → BitVec 64} (hRip : s.RIP = p)
    (hAddr : addr s = stack + BitVec.ofNat 64 offset) (hBound : offset + length ≤ 160)
    (hCode : ∀ i < codeLen, InProgram (p + BitVec.ofNat 64 i)) :
    Sha1.Proofs.Common.Instructions.StorePre.StorePre p codeLen addr length s := by
  refine ⟨hRip, ?_, ?_⟩
  · rw [hAddr]
    exact memoryWritable_slice h.writable offset length hBound
  · rw [hAddr]
    intro i hi j hj he
    have ha : InProgram (stack + BitVec.ofNat 64 (offset + i)) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, he]
      exact hCode j hj
    exact h.code (offset + i) (by omega) ha

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

theorem scratchComponents_reg (stack : BitVec 64) {dst : Nat}
    (hBound : dst < 16) (hSp : dst ≠ 4) :
    Component.reg (BitVec.ofNat 5 dst) ∈ scratchComponents stack := by
  have hd : dst = 0 ∨ dst = 1 ∨ dst = 2 ∨ dst = 3 ∨ dst = 5 ∨ dst = 6 ∨
      dst = 7 ∨ dst = 8 ∨ dst = 9 ∨ dst = 10 ∨ dst = 11 ∨ dst = 12 ∨
      dst = 13 ∨ dst = 14 ∨ dst = 15 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [scratchComponents]

theorem effect_agrees_scratch_reg {stack : BitVec 64} {s t : RamState} {e : Effect}
    {dst : Nat} {value : BitVec 64} (he : e.Holds s t)
    (hw : e.writes = [⟨.reg (BitVec.ofNat 5 dst), value⟩])
    (hBound : dst < 16) (hSp : dst ≠ 4) :
    AgreesExcept (scratchComponents stack) s t := by
  apply (effect_single_agrees he hw).mono
  intro c hc
  simp only [Write.component_reg, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact scratchComponents_reg stack hBound hSp
  · simp [scratchComponents]
  · simp [scratchComponents]

theorem scratchComponents_stack {stack address : BitVec 64} {offset length : Nat}
    (hBound : offset + length ≤ 128 ∨ 144 ≤ offset ∧ offset + length ≤ 160)
    (hCov : (Component.mem (stack + BitVec.ofNat 64 offset) length).Covers address) :
    ∃ c ∈ scratchComponents stack, c.Covers address := by
  obtain ⟨i, hi, he⟩ := hCov
  rcases hBound with hBound | ⟨hLow, hBound⟩
  · refine ⟨.mem stack 128, by simp [scratchComponents], offset + i, by omega, ?_⟩
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he
  · refine ⟨.mem (stack + 144) 16, by simp [scratchComponents], offset + i - 144,
      by omega, ?_⟩
    change address = stack + BitVec.ofNat 64 144 + BitVec.ofNat 64 (offset + i - 144)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 144 + (offset + i - 144) = offset + i by omega]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

theorem effect_agrees_scratch_stack {stack : BitVec 64} {s t : RamState} {e : Effect}
    {dst n : Nat} {value : BitVec n} (he : e.Holds s t)
    (hw : e.writes = [⟨.mem (stack + BitVec.ofNat 64 dst), value⟩])
    (hBound : dst + n / 8 ≤ 128 ∨ 144 ≤ dst ∧ dst + n / 8 ≤ 160) :
    AgreesExcept (scratchComponents stack) s t := by
  apply (effect_single_agrees he hw).widen
  · intro c hc hn
    simp only [Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · contradiction
    · simp [scratchComponents]
    · simp [scratchComponents]
  · intro x c hc hCov
    simp only [Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact scratchComponents_stack hBound hCov
    · exact hCov.elim
    · exact hCov.elim

end Sha1.Proofs.Compress.Machine
