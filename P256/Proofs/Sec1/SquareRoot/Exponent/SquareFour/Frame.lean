import P256.Proofs.Sec1.SquareRoot.Exponent.Frame
import P256.Proofs.Sec1.SquareRoot.Exponent.Preservation
import P256.Proofs.Field.Preserve
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Code
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def scratchOffset (i : Nat) : Prop :=
  (8 ≤ i ∧ i < 16) ∨ (0x10 ≤ i ∧ i < 0x78) ∨ (0x7c ≤ i ∧ i < 0x80) ∨
    (0x10 ≤ i ∧ i < 0x30) ∨ (0x2d0 ≤ i ∧ i < 0x2d8) ∨
    (0x2e8 ≤ i ∧ i < 0x2f8)

def components (base : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7,
    .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15,
    .flags, .rip, .mem (base + 8) 8, .mem (base + 0x10) 0x68,
    .mem (base + 0x7c) 4, .mem (base + 0x10) 32,
    .mem (base + 0x2d0) 8, .mem (base + 0x2e8) 16]

theorem covers_offset {base address : BitVec 64} {c : Component}
    (hc : c ∈ components base) (ha : c.Covers address) :
    ∃ i, scratchOffset i ∧ address = base + BitVec.ofNat 64 i := by
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim ha
  all_goals obtain ⟨i, hi, rfl⟩ := ha
  · refine ⟨8 + i, ?_, ?_⟩
    · unfold scratchOffset; omega
    · rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
  · refine ⟨0x10 + i, ?_, ?_⟩
    · unfold scratchOffset; omega
    · rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
  · refine ⟨0x7c + i, ?_, ?_⟩
    · unfold scratchOffset; omega
    · rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
  · refine ⟨0x10 + i, ?_, ?_⟩
    · unfold scratchOffset; omega
    · rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
  · refine ⟨0x2d0 + i, ?_, ?_⟩
    · unfold scratchOffset; omega
    · rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
  · refine ⟨0x2e8 + i, ?_, ?_⟩
    · unfold scratchOffset; omega
    · rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl

theorem scratchOffset_lt {i : Nat} (h : scratchOffset i) : i < 0x2f8 := by
  unfold scratchOffset at h
  omega

theorem byte_of_agrees {s t : RamState} {base : BitVec 64}
    (h : AgreesExcept (components base) s t) {i : Nat}
    (hi : i < 2^64) (hout : ¬ scratchOffset i) :
    t.external[base + BitVec.ofNat 64 i]? = s.external[base + BitVec.ofNat 64 i]? := by
  apply h.memory
  intro c hc hcover
  obtain ⟨j, hj, he⟩ := covers_offset hc hcover
  have hjlt : j < 2^64 := Nat.lt_trans (scratchOffset_lt hj) (by decide +kernel)
  have hnat := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp he)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hjlt] at hnat
  exact hout (hnat.symm ▸ hj)

theorem word_of_agrees {s t : RamState} {base : BitVec 64}
    (h : AgreesExcept (components base) s t) (offset : Nat)
    (hoff : offset + 8 < 2^64) (hout : ∀ i < 8, ¬ scratchOffset (offset + i)) :
    (Operand.mem (base + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (base + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, byte_of_agrees h (by omega) (hout i hi)]

theorem base_add_toNat [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) {offset : Nat} (hoff : offset ≤ 1416) :
    (exponentFrameBase s + BitVec.ofNat 64 offset).toNat =
      (s.regValue .rsp).toNat - 1416 + offset := by
  have hb := stack_bounds h.stack
  have hs := stack_sub_toNat h.stack (offset := 1416) (by decide)
  change (exponentFrameBase s).toNat = (s.regValue .rsp).toNat - 1416 at hs
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64)]
  apply Nat.mod_eq_of_lt
  change 1584 ≤ (s.regValue .rsp).toNat ∧ (s.regValue .rsp).toNat + 8 < 2^32 at hb
  omega

theorem writesWithin [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) :
    WritesWithin (components (exponentFrameBase s))
      #v[registerRegion s .rdi 32, Stack.region s 1584] := by
  intro c hc address ha
  obtain ⟨i, hi, rfl⟩ := covers_offset hc ha
  have hi' := scratchOffset_lt hi
  refine ⟨Stack.region s 1584, by simp, ?_⟩
  change (Stack.region s 1584).start ≤ _ ∧ _ <
    (Stack.region s 1584).start + (Stack.region s 1584).size
  rw [base_add_toNat h (by omega)]
  have hb := stack_bounds h.stack
  change 1584 ≤ (s.regValue .rsp).toNat ∧ (s.regValue .rsp).toNat + 8 < 2^32 at hb
  simp only [Stack.region]
  omega

theorem loaded_of_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hl : ProgramLoaded t)
    (ha : AgreesExcept (components (exponentFrameBase s)) t u) : ProgramLoaded u := by
  intro address byte hfetch
  rw [ha.memory address]
  · exact hl address byte hfetch
  · intro c hc hcover
    obtain ⟨region, hr, hin⟩ := writesWithin h c hc address hcover
    apply h.avoids region _ address hin (.inl ⟨byte, hfetch⟩)
    simpa using hr

theorem base_add_eq_sub [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) {offset : Nat} (hoff : offset ≤ 1416) :
    exponentFrameBase s + BitVec.ofNat 64 (1416 - offset) =
      s.regValue .rsp - BitVec.ofNat 64 offset := by
  apply BitVec.eq_of_toNat_eq
  rw [base_add_toNat h (by omega)]
  have hs := stack_sub_toNat h.stack (offset := offset) (by omega)
  change (s.regValue .rsp - BitVec.ofNat 64 offset).toNat =
    (s.regValue .rsp).toNat - offset at hs
  rw [hs]
  have hb := (stack_bounds h.stack).1
  change 1584 ≤ (s.regValue .rsp).toNat at hb
  omega

theorem frame_of_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hf : ExponentFrame s t)
    (hr : ReadyToStep u) (ha : AgreesExcept (components (exponentFrameBase s)) t u) :
    ExponentFrame s u := by
  refine ⟨?_, supportedMachine_of_ready_agrees hf.machine hr ha,
    bindingsSupported_of_ready_agrees hf.bindingsSupported hr ha,
    ha.directionFlagClear (by component_not_mem) hf.directionFlag,
    (ha.mxcsr (by component_not_mem)).trans hf.mxcsr,
    (ha.fcw (by component_not_mem)).trans hf.fp87,
    memoryWriteFrame_trans hf.frame (ha.memoryWriteFrame (writesWithin h)),
    loaded_of_agrees h hf.loaded ha,
    fun a hp => ha.grow a (hf.allocated a hp), ?_, ?_, ?_⟩
  · exact (ha.read (n := 64) (r := 4) (by simp [components])).trans hf.rsp
  · apply Eq.trans _ hf.returnAddress
    have he := word_of_agrees ha 1416 (by decide) (by unfold scratchOffset; omega)
    simpa only [show exponentFrameBase s + BitVec.ofNat 64 1416 = s.regValue .rsp from
      by simpa using base_add_eq_sub h (offset := 0) (by decide)] using he
  · intro i hi
    apply Eq.trans _ (hf.saved i hi)
    rw [← base_add_eq_sub h (by omega : 8 * (i + 1) ≤ 1416)]
    exact word_of_agrees ha _ (by omega) (by unfold scratchOffset; omega)
  · exact (word_of_agrees ha 0x2a0 (by decide) (by unfold scratchOffset; omega)).trans
      hf.outputPointer

theorem input_byte_of_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x)
    (ha : AgreesExcept (components (exponentFrameBase s)) t u) {i : Nat} (hi : i < 144) :
    u.external[s.regValue .rsi + BitVec.ofNat 64 i]? =
      t.external[s.regValue .rsi + BitVec.ofNat 64 i]? := by
  apply ha.memoryWriteFrame (writesWithin h)
  intro region hr
  have hin := memoryRegion_contains_add h.inputBounded
    (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : region = registerRegion s .rdi 32 ∨ region = Stack.region s 1584 := by
    simpa using hr
  rcases hr' with rfl | rfl
  · exact h.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ hin
  · exact h.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hin

theorem constants_of_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hc : ExponentConstants s t x)
    (ha : AgreesExcept (components (exponentFrameBase s)) t u) :
    ExponentConstants s u x := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hc.input.1.of_bytes_eq (fun i hi => input_byte_of_agrees h ha (by omega)), ?_⟩
    intro i hi
    have he := input_byte_of_agrees h ha (i := 32 + i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at he
    exact he.trans (hc.input.2 i hi)
  · intro i hi
    apply (hc.table i hi).of_bytes_eq
    intro j hj
    have he := byte_of_agrees ha (i := 0x338 + 32 * i + j) (by omega)
      (by unfold scratchOffset; omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc] using he
  · refine ⟨hc.exponent.1, ?_⟩
    intro j hj
    refine Eq.trans ?_ (hc.exponent.2 j hj)
    have he := byte_of_agrees ha (i := 0x538 + j) (by omega)
      (by unfold scratchOffset; omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc] using he
  · apply Eq.trans _ hc.initialWindow
    apply memLoad_congr
    intro i hi
    change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
    have he := byte_of_agrees ha (i := 0x78 + i) (by omega)
      (by unfold scratchOffset; omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at he
    simpa only [BitVec.ofNat_eq_ofNat] using congrArg (fun a : Option UInt8 => a.getD 0) he
  · exact (word_of_agrees ha 0x88 (by decide) (by unfold scratchOffset; omega)).trans hc.modulus0
  · exact (word_of_agrees ha 0x80 (by decide) (by unfold scratchOffset; omega)).trans hc.modulus1
  · exact (word_of_agrees ha 0x98 (by decide) (by unfold scratchOffset; omega)).trans hc.modulus2
  · exact (word_of_agrees ha 0x90 (by decide) (by unfold scratchOffset; omega)).trans hc.modulus3
  · exact (word_of_agrees ha 0x2a8 (by decide) (by unfold scratchOffset; omega)).trans hc.firstWindow
  · exact (word_of_agrees ha 0x2b8 (by decide) (by unfold scratchOffset; omega)).trans hc.parameterPointer
  · exact (word_of_agrees ha 0x2b0 (by decide) (by unfold scratchOffset; omega)).trans hc.firstWord
  · exact (word_of_agrees ha 0x2e0 (by decide) (by unfold scratchOffset; omega)).trans hc.inverse
  · exact (word_of_agrees ha 0x2d8 (by decide) (by unfold scratchOffset; omega)).trans hc.initialMask
  · exact (word_of_agrees ha 0x2c8 (by decide) (by unfold scratchOffset; omega)).trans hc.negativeInverse

theorem stack_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hf : ExponentFrame s t)
    {offset len : Nat} (hoff : offset ≤ 1416) (hlen : offset + len ≤ 1424) :
    MemReadable t (exponentFrameBase s + BitVec.ofNat 64 offset) len := by
  have he := base_add_eq_sub h (offset := 1416 - offset) (by omega)
  rw [Nat.sub_sub_self hoff] at he
  rw [he]
  exact readable_of_grow
    (stack_sub_readable h.stack (by omega) (by omega)) hf.allocated

theorem stack_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) (hf : ExponentFrame s t)
    {offset len : Nat} (hoff : offset ≤ 1416) (hlen : offset + len ≤ 1424)
    (halign : (len = 8 ∧ offset % 8 = 0) ∨ (len = 4 ∧ offset % 4 = 0) ∨ len = 1) :
    MemWritable t (exponentFrameBase s + BitVec.ofNat 64 offset) len := by
  have he := base_add_eq_sub h (offset := 1416 - offset) (by omega)
  rw [Nat.sub_sub_self hoff] at he
  rw [he]
  apply writable_of_grow (s := s) _ hf.allocated
  apply stack_sub_writable h.stack (fun a ha => h.avoids _ (by simp) a ha ∘ Or.inr) (by omega) (by omega) (by rcases halign with h | h | h <;> omega)
  rw [stackPtr_eq_regValue_rsp, ← he, base_add_toNat h hoff]
  have hs : (s.regValue .rsp).toNat % 16 = 8 := h.stack.2.2.2
  have hb : 1584 ≤ (s.regValue .rsp).toNat := (stack_bounds h.stack).1
  have hm8 := Nat.mod_mod_of_dvd ((s.regValue .rsp).toNat - 1416 + offset)
    (show 8 ∣ 4096 by decide)
  have hm4 := Nat.mod_mod_of_dvd ((s.regValue .rsp).toNat - 1416 + offset)
    (show 4 ∣ 4096 by decide)
  rcases halign with h | h | h <;> omega

theorem stack_byte_in_region [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) {offset i len : Nat}
    (hoff : offset ≤ 1416) (hlen : offset + len ≤ 1424) (hi : i < len) :
    (Stack.region s 1584).Contains
      (exponentFrameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  apply memoryRegion_contains_add h.stack.1 (len := len) _ _ hi
  · rw [base_add_toNat h hoff]
    change (s.regValue .rsp).toNat - 1584 ≤ (s.regValue .rsp).toNat - 1416 + offset
    omega
  · rw [base_add_toNat h hoff, stack_region_end]
    change (s.regValue .rsp).toNat - 1416 + offset + len ≤ (s.regValue .rsp).toNat + 8
    have hb : 1584 ≤ (s.regValue .rsp).toNat := (stack_bounds h.stack).1
    omega

theorem stack_apart_code [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (h : ExponentPre s boundary x) {offset len codeOffset codeLen : Nat}
    (hoff : offset ≤ 1416) (hlen : offset + len ≤ 1424)
    (hcode : codeOffset + codeLen ≤ 118431) :
    RangeApart (exponentFrameBase s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  have hin := stack_byte_in_region h hoff hlen hi
  have hp : InProgram (Extracted.textAddress + BitVec.ofNat 64 codeOffset + BitVec.ofNat 64 j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset _ (by omega)
  exact h.avoids (Stack.region s 1584) (by simp) _ hin (.inl (he ▸ hp))

end P256.Proofs.Sec1.SquareRoot.SquareFour
