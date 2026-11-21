import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Standard.Extract.Copy
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Extract

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame

variable [Bindings] {initial s : RamState} {salt : Option ByteArray} {inputs : Array Input}

theorem output_contains (ctx : Context initial salt inputs) {a : BitVec 64}
    (covered : (Component.mem (initial.regValue .r9) 32).Covers a) :
    (outputRegion initial hkdfSha256Extract).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  exact memoryRegion_contains_add ctx.call.outputInMemory.1
    (Nat.le_refl _) (Nat.le_refl _) hi

theorem output_readable (ctx : Context initial salt inputs) (state : State initial s) :
    MemReadable s (initial.regValue .r9) 32 := by
  apply Hkdf.Proofs.Common.Encoding.Serialize.readable_of_grow (s := initial) _ state.allocated
  exact Hkdf.Proofs.Common.Machine.memoryRegion_memReadable ctx.call.outputInMemory.1
    ctx.call.outputInMemory.2 (Nat.le_refl _) (Nat.le_refl _)

theorem output_writable (ctx : Context initial salt inputs) (state : State initial s) :
    Copy.Writable s (initial.regValue .r9) 32 := by
  have read := output_readable ctx state
  refine ⟨read, tables_of_not_reserved (by decide) read.low ?_⟩
  intro i hi reserved
  exact (ctx.call.outputSeparation.2 (outputRegion initial hkdfSha256Extract) (by simp)).2 _
    (output_contains ctx ⟨i, hi, rfl⟩) (.inr reserved)

theorem output_codeApart (ctx : Context initial salt inputs) :
    RangeApart (initial.regValue .r9) 32 0x10174c 69 := by
  intro i hi j hj eq
  apply (ctx.call.outputSeparation.2 (outputRegion initial hkdfSha256Extract) (by simp)).2 _
    (output_contains ctx ⟨i, hi, rfl⟩)
  left
  rw [eq]
  simpa only [Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
    BitVec.reduceAdd] using inProgram_of_textOffset (0x174c + j) (by omega)

theorem stack_contains (ctx : Context initial salt inputs) {a : BitVec 64} {offset : Nat}
    (low : offset ≤ 520) (high : 8 ≤ offset)
    (covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) 8).Covers a) :
    (Stack.region initial hkdfSha256Extract.minStackBytes).Contains a.toNat :=
  Hkdf.Proofs.Common.Machine.stackRegion_contains_sub ctx.call.stack.2.2.1
    (by change offset ≤ 1792; omega) high covered

theorem copy_pre (ctx : Context initial salt inputs) (state : State initial s)
    (rip : s.RIP = 0x10174c) (rsp : stackPtr s = frameBase initial)
    (pointer : memLoad s.external (frameBase initial + 96) 64 = initial.regValue .r9) :
    Copy.Pre s := by
  have ptr : Copy.outputPtr s = initial.regValue .r9 := by
    exact (show memLoad s.external (stackPtr s + 96) 64 = _ by rw [rsp]; exact pointer)
  refine ⟨rip, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · have addr : rspOf s + 96 = stackPtr initial - 424 :=
        Standard.stack_address rsp (offset := 96) (by decide)
      rw [addr]
      exact Standard.stack_readable ctx state (offset := 424) (by decide) (by decide)
    · have addr : rspOf s + 120 = stackPtr initial - 400 :=
        Standard.stack_address rsp (offset := 120) (by decide)
      rw [addr]
      exact Standard.stack_readable ctx state (offset := 400) (by decide) (by decide)
    · have addr : rspOf s + 128 = stackPtr initial - 392 :=
        Standard.stack_address rsp (offset := 128) (by decide)
      rw [addr]
      exact Standard.stack_readable ctx state (offset := 392) (by decide) (by decide)
    · have addr : rspOf s + 136 = stackPtr initial - 384 :=
        Standard.stack_address rsp (offset := 136) (by decide)
      rw [addr]
      exact Standard.stack_readable ctx state (offset := 384) (by decide) (by decide)
    · have addr : rspOf s + 144 = stackPtr initial - 376 :=
        Standard.stack_address rsp (offset := 144) (by decide)
      rw [addr]
      exact Standard.stack_readable ctx state (offset := 376) (by decide) (by decide)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · have addr : rspOf s + 16 = stackPtr initial - 504 :=
        Standard.stack_address rsp (offset := 16) (by decide)
      rw [addr]
      exact Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable.of_memWritable
        (Hkdf.Proofs.Common.Encoding.Serialize.writable_of_grow
          (Standard.initial_stack_writable8 ctx (offset := 504) (by decide) (by decide)) state.allocated)
    · have addr : rspOf s + 24 = stackPtr initial - 496 :=
        Standard.stack_address rsp (offset := 24) (by decide)
      rw [addr]
      exact Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable.of_memWritable
        (Hkdf.Proofs.Common.Encoding.Serialize.writable_of_grow
          (Standard.initial_stack_writable8 ctx (offset := 496) (by decide) (by decide)) state.allocated)
    · have addr : rspOf s + 32 = stackPtr initial - 488 :=
        Standard.stack_address rsp (offset := 32) (by decide)
      rw [addr]
      exact Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable.of_memWritable
        (Hkdf.Proofs.Common.Encoding.Serialize.writable_of_grow
          (Standard.initial_stack_writable8 ctx (offset := 488) (by decide) (by decide)) state.allocated)
    · have addr : rspOf s + 40 = stackPtr initial - 480 :=
        Standard.stack_address rsp (offset := 40) (by decide)
      rw [addr]
      exact Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable.of_memWritable
        (Hkdf.Proofs.Common.Encoding.Serialize.writable_of_grow
          (Standard.initial_stack_writable8 ctx (offset := 480) (by decide) (by decide)) state.allocated)
  · intro i hi
    rw [ptr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact (output_writable ctx state).add _ (by decide)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · have addr : rspOf s + 16 = stackPtr initial - 504 :=
        Standard.stack_address rsp (offset := 16) (by decide)
      rw [addr]
      exact Standard.stack_codeApart ctx (offset := 504)
        (codeOffset := 0x174c) (codeLen := 69)
        (by decide) (by decide) (by decide)
    · have addr : rspOf s + 24 = stackPtr initial - 496 :=
        Standard.stack_address rsp (offset := 24) (by decide)
      rw [addr]
      exact Standard.stack_codeApart ctx (offset := 496)
        (codeOffset := 0x174c) (codeLen := 69)
        (by decide) (by decide) (by decide)
    · have addr : rspOf s + 32 = stackPtr initial - 488 :=
        Standard.stack_address rsp (offset := 32) (by decide)
      rw [addr]
      exact Standard.stack_codeApart ctx (offset := 488)
        (codeOffset := 0x174c) (codeLen := 69)
        (by decide) (by decide) (by decide)
    · have addr : rspOf s + 40 = stackPtr initial - 480 :=
        Standard.stack_address rsp (offset := 40) (by decide)
      rw [addr]
      exact Standard.stack_codeApart ctx (offset := 480)
        (codeOffset := 0x174c) (codeLen := 69)
        (by decide) (by decide) (by decide)
  · intro i hi
    rw [ptr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      exact Hkdf.Proofs.Common.Instructions.RangeApart.add_left (output_codeApart ctx) _ (by decide)
  · intro i hi j hj a ha b hb eq
    have ib : i.toNat ≤ 40 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    have il : 16 ≤ i.toNat := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    have jb : j.toNat ≤ 24 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> decide
    have covered : (Component.mem (initial.regValue .r9) 32).Covers
        (Copy.outputPtr s + j + BitVec.ofNat 64 b) := by
      refine ⟨j.toNat+b, by omega, ?_⟩
      simp only [ptr, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.add_assoc]
    have stackCover : (Stack.region initial hkdfSha256Extract.minStackBytes).Contains
        (rspOf s + i + BitVec.ofNat 64 a).toNat := by
      have addr : rspOf s + i = stackPtr initial - BitVec.ofNat 64 (520-i.toNat) := by
        simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
          Standard.stack_address rsp (offset := i.toNat) (by omega)
      rw [addr]
      exact stack_contains ctx (by omega) (by omega) ⟨a, ha, rfl⟩
    exact ctx.call.outputSeparation.1 ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) _
      (output_contains ctx covered) (eq ▸ stackCover)


def copyComponents (initial : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7,
    .mem (frameBase initial + 16) 32, .mem (initial.regValue .r9) 32, .rip]

omit [Bindings] in
theorem copy_agrees {t : RamState} (rsp : stackPtr s = frameBase initial)
    (pointer : Copy.outputPtr s = initial.regValue .r9)
    (effect : (Copy.effect s).Holds s t) : AgreesExcept (copyComponents initial) s t := by
  apply Hkdf.Proofs.Common.Encoding.Serialize.agrees_of_footprint effect.agrees
  · intro c hc hm
    simp only [Copy.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl) | rfl
    all_goals simp [copyComponents, Component.isMem] at hm ⊢
  · intro c hc a ha
    simp only [Copy.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    · obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (frameBase initial + 16) 32, by simp [copyComponents],
        24+i, by omega, ?_⟩
      change rspOf s + 40 + BitVec.ofNat 64 i = _
      change s.regValue .rsp + _ + _ = _
      have sp : s.regValue .rsp = frameBase initial := rsp
      rw [sp]
      simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      exact congrArg (fun x : BitVec 64 ↦ frameBase initial + x)
        (BitVec.add_assoc (16 : BitVec 64) (24 : BitVec 64) (BitVec.ofNat 64 i))
    · obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (frameBase initial + 16) 32, by simp [copyComponents],
        16+i, by omega, ?_⟩
      change rspOf s + 32 + BitVec.ofNat 64 i = _
      change s.regValue .rsp + _ + _ = _
      have sp : s.regValue .rsp = frameBase initial := rsp
      rw [sp]
      simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      exact congrArg (fun x : BitVec 64 ↦ frameBase initial + x)
        (BitVec.add_assoc (16 : BitVec 64) (16 : BitVec 64) (BitVec.ofNat 64 i))
    · obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (frameBase initial + 16) 32, by simp [copyComponents],
        8+i, by omega, ?_⟩
      change rspOf s + 24 + BitVec.ofNat 64 i = _
      change s.regValue .rsp + _ + _ = _
      have sp : s.regValue .rsp = frameBase initial := rsp
      rw [sp]
      simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      exact congrArg (fun x : BitVec 64 ↦ frameBase initial + x)
        (BitVec.add_assoc (16 : BitVec 64) (8 : BitVec 64) (BitVec.ofNat 64 i))
    · obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (frameBase initial + 16) 32, by simp [copyComponents],
        0+i, by omega, ?_⟩
      change rspOf s + 16 + BitVec.ofNat 64 i = _
      change s.regValue .rsp + _ + _ = _
      have sp : s.regValue .rsp = frameBase initial := rsp
      rw [sp]
      simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      exact congrArg (fun x : BitVec 64 ↦ frameBase initial + x)
        (BitVec.add_assoc (16 : BitVec 64) (0 : BitVec 64) (BitVec.ofNat 64 i))
    · obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (initial.regValue .r9) 32, by simp [copyComponents],
        24+i, by omega, ?_⟩
      simp only [pointer, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
    · obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (initial.regValue .r9) 32, by simp [copyComponents],
        16+i, by omega, ?_⟩
      simp only [pointer, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
    · obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (initial.regValue .r9) 32, by simp [copyComponents],
        8+i, by omega, ?_⟩
      simp only [pointer, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
    · obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (initial.regValue .r9) 32, by simp [copyComponents],
        0+i, by omega, ?_⟩
      simp only [pointer, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]

theorem copy_saved {t : RamState} (ctx : Context initial salt inputs)
    (state : State initial s) (frame : AgreesExcept (copyComponents initial) s t) :
    SavedStackAt initial t := by
  apply state.saved.of_agrees
  intro i hi
  apply frame.byte
  intro c hc cover
  simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  · obtain ⟨j, hj, eq⟩ := cover
    have apart : OffsetsApart (-48) 56 (-504) 32 := by
      unfold OffsetsApart
      decide +kernel
    apply apart.ne (stackPtr initial) hi hj (by decide)
    rw [show frameBase initial = stackPtr initial - 520 from rfl] at eq
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] using eq
  · have savedContains : (Stack.region initial hkdfSha256Extract.minStackBytes).Contains
        (stackPtr initial - 48 + BitVec.ofNat 64 i).toNat := by
      have addr : (stackPtr initial - 48).toNat = (stackPtr initial).toNat - 48 :=
        Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 48) (by decide)
      apply memoryRegion_contains_add ctx.call.stack.1 (len := 56) _ _ hi
      · change (stackPtr initial).toNat - 1792 ≤ (stackPtr initial - 48).toNat
        rw [addr]
        omega
      · rw [stack_region_end, addr]
        have bounds := Standard.stack_bounds ctx
        omega
    exact ctx.call.outputSeparation.1 ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) _
      (output_contains ctx cover) savedContains

theorem copy_writeFrame {t : RamState} (ctx : Context initial salt inputs)
    (frame : AgreesExcept (copyComponents initial) s t) :
    MemoryWriteFrame s t #v[outputRegion initial hkdfSha256Extract,
      Stack.region initial hkdfSha256Extract.minStackBytes] := by
  apply frame.memoryWriteFrame
  intro c hc a ha
  simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · refine ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp, ?_⟩
    have addr : frameBase initial + 16 = stackPtr initial - 504 := by
      change (initial.regValue .rsp - 520) + 16 = initial.regValue .rsp - 504
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    rw [addr] at ha
    exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub ctx.call.stack.2.2.1
      (by decide) (by decide) ha
  · exact ⟨outputRegion initial hkdfSha256Extract, by simp, output_contains ctx ha⟩

end Hkdf.Proofs.Standard.Extract
