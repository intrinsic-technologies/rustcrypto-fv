import Hkdf.Proofs.Key.Memory
import Hkdf.Proofs.Key.Tail.Copy
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Tail

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Instructions.CrossPageStore

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {key : ByteArray}

theorem output_contains (ctx : Context initial boundary key) {a : BitVec 64}
    (covered : (Component.mem (initial.regValue .rdi) 64).Covers a) :
    (registerRegion initial .rdi 64).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  exact memoryRegion_contains_add ctx.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem block_contains (ctx : Context initial boundary key) {a : BitVec 64}
    (covered : (Component.mem (blockAddress initial) 64).Covers a) :
    (Stack.region initial stackBytes).Contains a.toNat :=
  stackRegion_contains_sub ctx.stack.2.2.1 (by decide) (by decide) covered

theorem output_readable (ctx : Context initial boundary key) (state : State initial boundary s) :
    MemReadable s (initial.regValue .rdi) 64 := by
  apply readable_of_grow (s := initial) _ state.allocated
  exact memoryRegion_memReadable ctx.outputBounded ctx.outputAllocated
    (Nat.le_refl _) (Nat.le_refl _)

theorem output_writable (ctx : Context initial boundary key) (state : State initial boundary s) :
    Writable s (initial.regValue .rdi) 64 := by
  have read := output_readable ctx state
  refine ⟨read, tables_of_not_reserved (by decide) read.low ?_⟩
  intro i hi reserved
  exact ctx.avoids (registerRegion initial .rdi 64) (by simp) _
    (output_contains ctx ⟨i, hi, rfl⟩) (.inr reserved)

theorem output_codeApart (ctx : Context initial boundary key)
    {offset len : Nat} (bound : offset + len ≤ 115149) :
    RangeApart (initial.regValue .rdi) 64
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj eq
  apply ctx.avoids (registerRegion initial .rdi 64) (by simp) _
    (output_contains ctx ⟨i, hi, rfl⟩)
  left
  rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact Hkdf.Proofs.Common.Machine.inProgram_of_textOffset (offset + j) (by omega)

theorem output_block_apart (ctx : Context initial boundary key) :
    RangeApart (initial.regValue .rdi) 64 (blockAddress initial) 64 := by
  intro i hi j hj eq
  exact ctx.separation 1 2 (by decide) _
    (output_contains ctx ⟨i, hi, rfl⟩)
    (eq ▸ block_contains ctx ⟨j, hj, rfl⟩)

theorem copy_pre (ctx : Context initial boundary key) (input : Ready initial boundary key s) :
    Copy.Pre s := by
  have srcRead : MemReadable s (rspOf s) 64 := by
    change MemReadable s (stackPtr s) 64
    rw [input.rsp]
    exact stack_readable ctx input.toState (by decide) (by decide)
  have ptr : rbx.read s = initial.regValue .rdi := input.outputPointer
  refine ⟨input.rip, ?_, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨?_, ?_⟩
    · have low := srcRead.low
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact srcRead.mem (8 * i + j) (by omega)
  · intro i hi
    rw [ptr]
    exact (output_writable ctx input.toState).add (8 * i) (by omega)
  · intro i hi offset len bound
    rw [ptr]
    exact Hkdf.Proofs.Common.Instructions.RangeApart.add_left
      (output_codeApart ctx bound) (8 * i) (by omega)
  · intro i hi j hj
    have ib : i.toNat ≤ 56 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have jb : j.toNat ≤ 56 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    change RangeApart (rbx.read s + i) 8 (stackPtr s + j) 8
    rw [ptr, input.rsp]
    intro k hk l hl eq
    have eq' : initial.regValue .rdi + BitVec.ofNat 64 (i.toNat + k) =
        blockAddress initial + BitVec.ofNat 64 (j.toNat + l) := by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.add_assoc] using eq
    exact output_block_apart ctx (i.toNat + k) (by omega) (j.toNat + l) (by omega) eq'

def components (initial : RamState) : List Component :=
  [.reg 0, .reg 1, .mem (initial.regValue .rdi) 64, .rip]

omit [Bindings] in
theorem copy_memory (c : Component) (hc : c ∈ (Copy.effect s).components)
    (a : BitVec 64) (ha : c.Covers a) : (Component.mem (rbx.read s) 64).Covers a := by
  simp only [Copy.effect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i, hi, rfl⟩ := ha
  · refine ⟨0 + i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
  · refine ⟨8 + i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
  · refine ⟨16 + i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
  · refine ⟨24 + i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
  · refine ⟨32 + i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
  · refine ⟨40 + i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
  · refine ⟨48 + i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
  · refine ⟨56 + i, by omega, ?_⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]

theorem copy_frame {t : RamState} (input : Ready initial boundary key s)
    (h : (Copy.effect s).Holds s t) : AgreesExcept (components initial) s t := by
  apply agrees_of_footprint h.agrees
  · intro c hc hm
    simp only [Copy.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals simp [components, Component.isMem] at hm ⊢
  · intro c hc a ha
    refine ⟨.mem (initial.regValue .rdi) 64, by simp [components], ?_⟩
    have hm := copy_memory c hc a ha
    have ptr : rbx.read s = initial.regValue .rdi := input.outputPointer
    rw [ptr] at hm
    exact hm

theorem saved_contains (ctx : Context initial boundary key) {a : BitVec 64}
    (ha : (Component.mem (stackPtr initial - 40) 48).Covers a) :
    (Stack.region initial stackBytes).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := ha
  have sub : (stackPtr initial - 40).toNat = (stackPtr initial).toNat - 40 := by
    simpa only [BitVec.ofNat_eq_ofNat] using
      Hkdf.Proofs.Key.stack_sub_toNat ctx.toCalleePre (offset := 40) (by decide)
  apply memoryRegion_contains_add ctx.stack.1 (len := 48) _ _ hi
  · change (stackPtr initial).toNat - 720 ≤ (stackPtr initial - 40).toNat
    rw [sub]
    omega
  · rw [stack_region_end, sub]
    have bounds := stack_bounds ctx.toCalleePre
    change 720 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 at bounds
    omega

theorem copy_state {t : RamState} {fuel : Nat}
    (ctx : Context initial boundary key) (input : Ready initial boundary key s)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (h : (Copy.effect s).Holds s t) : State initial boundary t := by
  have frame := copy_frame input h
  have writes : WritesWithin (components initial) (writeRegions initial) := by
    intro c hc a ha
    simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨registerRegion initial .rdi 64, by simp [writeRegions], output_contains ctx ha⟩
  have savedApart : ∀ c ∈ components initial, ∀ a,
      (Component.mem (stackPtr initial - 40) 48).Covers a → ¬ c.Covers a := by
    intro c hc a ha hw
    simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact hw.elim
    exact ctx.separation 1 2 (by decide) _ (output_contains ctx hw) (saved_contains ctx ha)
  have running := input.toRunning.of_agrees run ready frame writes (by
    intro region member address contains inside
    exact ctx.avoids region (by simpa [writeRegions] using member)
      address contains (.inl inside)) (by simp [components])
  have saved := input.saved.of_agrees (fun i hi ↦
    frame.byte (fun c hc ↦ savedApart c hc _ ⟨i, hi, rfl⟩))
  exact ⟨running, saved,
    (frame.read (n := 64) (r := 5) (by simp [components])).trans input.rbp,
    (frame.mxcsr (by simp [components])).trans input.mxcsr,
    (frame.fcw (by simp [components])).trans input.fcw⟩

end Hkdf.Proofs.Key.Tail
