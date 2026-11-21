import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Projective.Preserve
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs

theorem step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve : Nat} {frameOffset : Nat}
    {P : RamState → Prop} {E : RamState → Effect} {bytes : List UInt8} {offset : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve inputRegister)
    (state : FrameState s t outputBytes reserve (BitVec.ofNat 64 frameOffset))
    (saved : 48 ≤ reserve)
    (instruction : StepEffect P
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) E)
    (bounded : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (ready : P t) (next : InProgram (E t).rip)
    (writes : WritesWithin (E t).components #v[registerRegion s .rdi outputBytes, workRegion s reserve])
    (sp : .reg 4 ∉ (E t).components)
    (hdf : Component.df ∉ (E t).components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ (E t).components := by component_not_mem)
    (hfcw : Component.fcw ∉ (E t).components := by component_not_mem) :
    ∃ u, Advances boundary 1 t u ∧ FrameState s u outputBytes reserve (BitVec.ofNat 64 frameOffset) ∧
      (E t).Holds t u := by
  obtain ⟨u, run, ready', effect⟩ := instruction.advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes bounded code)
    ready (boundary_ne_program pre.outerBoundary next)
  exact ⟨u, run, FrameState.after_effect pre saved state ready' effect.agrees writes sp, effect⟩

theorem step_registers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve : Nat} {frameOffset : Nat}
    {P : RamState → Prop} {E : RamState → Effect} {bytes : List UInt8} {offset : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve inputRegister)
    (state : FrameState s t outputBytes reserve (BitVec.ofNat 64 frameOffset))
    (instruction : StepEffect P
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) E)
    (bounded : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (ready : P t) (next : InProgram (E t).rip)
    (noMem : ∀ c ∈ (E t).components, ∀ a, ¬ c.Covers a)
    (sp : .reg 4 ∉ (E t).components)
    (hdf : Component.df ∉ (E t).components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ (E t).components := by component_not_mem)
    (hfcw : Component.fcw ∉ (E t).components := by component_not_mem) :
    ∃ u, Advances boundary 1 t u ∧ FrameState s u outputBytes reserve (BitVec.ofNat 64 frameOffset) ∧
      (E t).Holds t u := by
  obtain ⟨u, run, ready', effect⟩ := instruction.advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes bounded code)
    ready (boundary_ne_program pre.outerBoundary next)
  exact ⟨u, run, state.after_registers ready' effect.agrees noMem sp, effect⟩

theorem point_of_stack [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes reserve : Nat} {point : Projective}
    (pre : CalleePre s boundary entry inputBytes 96 reserve inputRegister)
    (frame : MemoryWriteFrame t u #v[Stack.region s reserve])
    (input : ProjectiveAt t (s.regValue .rdi) point) :
    ProjectiveAt u (s.regValue .rdi) point := by
  apply input.of_frame frame pre.outputBounded
  intro region member
  have same : region = Stack.region s reserve := by simpa using member
  subst region
  exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)

def stackSlot (s : RamState) (offset : Nat) : BitVec 64 :=
  stackPtr s - 728 + BitVec.ofNat 64 offset

theorem stackSlot_eq (s : RamState) {offset : Nat} (h : offset ≤ 728) :
    stackSlot s offset = stackPtr s - BitVec.ofNat 64 (728 - offset) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 728 offset (by omega) h]
  simp only [stackSlot, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem stack_point_apart [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {offset len poffset plen : Nat} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (hb : offset + len ≤ 728) (hp : poffset + plen ≤ 96) :
    RangeApart (stackSlot s offset) len (s.regValue .rdi + BitVec.ofNat 64 poffset) plen := by
  intro i hi j hj he
  apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)
    (s.regValue .rdi + BitVec.ofNat 64 poffset + BitVec.ofNat 64 j).toNat
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
      (by change poffset + j < 96; omega)
  · rw [← he, stackSlot_eq s (by omega)]
    exact stack_contains pre (by omega) (by omega) ⟨i, hi, rfl⟩

theorem point_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve : Nat} {frameOffset : BitVec 64}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve inputRegister)
    (state : FrameState s t outputBytes reserve frameOffset)
    {offset len : Nat} (bound : offset + len ≤ outputBytes) :
    MemReadable t (s.regValue .rdi + BitVec.ofNat 64 offset) len := by
  have whole : MemReadable s (s.regValue .rdi) outputBytes :=
    memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _)
  exact readable_of_grow (P256.Proofs.Common.Memory.memReadable_sub whole offset len bound)
    state.allocated

theorem read_of_store {t u : RamState} {a b : BitVec 64}
    (frame : AgreesExcept [.mem a 8, .rip] t u) (apart : RangeApart a 8 b 8) :
    memLoad u.external b 64 = memLoad t.external b 64 := by
  apply memLoad_congr
  intro i hi
  change (u.external[b + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[b + BitVec.ofNat 64 i]?).getD 0
  rw [frame.byte]
  intro c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hv
    exact apart j hj i hi he.symm
  · exact hv.elim

theorem work_stack_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve inputRegister)
    (frame : MemoryWriteFrame t u #v[workRegion s reserve]) :
    MemoryWriteFrame t u #v[Stack.region s reserve] := by
  intro a ha
  apply frame
  intro region hregion hin
  have he : region = workRegion s reserve := by simpa using hregion
  subst region
  apply ha (Stack.region s reserve) (by simp)
  change (stackPtr s).toNat - reserve ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - reserve + (reserve - 48) at hin
  change (Stack.region s reserve).start ≤ a.toNat ∧
    a.toNat < (Stack.region s reserve).start + (Stack.region s reserve).size
  rw [stack_region_end]
  change (stackPtr s).toNat - reserve ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat + 8
  have hb := stack_bounds pre.stack
  constructor <;> omega

end P256.Proofs.Projective.Double
