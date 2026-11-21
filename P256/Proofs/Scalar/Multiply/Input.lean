import P256.Proofs.Scalar.Multiply.Barrett.Layout
import P256.Proofs.Scalar.Multiply.Interface
import P256.Proofs.Scalar.Multiply.Representation
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Adapter

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines


open Barrett
open P256.Proofs.Field.Inverse.SafeGcd.Core.Input (readWords readWords_at)

def activation (s : RamState) : Activation :=
  ⟨s.external, stackPtr s, (returnBoundary s).rip, stackPtr s - 112,
    s.regValue .rbx, s.regValue .rbp, s.regValue .r12, s.regValue .r13,
    s.regValue .r14, s.regValue .r15, s.regValue .rdi, s.regValue .rsi,
    s.regValue .rdx, s.regValue .rcx, s.regValue .r8, s.regValue .r9,
    s.MXCSR, (Operand.ftw : Operand 16).read s, s.FP87_Control, s.FS⟩

open P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution
  (fnCode_sub fnCode_inProgram disjoint_intervals writable_region)

variable [Bindings] {s : RamState} {boundary : ReturnBoundary}

theorem entry_ready (pre : BarrettPre s boundary) : EntryReady Machine.fnCode s :=
  ⟨readyToStep pre.machine pre.bindingsSupported, pre.machine.sse,
    (programLoaded_codeIn pre.loaded).mono (fun _ h => fnCode_sub h)⟩

theorem entry_atoms (pre : BarrettPre s boundary) :
    Atom.All Machine.fnCode (Machine.lifted.locationOf .l118320 s).arguments s.external
      (Machine.Reduce.frameAt .l118320 (activation s) ++
        commonAtoms (activation s) s (inputs s)) := by
  have hs := stack_bounds pre.stack
  have hlow := stack_sub_toNat pre.stack (offset := 112) (by decide)
  change (stackPtr s - 112).toNat = (stackPtr s).toNat - 112 at hlow
  have hret : Refine.Readable s.external (stackPtr s) 8 := by
    have h := stack_sub_readable pre.stack (offset := 0) (len := 8) (by decide) (by decide)
    have hr : MemReadable s (stackPtr s) 8 := by simpa using h
    exact ⟨hr.low, hr.mem⟩
  have hstack : Refine.Writable Machine.fnCode s.external (stackPtr s - 112) 112 := by
    apply writable_region pre.stack.1 pre.stack.2.1 (pre.avoids _ (by simp))
    · rw [hlow]; exact Nat.le_refl _
    · rw [hlow, stack_region_end]; omega
    · decide
  have hout : Refine.Writable Machine.fnCode s.external (s.regValue .rdi) 32 :=
    writable_region pre.outputBounded pre.outputAllocated (pre.avoids _ (by simp))
      (Nat.le_refl _) (Nat.le_refl _) (by decide)
  have hinput := memoryRegion_memReadable pre.inputBounded pre.inputAllocated
    (addr := s.regValue .rsi) (len := 32) (Nat.le_refl _) (Nat.le_refl _)
  have hright := memoryRegion_memReadable pre.rightBounded pre.rightAllocated
    (addr := s.regValue .rdx) (len := 32) (Nat.le_refl _) (Nat.le_refl _)
  have ho := disjoint_intervals (a := registerRegion s .rdi 32) (b := Stack.region s 112)
    (by change 0 < 32; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-112); omega)
    (pre.separation (1 : Fin 3) 2 (by decide))
  have hi := disjoint_intervals (a := registerRegion s .rsi 32) (b := Stack.region s 112)
    (by change 0 < 32; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-112); omega)
    (pre.separation (0 : Fin 3) 2 (by decide))
  have hm := disjoint_intervals (a := registerRegion s .rdx 32) (b := Stack.region s 112)
    (by change 0 < 32; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-112); omega)
    pre.rightStack
  rw [stack_region_end] at ho hi hm
  change (s.regValue .rdi).toNat+32 ≤ (stackPtr s).toNat-112 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rdi).toNat at ho
  change (s.regValue .rsi).toNat+32 ≤ (stackPtr s).toNat-112 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rsi).toNat at hi
  change (s.regValue .rdx).toNat+32 ≤ (stackPtr s).toNat-112 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rdx).toNat at hm
  have wi := readWords_at s (s.regValue .rsi)
  have wm := readWords_at s (s.regValue .rdx)
  rw [Atom.all_append]
  constructor
  · dsimp only [Machine.Reduce.frameAt, Machine.Reduce.frameAtG0,
      Atom.All, Atom.Holds, Atom.gpr]
    refine ⟨(Vector.getElem_ofFn _).trans rfl, ?_, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl,
      hret, rfl, inProgram_low pre.returnInProgram, hstack, ?_, pre.stack.2.2.2, trivial⟩
    · exact (Vector.getElem_ofFn _).trans (Reg.read_df_iff.mpr pre.directionFlag)
    · change (stackPtr s - 112).toNat+112 ≤ (stackPtr s).toNat
      rw [hlow]; omega
  · dsimp only [commonAtoms, Atom.All, Atom.Holds]
    refine ⟨(Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, hout, ?_, wi, wm, ⟨hinput.low, hinput.mem⟩,
      ⟨hright.low, hright.mem⟩, ?_, ?_, trivial⟩
    · change (s.regValue .rdi).toNat+32 ≤ (stackPtr s-112).toNat ∨
        (stackPtr s).toNat+8 ≤ (s.regValue .rdi).toNat
      rw [hlow]; exact ho
    · change (s.regValue .rsi).toNat+32 ≤ (stackPtr s-112).toNat ∨
        (stackPtr s).toNat ≤ (s.regValue .rsi).toNat
      rw [hlow]; omega
    · change (s.regValue .rdx).toNat+32 ≤ (stackPtr s-112).toNat ∨
        (stackPtr s).toNat ≤ (s.regValue .rdx).toNat
      rw [hlow]; omega

end P256.Proofs.Scalar.Multiply.Adapter
