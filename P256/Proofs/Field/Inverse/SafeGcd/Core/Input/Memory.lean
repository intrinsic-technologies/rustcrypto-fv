import P256.Proofs.Field.Inverse.SafeGcd.Core.Prefix.Layout
import P256.Proofs.Field.Inverse.SafeGcd.Core.Contract
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Input
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Input

open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines


def activation (s : RamState) : Activation :=
  ⟨s.external, stackPtr s, (returnBoundary s).rip, stackPtr s - 704,
    s.regValue .rbx, s.regValue .rbp, s.regValue .r12, s.regValue .r13,
    s.regValue .r14, s.regValue .r15, s.regValue .rdi, s.regValue .rsi,
    s.regValue .rdx, s.regValue .rcx, s.regValue .r8, s.regValue .r9,
    s.MXCSR, (Operand.ftw : Operand 16).read s, s.FP87_Control, s.FS⟩

def readWords (s : RamState) (address : BitVec 64) : Vector (BitVec 64) 4 :=
  #v[memLoad s.external address 64, memLoad s.external (address+8) 64,
     memLoad s.external (address+16) 64, memLoad s.external (address+24) 64]

def inputs (s : RamState) : Inputs :=
  ⟨readWords s (s.regValue .rsi), readWords s (s.regValue .rdx),
   readWords s (s.regValue .r8), s.regValue .rcx⟩

theorem readWords_at (s : RamState) (address : BitVec 64) :
    WordsAt s.external address 64 (readWords s address) := by
  intro i hi
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases casesI with rfl | rfl | rfl | rfl <;> simp [readWords, wordAddr]

theorem fnCode_sub {x : BitVec 64 × UInt8} (h : x ∈ Machine.fnCode) :
    x ∈ Extracted.programSections.toCodeMap := by
  simp only [Machine.fnCode, Machine.sections, ImageSections.toCodeMap,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
  simp only [Extracted.programSections, ImageSections.toCodeMap,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.mem_append_left _ h

theorem fnCode_inProgram {x : BitVec 64 × UInt8} (h : x ∈ Machine.fnCode) :
    InProgram x.1 := ⟨x.2, programSections_fetchByte_of_mem (fnCode_sub h)⟩

theorem writable_region {s : RamState} {region : MemoryRegion} {address : BitVec 64}
    {len : Nat} (hb : region.Bounded) (ha : region.Allocated s.external)
    (avoid : region.Avoids (fun a => InProgram a ∨ InPageTables a))
    (start : region.start ≤ address.toNat) (finish : address.toNat + len ≤ region.start + region.size)
    (positive : 0 < len) : Refine.Writable Machine.fnCode s.external address len := by
  have read := memoryRegion_memReadable hb ha start finish
  refine ⟨⟨read.low, read.mem⟩, ?_, ?_⟩
  · apply tables_of_not_reserved positive read.low
    intro i hi hres
    exact avoid _ (memoryRegion_contains_add hb start finish hi) (.inr hres)
  · intro x hx i hi he
    apply avoid _ (memoryRegion_contains_add hb start finish hi)
    exact .inl (he ▸ fnCode_inProgram hx)

variable [Bindings] {s : RamState} {boundary : ReturnBoundary}

theorem entry_ready (pre : SafeGcdPre s boundary) : EntryReady Machine.fnCode s :=
  ⟨readyToStep pre.machine pre.bindingsSupported, pre.machine.sse,
    (programLoaded_codeIn pre.loaded).mono (fun _ h => fnCode_sub h)⟩

theorem entry_atoms (pre : SafeGcdPre s boundary) :
    Atom.All Machine.fnCode (Machine.lifted.locationOf .l117650 s).arguments s.external
      (Prefix.atoms .entry (activation s) s (inputs s)) := by
  have hs := stack_bounds pre.stack
  have hlow := stack_sub_toNat pre.stack (offset := 704) (by decide)
  change (stackPtr s - 704).toNat = (stackPtr s).toNat - 704 at hlow
  have hret : Refine.Readable s.external (stackPtr s) 8 := by
    have h := stack_sub_readable pre.stack (offset := 0) (len := 8) (by decide) (by decide)
    have hr : MemReadable s (stackPtr s) 8 := by simpa using h
    exact ⟨hr.low, hr.mem⟩
  have hstack : Refine.Writable Machine.fnCode s.external (stackPtr s - 704) 704 := by
    apply writable_region pre.stack.1 pre.stack.2.1 (pre.avoids _ (by simp))
    · rw [hlow]; exact Nat.le_refl _
    · rw [hlow, stack_region_end]; omega
    · decide
  have hout : Refine.Writable Machine.fnCode s.external (s.regValue .rdi) 33 :=
    writable_region pre.outputBounded pre.outputAllocated (pre.avoids _ (by simp))
      (Nat.le_refl _) (by change (s.regValue .rdi).toNat + 33 ≤ (s.regValue .rdi).toNat + 40; omega) (by decide)
  have hinput := memoryRegion_memReadable pre.inputBounded pre.inputAllocated
    (addr := s.regValue .rsi) (len := 32) (Nat.le_refl _) (Nat.le_refl _)
  have hmodulus := memoryRegion_memReadable pre.modulusRegion.bounded pre.modulusRegion.allocated
    (addr := s.regValue .rdx) (len := 32) (Nat.le_refl _) (Nat.le_refl _)
  have ho := Correction.Execution.disjoint_intervals (a := registerRegion s .rdi 40) (b := Stack.region s 704)
    (by change 0 < 40; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-704); omega)
    (pre.separation (1 : Fin 3) 2 (by decide))
  have hi := Correction.Execution.disjoint_intervals (a := registerRegion s .rsi 32) (b := Stack.region s 704)
    (by change 0 < 32; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-704); omega)
    (pre.separation (0 : Fin 3) 2 (by decide))
  have hm := Correction.Execution.disjoint_intervals (a := registerRegion s .rdx 32) (b := Stack.region s 704)
    (by change 0 < 32; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-704); omega)
    pre.modulusRegion.stack
  rw [stack_region_end] at ho hi hm
  change (s.regValue .rdi).toNat+40 ≤ (stackPtr s).toNat-704 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rdi).toNat at ho
  change (s.regValue .rsi).toNat+32 ≤ (stackPtr s).toNat-704 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rsi).toNat at hi
  change (s.regValue .rdx).toNat+32 ≤ (stackPtr s).toNat-704 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rdx).toNat at hm
  have hscale := memoryRegion_memReadable pre.adjusterRegion.bounded pre.adjusterRegion.allocated
    (addr := s.regValue .r8) (len := 32) (Nat.le_refl _) (Nat.le_refl _)
  have ht := Correction.Execution.disjoint_intervals (a := registerRegion s .r8 32) (b := Stack.region s 704)
    (by change 0 < 32; decide)
    (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-704); omega)
    pre.adjusterRegion.stack
  rw [stack_region_end] at ht
  change (s.regValue .r8).toNat+32 ≤ (stackPtr s).toNat-704 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .r8).toNat at ht
  change Atom.All _ _ _ ((Machine.Core.frameAt .l117650 (activation s) ++
    [.reg 39 ⟨32, s.MXCSR⟩, .reg 51 ⟨16, s.FP87_Control⟩]) ++ commonAtoms (activation s) (inputs s))
  rw [Atom.all_append, Atom.all_append]
  refine ⟨⟨?_, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, trivial⟩, ?_⟩
  · dsimp only [Machine.Core.frameAt, Machine.Core.frameAtG0,
      Atom.All, Atom.Holds, Atom.gpr]
    refine ⟨(Vector.getElem_ofFn _).trans rfl, ?_, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl,
      hret, rfl, inProgram_low pre.returnInProgram, hstack, ?_, pre.stack.2.2.2, trivial⟩
    · exact (Vector.getElem_ofFn _).trans (Reg.read_df_iff.mpr pre.directionFlag)
    · change (stackPtr s - 704).toNat+704 ≤ (stackPtr s).toNat
      rw [hlow]; omega
  · simp only [commonAtoms, outputAtoms, inputAtoms, Atom.all_append, Atom.All, Atom.Holds]
    refine ⟨⟨hout, ?_, trivial⟩, readWords_at _ _, readWords_at _ _, readWords_at _ _,
      ⟨hinput.low,hinput.mem⟩, ⟨hmodulus.low,hmodulus.mem⟩, ⟨hscale.low,hscale.mem⟩,
      ?_, ?_, ?_, rfl, trivial⟩
    · change (s.regValue .rdi).toNat+33 ≤ (stackPtr s-704).toNat ∨
        (stackPtr s).toNat+8 ≤ (s.regValue .rdi).toNat
      rw [hlow]; omega
    · change (s.regValue .rsi).toNat+32 ≤ (stackPtr s-704).toNat ∨
        (stackPtr s).toNat ≤ (s.regValue .rsi).toNat
      rw [hlow]; omega
    · change (s.regValue .rdx).toNat+32 ≤ (stackPtr s-704).toNat ∨
        (stackPtr s).toNat ≤ (s.regValue .rdx).toNat
      rw [hlow]; omega
    · change (s.regValue .r8).toNat+32 ≤ (stackPtr s-704).toNat ∨
        (stackPtr s).toNat ≤ (s.regValue .r8).toNat
      rw [hlow]; omega

end P256.Proofs.Field.Inverse.SafeGcd.Core.Input
