import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Routine
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines


def activation (s : RamState) : Activation :=
  ⟨s.external, stackPtr s, (returnBoundary s).rip, stackPtr s - 56,
    s.regValue .rbx, s.regValue .rbp, s.regValue .r12, s.regValue .r13,
    s.regValue .r14, s.regValue .r15, s.regValue .rdi, s.regValue .rsi,
    s.regValue .rdx, s.regValue .rcx, s.regValue .r8, s.regValue .r9,
    s.MXCSR, (Operand.ftw : Operand 16).read s, s.FP87_Control, s.FS⟩

theorem fnCode_sub {x : BitVec 64 × UInt8} (h : x ∈ Machine.fnCode) :
    x ∈ Extracted.programSections.toCodeMap := by
  simp only [Machine.fnCode, Machine.sections, ImageSections.toCodeMap,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
  simp only [Extracted.programSections, ImageSections.toCodeMap,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.mem_append_left _ h

theorem fnCode_inProgram {x : BitVec 64 × UInt8} (h : x ∈ Machine.fnCode) :
    InProgram x.1 := ⟨x.2, programSections_fetchByte_of_mem (fnCode_sub h)⟩

theorem disjoint_intervals {a b : MemoryRegion} (ha : 0 < a.size) (hb : 0 < b.size)
    (h : a.Disjoint b) : a.start + a.size ≤ b.start ∨ b.start + b.size ≤ a.start := by
  by_cases hab : a.start ≤ b.start
  · have hn := h b.start
    simp only [MemoryRegion.Contains] at hn
    omega
  · have hn := h a.start
    simp only [MemoryRegion.Contains] at hn
    omega

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

theorem entry_ready (pre : Pre s boundary) : EntryReady Machine.fnCode s :=
  ⟨readyToStep pre.machine pre.bindingsSupported, pre.machine.sse,
    (programLoaded_codeIn pre.loaded).mono (fun _ h => fnCode_sub h)⟩

theorem entry_atoms (pre : Pre s boundary) :
    Atom.All Machine.fnCode (Machine.lifted.locationOf .l1181a0 s).arguments s.external
      (Machine.Correction.frameAt .l1181a0 (activation s) ++
        commonAtoms (activation s) s (inputs s)) := by
  have hs := stack_bounds pre.stack
  have hlow := stack_sub_toNat pre.stack (offset := 56) (by decide)
  change (stackPtr s - 56).toNat = (stackPtr s).toNat - 56 at hlow
  have hret : Refine.Readable s.external (stackPtr s) 8 := by
    have h := stack_sub_readable pre.stack (offset := 0) (len := 8) (by decide) (by decide)
    have hr : MemReadable s (stackPtr s) 8 := by simpa using h
    exact ⟨hr.low, hr.mem⟩
  have hstack : Refine.Writable Machine.fnCode s.external (stackPtr s - 56) 56 := by
    apply writable_region pre.stack.1 pre.stack.2.1 (pre.avoids _ (by simp))
    · rw [hlow]; exact Nat.le_refl _
    · rw [hlow, stack_region_end]; omega
    · decide
  have hout : Refine.Writable Machine.fnCode s.external (s.regValue .rdi) 32 :=
    writable_region pre.outputBounded pre.outputAllocated (pre.avoids _ (by simp))
      (Nat.le_refl _) (Nat.le_refl _) (by decide)
  have hinput := memoryRegion_memReadable pre.inputBounded pre.inputAllocated
    (addr := s.regValue .rsi) (len := 33) (Nat.le_refl _) (Nat.le_refl _)
  have hmodulus := memoryRegion_memReadable pre.modulusRegion.bounded pre.modulusRegion.allocated
    (addr := s.regValue .rcx) (len := 32) (Nat.le_refl _) (Nat.le_refl _)
  have ho := disjoint_intervals (a := registerRegion s .rdi 32) (b := Stack.region s 56)
    (by change 0 < 32; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-56); omega)
    (pre.separation (1 : Fin 3) 2 (by decide))
  have hi := disjoint_intervals (a := registerRegion s .rsi 33) (b := Stack.region s 56)
    (by change 0 < 33; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-56); omega)
    (pre.separation (0 : Fin 3) 2 (by decide))
  have hm := disjoint_intervals (a := registerRegion s .rcx 32) (b := Stack.region s 56)
    (by change 0 < 32; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-56); omega)
    pre.modulusRegion.stack
  rw [stack_region_end] at ho hi hm
  change (s.regValue .rdi).toNat+32 ≤ (stackPtr s).toNat-56 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rdi).toNat at ho
  change (s.regValue .rsi).toNat+33 ≤ (stackPtr s).toNat-56 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rsi).toNat at hi
  change (s.regValue .rcx).toNat+32 ≤ (stackPtr s).toNat-56 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rcx).toNat at hm
  have wi : WordsAt s.external (s.regValue .rsi) 64 (inputs s).magnitude := by
    intro i hi
    have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases casesI with rfl | rfl | rfl | rfl <;> simp [inputs, wordAddr]
  have wm : WordsAt s.external (s.regValue .rcx) 64 (inputs s).modulus := by
    intro i hi
    have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases casesI with rfl | rfl | rfl | rfl <;> simp [inputs, wordAddr]
  rw [Atom.all_append]
  constructor
  · dsimp only [Machine.Correction.frameAt, Machine.Correction.frameAtG0,
      Atom.All, Atom.Holds, Atom.gpr]
    refine ⟨(Vector.getElem_ofFn _).trans rfl, ?_, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl,
      hret, rfl, inProgram_low pre.returnInProgram, hstack, ?_, pre.stack.2.2.2, trivial⟩
    · exact (Vector.getElem_ofFn _).trans (Reg.read_df_iff.mpr pre.directionFlag)
    · change (stackPtr s - 56).toNat+56 ≤ (stackPtr s).toNat
      rw [hlow]; omega
  · dsimp only [commonAtoms, Atom.All, Atom.Holds]
    refine ⟨(Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, hout, ?_, wi, wm, rfl, ⟨hinput.low, hinput.mem⟩,
      ⟨hmodulus.low, hmodulus.mem⟩, ?_, ?_, rfl, trivial⟩
    · change (s.regValue .rdi).toNat+32 ≤ (stackPtr s-56).toNat ∨
        (stackPtr s).toNat+8 ≤ (s.regValue .rdi).toNat
      rw [hlow]; exact ho
    · change (s.regValue .rsi).toNat+33 ≤ (stackPtr s-56).toNat ∨
        (stackPtr s).toNat ≤ (s.regValue .rsi).toNat
      rw [hlow]; omega
    · change (s.regValue .rcx).toNat+32 ≤ (stackPtr s-56).toNat ∨
        (stackPtr s).toNat ≤ (s.regValue .rcx).toNat
      rw [hlow]; omega

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution
