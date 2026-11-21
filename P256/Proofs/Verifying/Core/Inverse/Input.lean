import P256.Proofs.Verifying.Core.Inverse.Defs
import P256.Proofs.Scalar.Inverse.Parameters
import P256.Proofs.Field.Inverse.SafeGcd.Core.Input.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Inverse

open P256.Proofs.Scalar.Inverse

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core
open P256.Proofs.Field.Inverse.SafeGcd.Core.Input (readWords readWords_at writable_region fnCode_sub)
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines

def activation (s : RamState) : Activation :=
  ⟨s.external, stackPtr s, (returnBoundary s).rip, stackPtr s - 768,
    s.regValue .rbx, s.regValue .rbp, s.regValue .r12, s.regValue .r13,
    s.regValue .r14, s.regValue .r15, s.regValue .rdi, s.regValue .rsi,
    s.regValue .rdx, s.regValue .rcx, s.regValue .r8, s.regValue .r9,
    s.MXCSR, (Operand.ftw : Operand 16).read s, s.FP87_Control, s.FS⟩

def inputs (s : RamState) : Inputs := ⟨readWords s (s.regValue .rsi), s.MXCSR, s.FP87_Control⟩

theorem parameter_stack [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x112fd0 32 40 768) {address : BitVec 64}
    (bound : address.toNat + 32 < 2^32)
    (program : ∀ i : Fin 32, InProgram (address + BitVec.ofNat 64 i.val)) :
    address.toNat + 32 ≤ (stackPtr s).toNat - 768 ∨
      (stackPtr s).toNat + 8 ≤ address.toNat := by
  have hs := stack_bounds pre.stack
  have hd : (MemoryRegion.mk address.toNat 32).Disjoint (Stack.region s 768) := by
    intro a ha hb
    have index : a - address.toNat < 32 := by
      change address.toNat ≤ a ∧ a < address.toNat + 32 at ha
      omega
    have equal : address + BitVec.ofNat 64 (a - address.toNat) = BitVec.ofNat 64 a := by
      apply BitVec.eq_of_toNat_eq
      change address.toNat ≤ a ∧ a < address.toNat + 32 at ha
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    apply pre.avoids (Stack.region s 768) (by simp) (BitVec.ofNat 64 a)
    · change address.toNat ≤ a ∧ a < address.toNat + 32 at ha
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2^64 by omega)] using hb
    · exact .inl (equal ▸ program ⟨a - address.toNat, index⟩)
  have h := Correction.Execution.disjoint_intervals (a := ⟨address.toNat, 32⟩)
    (b := Stack.region s 768) (by change 0 < 32; decide)
    (by change 0 < (stackPtr s).toNat + 8 - ((stackPtr s).toNat - 768); omega) hd
  rw [stack_region_end] at h
  exact h

theorem parameter_words {s : RamState} {address : BitVec 64} {n : Nat}
    (h : SecretKeyFromBytes.Scalar.Nat256At s address n) :
    WordsAt s.external address 64
      (#v[BitVec.ofNat 64 n, BitVec.ofNat 64 (n / 2^64),
        BitVec.ofNat 64 (n / 2^128), BitVec.ofNat 64 (n / 2^192)]) := by
  intro i hi
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases casesI with rfl | rfl | rfl | rfl
  · simpa [wordAddr] using h.memLoad_limb 0 (by decide)
  · simpa [wordAddr] using h.memLoad_limb 1 (by decide)
  · simpa [wordAddr] using h.memLoad_limb 2 (by decide)
  · simpa [wordAddr] using h.memLoad_limb 3 (by decide)

variable [Bindings] {s : RamState} {boundary : ReturnBoundary}

theorem entry_ready (pre : CalleePre s boundary 0x112fd0 32 40 768) : EntryReady Machine.fnCode s :=
  ⟨readyToStep pre.machine pre.bindingsSupported, pre.machine.sse,
    (programLoaded_codeIn pre.loaded).mono (fun _ h => fnCode_sub h)⟩

theorem entry_atoms (pre : CalleePre s boundary 0x112fd0 32 40 768) :
    Atom.All Machine.fnCode (Machine.lifted.locationOf .l115020 s).arguments s.external
      (entryAtoms (activation s) (inputs s)) := by
  have hs := stack_bounds pre.stack
  have hlow := stack_sub_toNat pre.stack (offset := 768) (by decide)
  change (stackPtr s - 768).toNat = (stackPtr s).toNat - 768 at hlow
  have hret : Refine.Readable s.external (stackPtr s) 8 := by
    have h := stack_sub_readable pre.stack (offset := 0) (len := 8) (by decide) (by decide)
    have hr : MemReadable s (stackPtr s) 8 := by simpa using h
    exact ⟨hr.low, hr.mem⟩
  have hstack : Refine.Writable Machine.fnCode s.external (stackPtr s - 768) 768 := by
    apply writable_region pre.stack.1 pre.stack.2.1 (pre.avoids _ (by simp))
    · rw [hlow]; exact Nat.le_refl _
    · rw [hlow, stack_region_end]; omega
    · decide
  have hout : Refine.Writable Machine.fnCode s.external (s.regValue .rdi) 33 :=
    writable_region pre.outputBounded pre.outputAllocated (pre.avoids _ (by simp))
      (Nat.le_refl _) (by change (s.regValue .rdi).toNat + 33 ≤ (s.regValue .rdi).toNat + 40; omega) (by decide)
  have hinput := memoryRegion_memReadable pre.inputBounded pre.inputAllocated
    (addr := s.regValue .rsi) (len := 32) (Nat.le_refl _) (Nat.le_refl _)
  have hmval := parameters_modulus pre.loaded
  have htval := parameters_adjuster pre.loaded
  have hmodulus : Readable s.external 0x2025e0 32 :=
    ⟨by decide, fun i hi => by rw [hmval.2 i hi]; trivial⟩
  have hscale : Readable s.external 0x2025c0 32 :=
    ⟨by decide, fun i hi => by rw [htval.2 i hi]; trivial⟩
  have hm := parameter_stack pre (address := 0x2025e0) (by decide) (by
    have h : ∀ i : Fin 32, Extracted.programSections.fetchByte
        (0x2025e0 + BitVec.ofNat 64 i.val) =
        some (UInt8.ofNat (Nat.mod (P256.Spec.Operations.domain.n / 256 ^ i.val) 256)) := by decide +kernel
    exact fun i => ⟨_, h i⟩)
  have ht := parameter_stack pre (address := 0x2025c0) (by decide) (by
    have h : ∀ i : Fin 32, Extracted.programSections.fetchByte
        (0x2025c0 + BitVec.ofNat 64 i.val) =
        some (UInt8.ofNat (Nat.mod (1 / 256 ^ i.val) 256)) := by decide +kernel
    exact fun i => ⟨_, h i⟩)
  have ho := Correction.Execution.disjoint_intervals (a := registerRegion s .rdi 40) (b := Stack.region s 768)
    (by change 0 < 40; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-768); omega)
    (pre.separation (1 : Fin 3) 2 (by decide))
  have hi := Correction.Execution.disjoint_intervals (a := registerRegion s .rsi 32) (b := Stack.region s 768)
    (by change 0 < 32; decide) (by change 0 < (stackPtr s).toNat+8-((stackPtr s).toNat-768); omega)
    (pre.separation (0 : Fin 3) 2 (by decide))
  rw [stack_region_end] at ho hi
  change (s.regValue .rdi).toNat+40 ≤ (stackPtr s).toNat-768 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rdi).toNat at ho
  change (s.regValue .rsi).toNat+32 ≤ (stackPtr s).toNat-768 ∨
    (stackPtr s).toNat+8 ≤ (s.regValue .rsi).toNat at hi
  simp only [entryAtoms, Atom.all_append]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, (Vector.getElem_ofFn _).trans rfl,
    (Vector.getElem_ofFn _).trans rfl, trivial⟩
  · dsimp only [Machine.Inverse.frameAt, Machine.Inverse.frameAtG0,
      Atom.All, Atom.Holds, Atom.gpr]
    refine ⟨(Vector.getElem_ofFn _).trans rfl, ?_, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl, (Vector.getElem_ofFn _).trans rfl,
      hret, rfl, inProgram_low pre.returnInProgram, hstack, ?_, pre.stack.2.2.2, trivial⟩
    · exact (Vector.getElem_ofFn _).trans (Reg.read_df_iff.mpr pre.directionFlag)
    · change (stackPtr s - 768).toNat+768 ≤ (stackPtr s).toNat
      rw [hlow]; omega
  · simp only [outputAtoms, Atom.All, Atom.Holds]
    refine ⟨hout, ?_, trivial⟩
    change (s.regValue .rdi).toNat+33 ≤ (stackPtr s-768).toNat ∨
      (stackPtr s).toNat+8 ≤ (s.regValue .rdi).toNat
    rw [hlow]; omega
  · simp only [inputAtoms, Atom.All, Atom.Holds]
    refine ⟨readWords_at _ _, ⟨hinput.low,hinput.mem⟩, ?_,
      parameter_words hmval, parameter_words htval, hmodulus, hscale, ?_, ?_, trivial⟩
    · change (s.regValue .rsi).toNat+32 ≤ (stackPtr s-768).toNat ∨
        (stackPtr s).toNat ≤ (s.regValue .rsi).toNat
      rw [hlow]; omega
    · change 0x202600 ≤ (stackPtr s-768).toNat ∨ (stackPtr s).toNat ≤ 0x2025e0
      rw [hlow]; change 0x202600 ≤ _ ∨ _ ≤ 0x2025e0 at hm; omega
    · change 0x2025e0 ≤ (stackPtr s-768).toNat ∨ (stackPtr s).toNat ≤ 0x2025c0
      rw [hlow]; change 0x2025e0 ≤ _ ∨ _ ≤ 0x2025c0 at ht; omega

end P256.Proofs.Verifying.Core.Inverse
