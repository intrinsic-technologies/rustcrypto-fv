import P256.Proofs.Verifying.Combination.Loop.MultiSave
import P256.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Imul.Generated.RRImm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def firstLengthBytes : List UInt8 :=
  [0x4c, 0x8b, 0x40, 0x10, 0x48, 0x8d, 0x4a, 0x01, 0x4c, 0x69, 0xca, 0x10, 0x01, 0, 0]

def firstLengthEffect (s : RamState) : Effect :=
  { rip := 0x10f00d
    writes := [⟨(.reg 8 : Operand 64), memLoad s.external (s.regValue .rax + 16) 64⟩,
      ⟨(.reg 1 : Operand 64), s.regValue .rdx + 1⟩,
      ⟨(.reg 9 : Operand 64), BitVec.ofInt 64 ((s.regValue .rdx).toInt * 272)⟩]
    flags := some (imulFlags (s.regValue .rdx) 272) }

theorem firstLength_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (LoadPre 0x10effe (fun s => s.regValue .rax + 16) 8)
      (codeRange 0x10effe firstLengthBytes) (Effect.post firstLengthEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10effe 0x4c (by simp [RexWPrefix]) 0
    (.base 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf002 (by decide))
  advance_then (lea_r64_effect_step 0x10f002 0x48 (by simp [RexWPrefix]) 1
    (.base 2 (.d8 1)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10effe firstLengthBytes 4 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf006 (by decide))⟩
  advance_then (imul_r64_r64_imm32_effect_step 0x10f006 0x4c (by simp [RexWPrefix]) 0xca rfl 272)
  case sub => exact codeRange_slice_subset 0x10effe firstLengthBytes 8 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf00d (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [firstLengthEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [firstLengthEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [firstLengthEffect] <;> rfl
  · x86_norm [firstLengthEffect]
    all_goals (repeat first | constructor | rfl)

theorem first_length [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {u : Nat} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10effe)
    (metadata : t.regValue .rax = s.regValue .rsi) (index : t.regValue .rdx = 0)
    (length : memLoad t.external digits 64 = BitVec.ofNat 64 (Naf.digits u).length) :
    ∃ fuel w, Advances boundary fuel t w ∧ State s w ∧ w.RIP = 0x10f011 ∧
      w.regValue .r8 = digits ∧ w.regValue .r9 = 0 ∧ w.regValue .rcx = 1 ∧
      w.regValue .rbx = BitVec.ofNat 64 (Naf.digits u).length ∧
      AgreesExcept [.reg 8, .reg 1, .reg 9, .reg 3, .flags, .rip] t w := by
  obtain ⟨fuel, a, runA, readyA, _, effectA⟩ :=
    firstLength_correct boundary pre.outerBoundary t
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xeffe firstLengthBytes
        (by decide) (by decide +kernel))
      ⟨rip, by rw [metadata]; exact metadata_readable pre state 16 (by decide)⟩
  have frameA : AgreesExcept [.reg 8, .reg 1, .reg 9, .flags, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have ptrA : a.regValue .r8 = digits := by
    have h := effectA.writes.1
    change a.regValue .r8 = memLoad t.external (t.regValue .rax + 16) 64 at h
    rw [metadata] at h
    exact h.trans ((metadata_read pre state 16 (by decide)).trans pre.digitPointer)
  have indexA : a.regValue .r9 = 0 := by
    have h := effectA.writes.2.2
    change a.regValue .r9 = BitVec.ofInt 64 ((t.regValue .rdx).toInt * 272) at h
    rw [index] at h
    exact h.trans (by decide +kernel)
  have nextA : a.regValue .rcx = 1 := by
    have h := effectA.writes.2.1
    change a.regValue .rcx = t.regValue .rdx + 1 at h
    rw [index] at h
    exact h.trans (by decide +kernel)
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (mov_r64_m64_effect_step 0x10f00d 0x4b (by simp [RexWPrefix]) 3
      (.sib 8 (some 9) 0 .none) (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf00d _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, by
        change MemReadable a (a.regValue .r8 + (a.regValue .r9 <<< 0) + 0) 8
        rw [ptrA, indexA, BitVec.shiftLeft_zero]
        change MemReadable a (digits + 0#64 + 0#64) 8
        rw [BitVec.add_zero, BitVec.add_zero]
        apply readable_of_grow (s := s) _ stateA.allocated
        exact memoryRegion_memReadable pre.digitsBounded pre.digitsAllocated
          (Nat.le_refl _) (by change digits.toNat + 8 ≤ digits.toNat + 544; omega)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf011 (by decide)))
  have frameW : AgreesExcept [.reg 3, .rip] a w := effectW.agrees
  have frame : AgreesExcept [.reg 8, .reg 1, .reg 9, .reg 3, .flags, .rip] t w :=
    (frameA.trans frameW).mono (by simp)
  refine ⟨fuel+1, w, runA.trans runW,
    state.after_registers readyW frame (by simp [Component.Covers]) (by simp), effectW.rip,
    (frameW.read (n := 64) (r := 8) (by simp)).trans ptrA,
    (frameW.read (n := 64) (r := 9) (by simp)).trans indexA,
    (frameW.read (n := 64) (r := 1) (by simp)).trans nextA, ?_, frame⟩
  have h := effectW.writes
  change w.regValue .rbx = memLoad a.external
    (a.regValue .r8 + (a.regValue .r9 <<< 0) + 0) 64 at h
  rw [ptrA, indexA, BitVec.shiftLeft_zero] at h
  change w.regValue .rbx = memLoad a.external (digits + 0#64 + 0#64) 64 at h
  rw [BitVec.add_zero, BitVec.add_zero, frameA.external (by simp [Component.Covers])] at h
  exact h.trans length

theorem entry_first_length [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q : Projective} {u v : Nat}
    (pre : MultiPre s boundary tables digits)
    (leftTable : Table.TableAt s tables (Table.oddTable p))
    (rightTable : Table.TableAt s (tables + 768) (Table.oddTable q))
    (leftDigits : Naf.NafAt s digits u) (rightDigits : Naf.NafAt s (digits + 272) v) :
    ∃ fuel t, Advances boundary fuel s t ∧ Memory s t tables digits p q u v ∧
      t.RIP = 0x10f011 ∧ t.regValue .rax = s.regValue .rsi ∧
      t.regValue .rdx = 0 ∧ t.regValue .rsi = 2 ∧
      t.regValue .r8 = digits ∧ t.regValue .r9 = 0 ∧ t.regValue .rcx = 1 ∧
      t.regValue .rbx = BitVec.ofNat 64 (Naf.digits u).length ∧
      memLoad t.external (stackPtr s - 400) 64 = 2 ∧
      memLoad t.external (stackPtr s - 392) 64 = s.regValue .rdi := by
  obtain ⟨a, runA, stateA, ripA, axA, dxA, siA, countA, outputA⟩ := entry pre
  have memoryA := memory_of_frame pre stateA leftTable rightTable leftDigits rightDigits
  obtain ⟨fuel, t, runT, stateT, ripT, ptrT, indexT, nextT, lengthT, frameT⟩ :=
    first_length pre stateA ripA axA dxA memoryA.leftDigits.length
  refine ⟨15+fuel, t, runA.trans runT,
    memory_of_frame pre stateT leftTable rightTable leftDigits rightDigits, ripT,
    (frameT.read (n := 64) (r := 0) (by simp)).trans axA,
    (frameT.read (n := 64) (r := 2) (by simp)).trans dxA,
    (frameT.read (n := 64) (r := 6) (by simp)).trans siA,
    ptrT, indexT, nextT, lengthT, ?_, ?_⟩
  · rw [frameT.external (by simp [Component.Covers])]
    exact countA
  · rw [frameT.external (by simp [Component.Covers])]
    exact outputA

end P256.Proofs.Verifying.Combination.Loop.Multi
