import P256.Proofs.Verifying.Combination.Loop.MultiLength
import X86Proofs.Instructions.Dec.Generated.R.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem counter_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {k : Nat} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f160)
    (count : t.regValue .rbx = BitVec.ofNat 64 (k+1))
    (cursor : memLoad t.external (stackPtr s - 376) 64 = digits + BitVec.ofNat 64 (k+8)) :
    ∃ w, Advances boundary 3 t w ∧ State s w ∧ w.RIP = 0x10f16b ∧
      w.regValue .rbx = BitVec.ofNat 64 k ∧
      w.regValue .r13 = digits + BitVec.ofNat 64 (k+7) ∧
      AgreesExcept [.reg 3, .reg 13, .flags, .rip] t w := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (dec_r64_effect_step 0x10f160 0x48 0xcb (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf160 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf163 (by decide)))
  have frameA : AgreesExcept [.reg 3, .flags, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have sub : t.regValue .rbx - 1 = BitVec.ofNat 64 k := by
    rw [count, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have countA : a.regValue .rbx = BitVec.ofNat 64 k := effectA.writes.trans sub
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (mov_r64_m64_effect_step 0x10f163 0x4c (by simp [RexWPrefix]) 5
      (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf163 _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, stack_readable pre.toCalleePre stateA (offset := 32) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf168 (by decide)))
  have frameB : AgreesExcept [.reg 13, .rip] a b := effectB.agrees
  have stateB := stateA.after_registers readyB frameB (by simp [Component.Covers]) (by simp)
  have cursorB : b.regValue .r13 = digits + BitVec.ofNat 64 (k+8) := by
    have h := effectB.writes
    change b.regValue .r13 = memLoad a.external (stackPtr a + 32#64) 64 at h
    rw [scalar_stack_address stateA.rsp (offset := 32) (by decide) (by decide),
      frameA.external (by simp [Component.Covers])] at h
    exact h.trans cursor
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (dec_r64_effect_step 0x10f168 0x49 0xcd (by simp [RexWPrefix]) rfl rfl).advances readyB
      (programText_slice (programLoaded_codeIn stateB.loaded) 0xf168 _
        (by decide) (by decide +kernel)) effectB.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf16b (by decide)))
  have frameW : AgreesExcept [.reg 13, .flags, .rip] b w := effectW.agrees
  have frame : AgreesExcept [.reg 3, .reg 13, .flags, .rip] t w :=
    ((frameA.trans frameB).trans frameW).mono (by simp)
  refine ⟨w, (runA.trans runB).trans runW,
    state.after_registers readyW frame (by simp [Component.Covers]) (by simp), effectW.rip,
    (frameW.read (n := 64) (r := 3) (by simp)).trans
      ((frameB.read (n := 64) (r := 3) (by simp)).trans countA), ?_, frame⟩
  have h := effectW.writes
  change w.regValue .r13 = b.regValue .r13 - 1 at h
  rw [cursorB] at h
  have eq : digits + BitVec.ofNat 64 (k+8) - 1 = digits + BitVec.ofNat 64 (k+7) := by
    rw [show k+8 = (k+7)+1 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  exact h.trans eq

end P256.Proofs.Verifying.Combination.Loop.Multi
