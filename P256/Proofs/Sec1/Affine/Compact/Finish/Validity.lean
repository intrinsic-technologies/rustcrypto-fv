import P256.Proofs.Sec1.Affine.Compact.Flags.Store
import P256.Proofs.Sec1.Affine.Uncompressed.Output.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem store_validity [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110560) :
    ∃ u, Advances boundary 1 t u ∧ Frame s u ∧ u.RIP = (0x110565 : BitVec 64) ∧
      memLoad u.external (stackPtr s - BitVec.ofNat 64 (760-88)) 8 =
        (t.regValue .rbp).setWidth 8 ∧
      AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 (760-88)) 1, .rip] t u := by
  have bound : 88 + 1 ≤ 712 := by decide
  have codeBound : (0x110560 : BitVec 64).toNat - 0x100000 + 5 ≤ 118431 := by decide
  have codeAddress : Extracted.textAddress + BitVec.ofNat 64 ((0x110560 : BitVec 64).toNat - 0x100000) = 0x110560 := by
    decide
  have code := programText_slice (programLoaded_codeIn state.loaded)
    ((0x110560 : BitVec 64).toNat-0x100000) [0x40,0x88,0x6c,0x24,0x58] codeBound (by decide +kernel)
  rw [codeAddress] at code
  have writable := ScalarFrame.stack_writable (frameOffset := 760) pre.toCalleePre state
    (offset := 88) (len := 1) (by decide) (by omega) (by decide)
  have address : stackPtr t + BitVec.ofNat 64 88 =
      stackPtr s - BitVec.ofNat 64 (760-88) :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by omega)
  obtain ⟨u,run,ready,effect⟩ := (P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x110560 0x40 (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl).advances
    (readyToStep state.machine state.bindingsSupported) code
    ⟨rip, ⟨writable.low, writable.mem, writable.tables⟩, by
      have h := ScalarFrame.stack_code (frameOffset := 760) pre.toCalleePre state
        (offset := 88) (len := 1) (by decide) (by omega) codeBound
      rwa [codeAddress] at h⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10565 (by decide)))
  have agrees : AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 (760-88)) 1, .rip] t u := by
    have h := effect.agrees
    simp only [storeEffect,Effect.components,
      List.map_cons,List.map_nil,Write.component,Operand.component,Nat.reduceDiv,
      List.append_nil] at h
    change AgreesExcept [.mem (stackPtr t + 88) 1, .rip] t u at h
    have address' : stackPtr t + 88 = stackPtr s - 672 := address
    rwa [address'] at h
  have frame : Frame s u := by
    apply state.after_effect pre.toCalleePre (by decide) ready agrees
    · intro c hc a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨ScalarFrame.workRegion s 3360,by simp,
          ScalarFrame.work_contains pre.toCalleePre (by omega) (by omega) ha⟩
      · exact ha.elim
    all_goals simp
  refine ⟨u,run,frame,effect.rip,?_,agrees⟩
  have value : memLoad u.external (stackPtr t + BitVec.ofNat 64 88) 8 =
      (t.regValue .rbp).setWidth 8 := effect.writes
  rwa [address] at value

end P256.Proofs.Sec1.Affine.Compact.Finish
