import Hkdf.Proofs.Key.Tail.Context
import Hkdf.Proofs.Key.Tail.Epilogue
import Hkdf.Proofs.Key.Tail.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Tail

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {key : ByteArray}
    (ctx : Context initial boundary key) (input : Ready initial boundary key s) :
    ∃ final, CalleeResult initial final boundary 64 stackBytes ∧
      (registerRegion initial .rdi 64).HasBytes final.external
        (Hkdf.Proofs.Common.HMAC.keyBlock key) := by
  obtain ⟨copyFuel, copied, copyRun, copyReady, _, copyEffect⟩ :=
    Copy.run boundary ctx.outerBoundary s
      (supportedMachine_readyToStep input.machine) (Copy.code input.loaded) (copy_pre ctx input)
  have current := copy_state ctx input copyRun copyReady copyEffect
  have copyFrame := copy_frame input copyEffect
  have copiedRsp : stackPtr copied = blockAddress initial :=
    (copyFrame.read (n := 64) (r := 4) (by simp [components])).trans input.rsp
  have rsp : rspOf copied = blockAddress initial := copiedRsp
  have src : rspOf s = blockAddress initial := input.rsp
  have dst : rbx.read s = initial.regValue .rdi := input.outputPointer
  have stores := copyEffect.writes
  simp only [Copy.effect, Write.AllHold, src, dst] at stores
  have words : ∀ j < 8,
      memLoad copied.external (initial.regValue .rdi + BitVec.ofNat 64 (8 * j)) 64 =
        memLoad s.external (blockAddress initial + BitVec.ofNat 64 (8 * j)) 64 := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
      j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read] using stores.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read] using stores.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read] using stores.2.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read] using stores.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read] using stores.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read] using stores.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read] using stores.2.2.2.2.2.2.2.2.1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, Operand.read] using stores.2.2.2.2.2.2.2.2.2
  have output := copy_qwords_hasBytes input.block (output_readable ctx current).mem words
  have returnWord : memLoad copied.external (rspOf copied + 376) 64 =
      (returnBoundary initial).rip := by
    rw [rsp]
    change memLoad copied.external (stackPtr initial - 376 + 376) 64 = _
    rw [BitVec.sub_add_cancel]
    exact current.saved.returnAddress
  have epiloguePre : Epilogue.Pre copied := by
    refine ⟨copyEffect.rip, ?_, ?_, ?_⟩
    · intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [rsp, blockAddress, Nat.reduceMul, Nat.reduceAdd,
          BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd,
          BitVec.ofNat_eq_ofNat] using
          Hkdf.Proofs.Key.stack_readable ctx current (offset := 40) (len := 8)
            (by decide) (by decide)
      · simpa only [rsp, blockAddress, Nat.reduceMul, Nat.reduceAdd,
          BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd,
          BitVec.ofNat_eq_ofNat] using
          Hkdf.Proofs.Key.stack_readable ctx current (offset := 32) (len := 8)
            (by decide) (by decide)
      · simpa only [rsp, blockAddress, Nat.reduceMul, Nat.reduceAdd,
          BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd,
          BitVec.ofNat_eq_ofNat] using
          Hkdf.Proofs.Key.stack_readable ctx current (offset := 24) (len := 8)
            (by decide) (by decide)
      · simpa only [rsp, blockAddress, Nat.reduceMul, Nat.reduceAdd,
          BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd,
          BitVec.ofNat_eq_ofNat] using
          Hkdf.Proofs.Key.stack_readable ctx current (offset := 16) (len := 8)
            (by decide) (by decide)
      · simpa only [rsp, blockAddress, Nat.reduceMul, Nat.reduceAdd,
          BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd,
          BitVec.ofNat_eq_ofNat] using
          Hkdf.Proofs.Key.stack_readable ctx current (offset := 8) (len := 8)
            (by decide) (by decide)
      · simpa only [rsp, blockAddress, Nat.reduceMul, Nat.reduceAdd,
          BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd,
          BitVec.ofNat_eq_ofNat] using
          Hkdf.Proofs.Key.stack_readable ctx current (offset := 0) (len := 8)
            (by decide) (by decide)
    · rw [returnWord]
      obtain ⟨byte, hb⟩ := ctx.returnInProgram
      exact programSections_low.codeLow _ hb
    · rw [returnWord]
      exact ctx.returnInProgram
  obtain ⟨exitFuel, final, exitRun, exitReady, _, exitEffect⟩ :=
    Epilogue.run boundary ctx.outerBoundary copied
      (supportedMachine_readyToStep current.machine) (Epilogue.code current.loaded) epiloguePre
  have noMemory : ∀ c ∈ (Epilogue.effect copied).components, ∀ a, ¬ c.Covers a := by
    simp [Epilogue.effect, Effect.components, Component.Covers]
  have running := current.toRunning.of_agrees exitRun exitReady exitEffect.agrees
    (by intro c hc a ha; exact (noMemory c hc a ha).elim) (by
      intro region member address contains inside
      exact ctx.avoids region (by simpa [writeRegions] using member)
        address contains (.inl inside)) (by simp [Epilogue.effect, Effect.components])
  have restored := exitEffect.writes
  simp only [Epilogue.effect, Write.AllHold, rsp] at restored
  refine ⟨final, {
    execution := running.execution
    rip := exitEffect.rip.trans returnWord
    rsp := ?_
    machine := running.machine
    abi := ?_
    frame := running.frame
    loaded := running.loaded
    allocated := running.allocated
  }, ?_⟩
  · have value := restored.1
    change (Operand.reg 4 : Operand 64).read final = stackPtr initial + 8
    simpa only [blockAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using value
  · refine ⟨?_, running.directionFlag, ?_, ?_⟩
    · intro register member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · have word := current.saved.words (.rbx, 40) (by simp)
        have value := restored.2.1
        simp only [blockAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd, Operand.read_reg64] at value word ⊢
        exact value.trans word
      · exact (exitEffect.agrees.read (n := 64) (r := 5)
          (by simp [Epilogue.effect, Effect.components])).trans current.rbp
      · have word := current.saved.words (.r12, 32) (by simp)
        have value := restored.2.2.1
        simp only [blockAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd, Operand.read_reg64] at value word ⊢
        exact value.trans word
      · have word := current.saved.words (.r13, 24) (by simp)
        have value := restored.2.2.2.1
        simp only [blockAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd, Operand.read_reg64] at value word ⊢
        exact value.trans word
      · have word := current.saved.words (.r14, 16) (by simp)
        have value := restored.2.2.2.2.1
        simp only [blockAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd, Operand.read_reg64] at value word ⊢
        exact value.trans word
      · have word := current.saved.words (.r15, 8) (by simp)
        have value := restored.2.2.2.2.2
        simp only [blockAddress, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceNeg, BitVec.reduceAdd, Operand.read_reg64] at value word ⊢
        exact value.trans word
    · exact (exitEffect.agrees.mxcsr
        (by simp [Epilogue.effect, Effect.components])).trans current.mxcsr
    · exact (exitEffect.agrees.fcw
        (by simp [Epilogue.effect, Effect.components])).trans current.fcw
  · rw [exitEffect.agrees.external noMemory]
    exact output

end Hkdf.Proofs.Key.Tail
