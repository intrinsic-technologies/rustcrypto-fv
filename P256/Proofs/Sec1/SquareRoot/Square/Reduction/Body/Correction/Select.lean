import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Difference
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Arithmetic
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Field.Representation
import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import P256.Proofs.Common.Instructions.Setb.Triple
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Instructions.Carry.Memory.Effect
import P256.Proofs.Common.Instructions.Sar.Triple
import P256.Proofs.Common.Instructions.Neg64
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem after_stack (pre : ReductionPre s boundary)
    (frame : ScalarFrame.FrameState s t 32 112 112) (ready : ReadyToStep u)
    {len : Nat} (hl : len ≤ 8)
    (agrees : AgreesExcept [.mem (stackPtr t + 8) len, .rip] t u) :
    ScalarFrame.FrameState s u 32 112 112 := by
  apply frame.after_effect pre.toCalleePre (by decide) ready agrees ?_ (by simp)
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · refine ⟨ScalarFrame.workRegion s 112, by simp, ?_⟩
    apply ScalarFrame.work_contains pre.toCalleePre (offset := 104) (len := len)
      (by decide) (by omega)
    change (Component.mem (stackPtr t + BitVec.ofNat 64 8) len).Covers a at ha
    rw [ScalarFrame.scalar_stack_address (frameOffset := 112) frame.rsp
      (offset := 8) (by decide) (by decide)] at ha
    exact ha
  · exact ha.elim

theorem byte_writable (pre : ReductionPre s boundary)
    (frame : ScalarFrame.FrameState s t 32 112 112) :
    MemWritable t (stackPtr t + 8) 1 := by
  have w := ScalarFrame.stack_writable pre.toCalleePre frame
    (offset := 8) (len := 1) (by decide) (by decide) (by decide)
  exact ⟨w.low, w.mem, w.tables⟩

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteLogic
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.Neg64
open P256.Proofs.Common.Instructions.CrossPageStore

theorem prefix_correct [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s u 32 112 112)
    (rip : u.RIP = 0x1136fc) :
    ∃ w, (∃ fuel, Advances boundary fuel u w) ∧
      ScalarFrame.FrameState s w 32 112 112 ∧ w.RIP = 0x113709 ∧
      w.regValue .rax = u.regValue .rdi ∧
      (Operand.reg 7 : Operand 8).read w =
        (if u.regValue .r12 = 0 then 1 else 0) &&& (u.regValue .rbp).setWidth 8 ∧
      AgreesExcept [.reg 0, .reg 7, .flags, .rip] u w := by
  have f0 := frame
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_r64_r64_effect_step 0x1136fc 0x48 0xf8 (by simp [RexWPrefix]) rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x136fc _
        (by decide) (by decide +kernel))
      rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x136ff (by decide)))
  change (movR64R64Effect 0x1136fc 0 7 u).Holds u u1 at e1
  have a1 : AgreesExcept [.reg 0, .rip] u u1 := by
    simpa [movR64R64Effect, Effect.components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := f0.after_registers ready1 a1 (by simp [Component.Covers]) (by simp)
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (test_r64_r64_effect_step 0x1136ff 0x4d 0xe4 (by simp [RexWPrefix]) rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x136ff _
        (by decide) (by decide +kernel))
      e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13702 (by decide)))
  change (testR64R64Effect 0x1136ff 12 12 u1).Holds u1 u2 at e2
  have a2 : AgreesExcept [.flags, .rip] u1 u2 := by
    simpa [testR64R64Effect, Effect.components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := f1.after_registers ready2 a2 (by simp [Component.Covers]) (by simp)
  have high : (Operand.reg 12 : Operand 64).read u1 = u.regValue .r12 := a1.read (by simp)
  have hz : (StatusFlags.ofRFLAGS u2.RFLAGS).ZF = (u.regValue .r12 == 0) := by
    simpa only [testR64R64Effect, testFlags, high, BitVec.and_self, FlagAllows]
      using e2.flags.2.2.2.1
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (setcc_r8_rex_effect_step 0x113702 0x40 0x94 0xc7 (by simp [RexPrefix]) (by simp [SupportedOpcode]) rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x13702 _
        (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13706 (by decide)))
  change (setccR8Effect 0x113702 4 7 4 u2).Holds u2 u3 at e3
  have a3 : AgreesExcept [.reg 7, .rip] u2 u3 := by
    simpa [setccR8Effect, Effect.components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := f2.after_registers ready3 a3 (by simp [Component.Covers]) (by simp)
  have byte : (Operand.reg 7 : Operand 8).read u3 =
      if u.regValue .r12 = 0 then 1 else 0 := by
    have hw := congrArg (BitVec.setWidth 8) e3.writes
    rw [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8] at hw
    change (Operand.reg 7 : Operand 8).read u3 =
      (if (StatusFlags.ofRFLAGS u2.RFLAGS).ZF then 1 else 0) at hw
    simpa only [hz, beq_iff_eq] using hw
  have bp : (Operand.reg 5 : Operand 8).read u3 = (u.regValue .rbp).setWidth 8 :=
    ((a1.trans a2).trans a3).read (by simp)
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (and_r8_r8_rex_effect_step 0x113706 0x40 0xef (by simp [RexPrefix]) rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x13706 _
        (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13709 (by decide)))
  change (andR8R8Effect 0x113706 7 5 u3).Holds u3 u4 at e4
  have a4 : AgreesExcept [.reg 7, .flags, .rip] u3 u4 := by
    simpa [andR8R8Effect, Effect.components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := f3.after_registers ready4 a4 (by simp [Component.Covers]) (by simp)
  have ag : AgreesExcept [.reg 0, .reg 7, .flags, .rip] u u4 := (((a1.trans a2).trans a3).trans a4).mono (by simp)
  refine ⟨u4, ⟨4, (((run1.trans run2).trans run3).trans run4)⟩, f4, e4.rip, ?_, ?_, ag⟩
  · exact (((a2.trans a3).trans a4).read (r := 0) (n := 64) (by simp)).trans e1.writes
  · have hw := congrArg (BitVec.setWidth 8) e4.writes
    rw [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8] at hw
    exact hw.trans (by rw [byte, bp])

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteLogic
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.Neg64
open P256.Proofs.Common.Instructions.CrossPageStore

set_option maxHeartbeats 800000 in
theorem scratch [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s u 32 112 112)
    (rip : u.RIP = 0x113709) :
    ∃ w, (∃ fuel, Advances boundary fuel u w) ∧
      ScalarFrame.FrameState s w 32 112 112 ∧ w.RIP = 0x113736 ∧
      w.regValue .rdx = u.regValue .rdx + slot s u 24 ∧
      AgreesExcept [.reg 2, .reg 12, .flags, .rip,
        .mem (stackPtr u + 8) 8] u w := by
  have f0 := frame
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_m8_r8_effect_step 0x113709 0x40 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x13709 _
        (by decide) (by decide +kernel))
      ⟨rip, byte_writable pre f0, ScalarFrame.stack_code pre.toCalleePre f0 (offset := 8) (len := 1) (codeOffset := 0x13709) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1370e (by decide)))
  change (storeEffect 0x113709 5 (fun t => stackPtr t + 8) (fun t => (Operand.reg 7 : Operand 8).read t) u).Holds u u1 at e1
  have a1 : AgreesExcept [.mem (stackPtr u + 8) 1, .rip] u u1 := by
    simpa [storeEffect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := after_stack pre f0 ready1 (by decide) a1
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (lea_r64_effect_step 0x11370e 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x1370e _
        (by decide) (by decide +kernel))
      e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13713 (by decide)))
  change (leaR64Effect 0x11370e 12 (.sib 4 none 0 (.d8 8)) u1).Holds u1 u2 at e2
  have a2 : AgreesExcept [.reg 12, .rip] u1 u2 := by
    simpa [leaR64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := f1.after_registers ready2 a2 (by simp [Component.Covers]) (by simp)
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (movzx_r_m8_rex_effect_step 0x113713 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (fun _ => rfl) 4 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x13713 _
        (by decide) (by decide +kernel))
      ⟨e2.rip, ScalarFrame.stack_readable pre.toCalleePre f2 (offset := 8) (len := 1) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13719 (by decide)))
  change (movzxR32M8Effect 0x113713 6 12 (.sib 4 none 0 (.d8 8)) u2).Holds u2 u3 at e3
  have a3 : AgreesExcept [.reg 12, .rip] u2 u3 := by
    simpa [movzxR32M8Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := f2.after_registers ready3 a3 (by simp [Component.Covers]) (by simp)
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (dec_r64_effect_step 0x113719 0x49 0xcc (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x13719 _
        (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1371c (by decide)))
  change (decR64Effect 0x113719 12 u3).Holds u3 u4 at e4
  have a4 : AgreesExcept [.reg 12, .flags, .rip] u3 u4 := by
    simpa [decR64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := f3.after_registers ready4 a4 (by simp [Component.Covers]) (by simp)
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (and_r64_r64_effect_step 0x11371c 0x49 0xec (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x1371c _
        (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1371f (by decide)))
  change (andR64R64Effect 0x11371c 12 5 u4).Holds u4 u5 at e5
  have a5 : AgreesExcept [.reg 12, .flags, .rip] u4 u5 := by
    simpa [andR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e5.agrees
  have f5 := f4.after_registers ready5 a5 (by simp [Component.Covers]) (by simp)
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (sar_r64_imm8_effect_step 0x11371f 0x49 0xfc 63 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x1371f _
        (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13723 (by decide)))
  change (sarR64Effect 0x11371f 4 12 63 u5).Holds u5 u6 at e6
  have a6 : AgreesExcept [.reg 12, .flags, .rip] u5 u6 := by
    simpa [sarR64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e6.agrees
  have f6 := f5.after_registers ready6 a6 (by simp [Component.Covers]) (by simp)
  obtain ⟨u7, run7, ready7, e7⟩ :=
    (add_r64_m64_effect_step 0x113723 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x13723 _
        (by decide) (by decide +kernel))
      ⟨e6.rip, ScalarFrame.stack_readable pre.toCalleePre f6 (offset := 24) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13728 (by decide)))
  change (addR64M64Effect 0x113723 2 (.sib 4 none 0 (.d8 24)) u6).Holds u6 u7 at e7
  have a7 : AgreesExcept [.reg 2, .flags, .rip] u6 u7 := by
    simpa [addR64M64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e7.agrees
  have f7 := f6.after_registers ready7 a7 (by simp [Component.Covers]) (by simp)
  have keep24 : slot s u6 24 = slot s u 24 := by
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees
      (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6)
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    rintro ⟨j, hj, he⟩
    rw [frame.rsp] at he
    exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj)
      (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have top : u7.regValue .rdx = u.regValue .rdx + slot s u 24 := by
    have hw := e7.writes
    change u7.regValue .rdx = (Operand.reg 2 : Operand 64).read u6 +
      memLoad u6.external (stackPtr u6 + 24) 64 at hw
    rw [f6.rsp] at hw
    change u7.regValue .rdx = (Operand.reg 2 : Operand 64).read u6 + slot s u6 24 at hw
    rw [keep24, ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6)).read (r := 2) (n := 64) (by simp)] at hw
    exact hw
  obtain ⟨u8, run8, ready8, e8⟩ :=
    (adc_r64_m64_effect_step 0x113728 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x13728 _
        (by decide) (by decide +kernel))
      ⟨e7.rip, ScalarFrame.stack_readable pre.toCalleePre f7 (offset := 16) (len := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1372d (by decide)))
  change (adcR64M64Effect 0x113728 12 (.sib 4 none 0 (.d8 16)) u7).Holds u7 u8 at e8
  have a8 : AgreesExcept [.reg 12, .flags, .rip] u7 u8 := by
    simpa [adcR64M64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e8.agrees
  have f8 := f7.after_registers ready8 a8 (by simp [Component.Covers]) (by simp)
  obtain ⟨u9, run9, ready9, e9⟩ :=
    (shr_r64_imm8_effect_step 0x11372d 0x49 0xec 63 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x1372d _
        (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13731 (by decide)))
  change (shrR64Effect 0x11372d 4 12 63 u8).Holds u8 u9 at e9
  have a9 : AgreesExcept [.reg 12, .flags, .rip] u8 u9 := by
    simpa [shrR64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e9.agrees
  have f9 := f8.after_registers ready9 a9 (by simp [Component.Covers]) (by simp)
  obtain ⟨u10, run10, ready10, e10⟩ :=
    (mov_m64_r64_effect_step_any 0x113731 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x13731 _
        (by decide) (by decide +kernel))
      ⟨e9.rip, ScalarFrame.stack_writable pre.toCalleePre f9 (offset := 8) (len := 8) (by decide) (by decide) (by decide), ScalarFrame.stack_code pre.toCalleePre f9 (offset := 8) (len := 8) (codeOffset := 0x13731) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13736 (by decide)))
  change (movM64R64Effect 0x113731 12 (.sib 4 none 0 (.d8 8)) u9).Holds u9 u10 at e10
  have a10 : AgreesExcept [.mem (stackPtr u9 + 8) 8, .rip] u9 u10 := by
    simpa [movM64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e10.agrees
  have f10 := after_stack pre f9 ready10 (by decide) a10
  have sp : stackPtr u9 = stackPtr u := (((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9)).read (r := 4) (n := 64) (by simp)
  have ag : AgreesExcept [.reg 2, .reg 12, .flags, .rip,
      .mem (stackPtr u + 8) 8] u u10 := by
    apply (((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).widen
    · intro c hc hm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, sp, or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem]
    · intro a c hc ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, sp, or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      · obtain ⟨i, hi, rfl⟩ := ha
        exact ⟨.mem (stackPtr u + 8) 8, by simp, i, by omega, rfl⟩
      · exact ⟨.mem (stackPtr u + 8) 8, by simp, ha⟩
  exact ⟨u10, ⟨10, (((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10)⟩,
    f10, e10.rip, ((((a8.trans a9).trans a10)).read (r := 2) (n := 64) (by simp)).trans top, ag⟩

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteLogic
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.Neg64
open P256.Proofs.Common.Instructions.CrossPageStore

set_option maxHeartbeats 800000 in
theorem select_low [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s u 32 112 112)
    (rip : u.RIP = 0x113736) :
    ∃ w, (∃ fuel, Advances boundary fuel u w) ∧
      ScalarFrame.FrameState s w 32 112 112 ∧ w.RIP = 0x113752 ∧
      (Operand.reg 10 : Operand 64).read w = selectWord
        ((Operand.reg 3 : Operand 64).read u) ((Operand.reg 6 : Operand 64).read u)
        (((Operand.reg 7 : Operand 8).read u).setWidth 64) ∧
      AgreesExcept [.reg 11, .reg 10, .reg 3, .flags, .rip, .mem (stackPtr u + 8) 1] u w := by
  have f0 := frame
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_m8_r8_effect_step 0x113736 0x40 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x13736 _
        (by decide) (by decide +kernel))
      ⟨rip, byte_writable pre f0, ScalarFrame.stack_code pre.toCalleePre f0 (offset := 8) (len := 1) (codeOffset := 0x13736) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1373b (by decide)))
  change (storeEffect 0x113736 5 (fun t => stackPtr t + 8) (fun t => (Operand.reg 7 : Operand 8).read t) u).Holds u u1 at e1
  have a1 : AgreesExcept [.mem (stackPtr u + 8) 1, .rip] u u1 := by
    simpa [storeEffect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := after_stack pre f0 ready1 (by decide) a1
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (lea_r64_effect_step 0x11373b 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x1373b _
        (by decide) (by decide +kernel))
      e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13740 (by decide)))
  change (leaR64Effect 0x11373b 11 (.sib 4 none 0 (.d8 8)) u1).Holds u1 u2 at e2
  have a2 : AgreesExcept [.reg 11, .rip] u1 u2 := by
    simpa [leaR64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := f1.after_registers ready2 a2 (by simp [Component.Covers]) (by simp)
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (movzx_r_m8_rex_effect_step 0x113740 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (fun _ => rfl) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x13740 _
        (by decide) (by decide +kernel))
      ⟨e2.rip, ScalarFrame.stack_readable pre.toCalleePre f2 (offset := 8) (len := 1) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13746 (by decide)))
  change (movzxR32M8Effect 0x113740 6 10 (.sib 4 none 0 (.d8 8)) u2).Holds u2 u3 at e3
  have a3 : AgreesExcept [.reg 10, .rip] u2 u3 := by
    simpa [movzxR32M8Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := f2.after_registers ready3 a3 (by simp [Component.Covers]) (by simp)
  have byteLoad : (Operand.reg 10 : Operand 64).read u3 =
      (((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e3.writes
    change (Operand.reg 10 : Operand 64).read u3 =
      (memLoad u2.external (stackPtr u2 + 8) 8).setWidth 64 at hw
    have sp : stackPtr u2 = stackPtr u := ((a1.trans a2)).read (r := 4) (n := 64) (by simp)
    rw [sp] at hw
    rw [a2.external (by simp [Component.Covers])] at hw
    exact hw.trans (congrArg (BitVec.setWidth 64) e1.writes)
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (xor_r64_r64_effect_step 0x113746 0x48 0xf3 (by simp [RexWPrefix]) rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x13746 _
        (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13749 (by decide)))
  change (xorR64R64Effect 0x113746 3 6 u3).Holds u3 u4 at e4
  have a4 : AgreesExcept [.reg 3, .flags, .rip] u3 u4 := by
    simpa [xorR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := f3.after_registers ready4 a4 (by simp [Component.Covers]) (by simp)
  have xorInput : (Operand.reg 3 : Operand 64).read u4 =
      ((Operand.reg 3 : Operand 64).read u) ^^^ ((Operand.reg 6 : Operand 64).read u) := by
    have hw := e4.writes
    change (Operand.reg 3 : Operand 64).read u4 =
      ((Operand.reg 3 : Operand 64).read u3) ^^^ ((Operand.reg 6 : Operand 64).read u3) at hw
    rw [(((a1.trans a2).trans a3)).read (r := 3) (n := 64) (by simp), (((a1.trans a2).trans a3)).read (r := 6) (n := 64) (by simp)] at hw
    exact hw
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (neg_r64_effect_step 0x113749 0x49 0xda (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x13749 _
        (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1374c (by decide)))
  change (negR64Effect 0x113749 10 u4).Holds u4 u5 at e5
  have a5 : AgreesExcept [.reg 10, .flags, .rip] u4 u5 := by
    simpa [negR64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e5.agrees
  have f5 := f4.after_registers ready5 a5 (by simp [Component.Covers]) (by simp)
  have mask : (Operand.reg 10 : Operand 64).read u5 =
      -(((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e5.writes
    change (Operand.reg 10 : Operand 64).read u5 = -((Operand.reg 10 : Operand 64).read u4) at hw
    rw [(a4).read (r := 10) (n := 64) (by simp), byteLoad] at hw
    exact hw
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (and_r64_r64_effect_step 0x11374c 0x49 0xda (by simp [RexWPrefix]) rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x1374c _
        (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1374f (by decide)))
  change (andR64R64Effect 0x11374c 10 3 u5).Holds u5 u6 at e6
  have a6 : AgreesExcept [.reg 10, .flags, .rip] u5 u6 := by
    simpa [andR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e6.agrees
  have f6 := f5.after_registers ready6 a6 (by simp [Component.Covers]) (by simp)
  have masked : (Operand.reg 10 : Operand 64).read u6 =
      -(((Operand.reg 7 : Operand 8).read u).setWidth 64) &&&
        (((Operand.reg 3 : Operand 64).read u) ^^^ ((Operand.reg 6 : Operand 64).read u)) := by
    have hw := e6.writes
    change (Operand.reg 10 : Operand 64).read u6 =
      ((Operand.reg 10 : Operand 64).read u5) &&& ((Operand.reg 3 : Operand 64).read u5) at hw
    rw [mask, (a5).read (r := 3) (n := 64) (by simp), xorInput] at hw
    exact hw
  obtain ⟨u7, run7, ready7, e7⟩ :=
    (xor_r64_r64_effect_step 0x11374f 0x49 0xf2 (by simp [RexWPrefix]) rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x1374f _
        (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13752 (by decide)))
  change (xorR64R64Effect 0x11374f 10 6 u6).Holds u6 u7 at e7
  have a7 : AgreesExcept [.reg 10, .flags, .rip] u6 u7 := by
    simpa [xorR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e7.agrees
  have f7 := f6.after_registers ready7 a7 (by simp [Component.Covers]) (by simp)
  have selected : (Operand.reg 10 : Operand 64).read u7 = selectWord
      ((Operand.reg 3 : Operand 64).read u) ((Operand.reg 6 : Operand 64).read u)
      (((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e7.writes
    change (Operand.reg 10 : Operand 64).read u7 =
      ((Operand.reg 10 : Operand 64).read u6) ^^^ ((Operand.reg 6 : Operand 64).read u6) at hw
    rw [masked, ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6)).read (r := 6) (n := 64) (by simp)] at hw
    exact hw
  have ag : AgreesExcept [.reg 11, .reg 10, .reg 3, .flags, .rip, .mem (stackPtr u + 8) 1] u u7 := ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).mono (by simp)
  exact ⟨u7, ⟨7, ((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7)⟩, f7, e7.rip, selected, ag⟩

set_option maxHeartbeats 800000 in
theorem select_middleLow [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s u 32 112 112)
    (rip : u.RIP = 0x113752) :
    ∃ w, (∃ fuel, Advances boundary fuel u w) ∧
      ScalarFrame.FrameState s w 32 112 112 ∧ w.RIP = 0x113768 ∧
      (Operand.reg 6 : Operand 64).read w = selectWord
        ((Operand.reg 1 : Operand 64).read u) ((Operand.reg 9 : Operand 64).read u)
        (((Operand.reg 7 : Operand 8).read u).setWidth 64) ∧
      AgreesExcept [.reg 6, .reg 1, .flags, .rip, .mem (stackPtr u + 8) 1] u w := by
  have f0 := frame
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_m8_r8_effect_step 0x113752 0x40 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x13752 _
        (by decide) (by decide +kernel))
      ⟨rip, byte_writable pre f0, ScalarFrame.stack_code pre.toCalleePre f0 (offset := 8) (len := 1) (codeOffset := 0x13752) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13757 (by decide)))
  change (storeEffect 0x113752 5 (fun t => stackPtr t + 8) (fun t => (Operand.reg 7 : Operand 8).read t) u).Holds u u1 at e1
  have a1 : AgreesExcept [.mem (stackPtr u + 8) 1, .rip] u u1 := by
    simpa [storeEffect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := after_stack pre f0 ready1 (by decide) a1
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (movzx_r32_m8_effect_step 0x113757 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x13757 _
        (by decide) (by decide +kernel))
      ⟨e1.rip, ScalarFrame.stack_readable pre.toCalleePre f1 (offset := 8) (len := 1) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1375c (by decide)))
  change (movzxR32M8Effect 0x113757 5 6 (.sib 4 none 0 (.d8 8)) u1).Holds u1 u2 at e2
  have a2 : AgreesExcept [.reg 6, .rip] u1 u2 := by
    simpa [movzxR32M8Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := f1.after_registers ready2 a2 (by simp [Component.Covers]) (by simp)
  have byteLoad : (Operand.reg 6 : Operand 64).read u2 =
      (((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e2.writes
    change (Operand.reg 6 : Operand 64).read u2 =
      (memLoad u1.external (stackPtr u1 + 8) 8).setWidth 64 at hw
    have sp : stackPtr u1 = stackPtr u := (a1).read (r := 4) (n := 64) (by simp)
    rw [sp] at hw
    exact hw.trans (congrArg (BitVec.setWidth 64) e1.writes)
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (xor_r64_r64_effect_step 0x11375c 0x4c 0xc9 (by simp [RexWPrefix]) rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x1375c _
        (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1375f (by decide)))
  change (xorR64R64Effect 0x11375c 1 9 u2).Holds u2 u3 at e3
  have a3 : AgreesExcept [.reg 1, .flags, .rip] u2 u3 := by
    simpa [xorR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := f2.after_registers ready3 a3 (by simp [Component.Covers]) (by simp)
  have xorInput : (Operand.reg 1 : Operand 64).read u3 =
      ((Operand.reg 1 : Operand 64).read u) ^^^ ((Operand.reg 9 : Operand 64).read u) := by
    have hw := e3.writes
    change (Operand.reg 1 : Operand 64).read u3 =
      ((Operand.reg 1 : Operand 64).read u2) ^^^ ((Operand.reg 9 : Operand 64).read u2) at hw
    rw [((a1.trans a2)).read (r := 1) (n := 64) (by simp), ((a1.trans a2)).read (r := 9) (n := 64) (by simp)] at hw
    exact hw
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (neg_r64_effect_step 0x11375f 0x48 0xde (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x1375f _
        (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13762 (by decide)))
  change (negR64Effect 0x11375f 6 u3).Holds u3 u4 at e4
  have a4 : AgreesExcept [.reg 6, .flags, .rip] u3 u4 := by
    simpa [negR64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := f3.after_registers ready4 a4 (by simp [Component.Covers]) (by simp)
  have mask : (Operand.reg 6 : Operand 64).read u4 =
      -(((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e4.writes
    change (Operand.reg 6 : Operand 64).read u4 = -((Operand.reg 6 : Operand 64).read u3) at hw
    rw [(a3).read (r := 6) (n := 64) (by simp), byteLoad] at hw
    exact hw
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (and_r64_r64_effect_step 0x113762 0x48 0xce (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x13762 _
        (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13765 (by decide)))
  change (andR64R64Effect 0x113762 6 1 u4).Holds u4 u5 at e5
  have a5 : AgreesExcept [.reg 6, .flags, .rip] u4 u5 := by
    simpa [andR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e5.agrees
  have f5 := f4.after_registers ready5 a5 (by simp [Component.Covers]) (by simp)
  have masked : (Operand.reg 6 : Operand 64).read u5 =
      -(((Operand.reg 7 : Operand 8).read u).setWidth 64) &&&
        (((Operand.reg 1 : Operand 64).read u) ^^^ ((Operand.reg 9 : Operand 64).read u)) := by
    have hw := e5.writes
    change (Operand.reg 6 : Operand 64).read u5 =
      ((Operand.reg 6 : Operand 64).read u4) &&& ((Operand.reg 1 : Operand 64).read u4) at hw
    rw [mask, (a4).read (r := 1) (n := 64) (by simp), xorInput] at hw
    exact hw
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (xor_r64_r64_effect_step 0x113765 0x4c 0xce (by simp [RexWPrefix]) rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x13765 _
        (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13768 (by decide)))
  change (xorR64R64Effect 0x113765 6 9 u5).Holds u5 u6 at e6
  have a6 : AgreesExcept [.reg 6, .flags, .rip] u5 u6 := by
    simpa [xorR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e6.agrees
  have f6 := f5.after_registers ready6 a6 (by simp [Component.Covers]) (by simp)
  have selected : (Operand.reg 6 : Operand 64).read u6 = selectWord
      ((Operand.reg 1 : Operand 64).read u) ((Operand.reg 9 : Operand 64).read u)
      (((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e6.writes
    change (Operand.reg 6 : Operand 64).read u6 =
      ((Operand.reg 6 : Operand 64).read u5) ^^^ ((Operand.reg 9 : Operand 64).read u5) at hw
    rw [masked, (((((a1.trans a2).trans a3).trans a4).trans a5)).read (r := 9) (n := 64) (by simp)] at hw
    exact hw
  have ag : AgreesExcept [.reg 6, .reg 1, .flags, .rip, .mem (stackPtr u + 8) 1] u u6 := (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).mono (by simp)
  exact ⟨u6, ⟨6, (((((run1.trans run2).trans run3).trans run4).trans run5).trans run6)⟩, f6, e6.rip, selected, ag⟩

set_option maxHeartbeats 800000 in
theorem select_middleHigh [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s u 32 112 112)
    (rip : u.RIP = 0x113768) :
    ∃ w, (∃ fuel, Advances boundary fuel u w) ∧
      ScalarFrame.FrameState s w 32 112 112 ∧ w.RIP = 0x11377e ∧
      (Operand.reg 1 : Operand 64).read w = selectWord
        ((Operand.reg 8 : Operand 64).read u) ((Operand.reg 14 : Operand 64).read u)
        (((Operand.reg 7 : Operand 8).read u).setWidth 64) ∧
      AgreesExcept [.reg 1, .reg 8, .flags, .rip, .mem (stackPtr u + 8) 1] u w := by
  have f0 := frame
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_m8_r8_effect_step 0x113768 0x40 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x13768 _
        (by decide) (by decide +kernel))
      ⟨rip, byte_writable pre f0, ScalarFrame.stack_code pre.toCalleePre f0 (offset := 8) (len := 1) (codeOffset := 0x13768) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1376d (by decide)))
  change (storeEffect 0x113768 5 (fun t => stackPtr t + 8) (fun t => (Operand.reg 7 : Operand 8).read t) u).Holds u u1 at e1
  have a1 : AgreesExcept [.mem (stackPtr u + 8) 1, .rip] u u1 := by
    simpa [storeEffect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := after_stack pre f0 ready1 (by decide) a1
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (movzx_r32_m8_effect_step 0x11376d 1 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x1376d _
        (by decide) (by decide +kernel))
      ⟨e1.rip, ScalarFrame.stack_readable pre.toCalleePre f1 (offset := 8) (len := 1) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13772 (by decide)))
  change (movzxR32M8Effect 0x11376d 5 1 (.sib 4 none 0 (.d8 8)) u1).Holds u1 u2 at e2
  have a2 : AgreesExcept [.reg 1, .rip] u1 u2 := by
    simpa [movzxR32M8Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := f1.after_registers ready2 a2 (by simp [Component.Covers]) (by simp)
  have byteLoad : (Operand.reg 1 : Operand 64).read u2 =
      (((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e2.writes
    change (Operand.reg 1 : Operand 64).read u2 =
      (memLoad u1.external (stackPtr u1 + 8) 8).setWidth 64 at hw
    have sp : stackPtr u1 = stackPtr u := (a1).read (r := 4) (n := 64) (by simp)
    rw [sp] at hw
    exact hw.trans (congrArg (BitVec.setWidth 64) e1.writes)
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (xor_r64_r64_effect_step 0x113772 0x4d 0xf0 (by simp [RexWPrefix]) rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x13772 _
        (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13775 (by decide)))
  change (xorR64R64Effect 0x113772 8 14 u2).Holds u2 u3 at e3
  have a3 : AgreesExcept [.reg 8, .flags, .rip] u2 u3 := by
    simpa [xorR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := f2.after_registers ready3 a3 (by simp [Component.Covers]) (by simp)
  have xorInput : (Operand.reg 8 : Operand 64).read u3 =
      ((Operand.reg 8 : Operand 64).read u) ^^^ ((Operand.reg 14 : Operand 64).read u) := by
    have hw := e3.writes
    change (Operand.reg 8 : Operand 64).read u3 =
      ((Operand.reg 8 : Operand 64).read u2) ^^^ ((Operand.reg 14 : Operand 64).read u2) at hw
    rw [((a1.trans a2)).read (r := 8) (n := 64) (by simp), ((a1.trans a2)).read (r := 14) (n := 64) (by simp)] at hw
    exact hw
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (neg_r64_effect_step 0x113775 0x48 0xd9 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x13775 _
        (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13778 (by decide)))
  change (negR64Effect 0x113775 1 u3).Holds u3 u4 at e4
  have a4 : AgreesExcept [.reg 1, .flags, .rip] u3 u4 := by
    simpa [negR64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := f3.after_registers ready4 a4 (by simp [Component.Covers]) (by simp)
  have mask : (Operand.reg 1 : Operand 64).read u4 =
      -(((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e4.writes
    change (Operand.reg 1 : Operand 64).read u4 = -((Operand.reg 1 : Operand 64).read u3) at hw
    rw [(a3).read (r := 1) (n := 64) (by simp), byteLoad] at hw
    exact hw
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (and_r64_r64_effect_step 0x113778 0x4c 0xc1 (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x13778 _
        (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1377b (by decide)))
  change (andR64R64Effect 0x113778 1 8 u4).Holds u4 u5 at e5
  have a5 : AgreesExcept [.reg 1, .flags, .rip] u4 u5 := by
    simpa [andR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e5.agrees
  have f5 := f4.after_registers ready5 a5 (by simp [Component.Covers]) (by simp)
  have masked : (Operand.reg 1 : Operand 64).read u5 =
      -(((Operand.reg 7 : Operand 8).read u).setWidth 64) &&&
        (((Operand.reg 8 : Operand 64).read u) ^^^ ((Operand.reg 14 : Operand 64).read u)) := by
    have hw := e5.writes
    change (Operand.reg 1 : Operand 64).read u5 =
      ((Operand.reg 1 : Operand 64).read u4) &&& ((Operand.reg 8 : Operand 64).read u4) at hw
    rw [mask, (a4).read (r := 8) (n := 64) (by simp), xorInput] at hw
    exact hw
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (xor_r64_r64_effect_step 0x11377b 0x4c 0xf1 (by simp [RexWPrefix]) rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x1377b _
        (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1377e (by decide)))
  change (xorR64R64Effect 0x11377b 1 14 u5).Holds u5 u6 at e6
  have a6 : AgreesExcept [.reg 1, .flags, .rip] u5 u6 := by
    simpa [xorR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e6.agrees
  have f6 := f5.after_registers ready6 a6 (by simp [Component.Covers]) (by simp)
  have selected : (Operand.reg 1 : Operand 64).read u6 = selectWord
      ((Operand.reg 8 : Operand 64).read u) ((Operand.reg 14 : Operand 64).read u)
      (((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e6.writes
    change (Operand.reg 1 : Operand 64).read u6 =
      ((Operand.reg 1 : Operand 64).read u5) ^^^ ((Operand.reg 14 : Operand 64).read u5) at hw
    rw [masked, (((((a1.trans a2).trans a3).trans a4).trans a5)).read (r := 14) (n := 64) (by simp)] at hw
    exact hw
  have ag : AgreesExcept [.reg 1, .reg 8, .flags, .rip, .mem (stackPtr u + 8) 1] u u6 := (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).mono (by simp)
  exact ⟨u6, ⟨6, (((((run1.trans run2).trans run3).trans run4).trans run5).trans run6)⟩, f6, e6.rip, selected, ag⟩

set_option maxHeartbeats 800000 in
theorem select_high [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s u 32 112 112)
    (rip : u.RIP = 0x11377e) :
    ∃ w, (∃ fuel, Advances boundary fuel u w) ∧
      ScalarFrame.FrameState s w 32 112 112 ∧ w.RIP = 0x113794 ∧
      (Operand.reg 7 : Operand 64).read w = selectWord
        ((Operand.reg 2 : Operand 64).read u) ((Operand.reg 15 : Operand 64).read u)
        (((Operand.reg 7 : Operand 8).read u).setWidth 64) ∧
      AgreesExcept [.reg 7, .reg 2, .flags, .rip, .mem (stackPtr u + 8) 1] u w := by
  have f0 := frame
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_m8_r8_effect_step 0x11377e 0x40 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x1377e _
        (by decide) (by decide +kernel))
      ⟨rip, byte_writable pre f0, ScalarFrame.stack_code pre.toCalleePre f0 (offset := 8) (len := 1) (codeOffset := 0x1377e) (codeLen := 5) (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13783 (by decide)))
  change (storeEffect 0x11377e 5 (fun t => stackPtr t + 8) (fun t => (Operand.reg 7 : Operand 8).read t) u).Holds u u1 at e1
  have a1 : AgreesExcept [.mem (stackPtr u + 8) 1, .rip] u u1 := by
    simpa [storeEffect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := after_stack pre f0 ready1 (by decide) a1
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (movzx_r32_m8_effect_step 0x113783 7 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x13783 _
        (by decide) (by decide +kernel))
      ⟨e1.rip, ScalarFrame.stack_readable pre.toCalleePre f1 (offset := 8) (len := 1) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13788 (by decide)))
  change (movzxR32M8Effect 0x113783 5 7 (.sib 4 none 0 (.d8 8)) u1).Holds u1 u2 at e2
  have a2 : AgreesExcept [.reg 7, .rip] u1 u2 := by
    simpa [movzxR32M8Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := f1.after_registers ready2 a2 (by simp [Component.Covers]) (by simp)
  have byteLoad : (Operand.reg 7 : Operand 64).read u2 =
      (((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e2.writes
    change (Operand.reg 7 : Operand 64).read u2 =
      (memLoad u1.external (stackPtr u1 + 8) 8).setWidth 64 at hw
    have sp : stackPtr u1 = stackPtr u := (a1).read (r := 4) (n := 64) (by simp)
    rw [sp] at hw
    exact hw.trans (congrArg (BitVec.setWidth 64) e1.writes)
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (xor_r64_r64_effect_step 0x113788 0x4c 0xfa (by simp [RexWPrefix]) rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x13788 _
        (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1378b (by decide)))
  change (xorR64R64Effect 0x113788 2 15 u2).Holds u2 u3 at e3
  have a3 : AgreesExcept [.reg 2, .flags, .rip] u2 u3 := by
    simpa [xorR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := f2.after_registers ready3 a3 (by simp [Component.Covers]) (by simp)
  have xorInput : (Operand.reg 2 : Operand 64).read u3 =
      ((Operand.reg 2 : Operand 64).read u) ^^^ ((Operand.reg 15 : Operand 64).read u) := by
    have hw := e3.writes
    change (Operand.reg 2 : Operand 64).read u3 =
      ((Operand.reg 2 : Operand 64).read u2) ^^^ ((Operand.reg 15 : Operand 64).read u2) at hw
    rw [((a1.trans a2)).read (r := 2) (n := 64) (by simp), ((a1.trans a2)).read (r := 15) (n := 64) (by simp)] at hw
    exact hw
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (neg_r64_effect_step 0x11378b 0x48 0xdf (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x1378b _
        (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1378e (by decide)))
  change (negR64Effect 0x11378b 7 u3).Holds u3 u4 at e4
  have a4 : AgreesExcept [.reg 7, .flags, .rip] u3 u4 := by
    simpa [negR64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := f3.after_registers ready4 a4 (by simp [Component.Covers]) (by simp)
  have mask : (Operand.reg 7 : Operand 64).read u4 =
      -(((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e4.writes
    change (Operand.reg 7 : Operand 64).read u4 = -((Operand.reg 7 : Operand 64).read u3) at hw
    rw [(a3).read (r := 7) (n := 64) (by simp), byteLoad] at hw
    exact hw
  obtain ⟨u5, run5, ready5, e5⟩ :=
    (and_r64_r64_effect_step 0x11378e 0x48 0xd7 (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x1378e _
        (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13791 (by decide)))
  change (andR64R64Effect 0x11378e 7 2 u4).Holds u4 u5 at e5
  have a5 : AgreesExcept [.reg 7, .flags, .rip] u4 u5 := by
    simpa [andR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e5.agrees
  have f5 := f4.after_registers ready5 a5 (by simp [Component.Covers]) (by simp)
  have masked : (Operand.reg 7 : Operand 64).read u5 =
      -(((Operand.reg 7 : Operand 8).read u).setWidth 64) &&&
        (((Operand.reg 2 : Operand 64).read u) ^^^ ((Operand.reg 15 : Operand 64).read u)) := by
    have hw := e5.writes
    change (Operand.reg 7 : Operand 64).read u5 =
      ((Operand.reg 7 : Operand 64).read u4) &&& ((Operand.reg 2 : Operand 64).read u4) at hw
    rw [mask, (a4).read (r := 2) (n := 64) (by simp), xorInput] at hw
    exact hw
  obtain ⟨u6, run6, ready6, e6⟩ :=
    (xor_r64_r64_effect_step 0x113791 0x4c 0xff (by simp [RexWPrefix]) rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x13791 _
        (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13794 (by decide)))
  change (xorR64R64Effect 0x113791 7 15 u5).Holds u5 u6 at e6
  have a6 : AgreesExcept [.reg 7, .flags, .rip] u5 u6 := by
    simpa [xorR64R64Effect, Effect.components, storeEffect, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e6.agrees
  have f6 := f5.after_registers ready6 a6 (by simp [Component.Covers]) (by simp)
  have selected : (Operand.reg 7 : Operand 64).read u6 = selectWord
      ((Operand.reg 2 : Operand 64).read u) ((Operand.reg 15 : Operand 64).read u)
      (((Operand.reg 7 : Operand 8).read u).setWidth 64) := by
    have hw := e6.writes
    change (Operand.reg 7 : Operand 64).read u6 =
      ((Operand.reg 7 : Operand 64).read u5) ^^^ ((Operand.reg 15 : Operand 64).read u5) at hw
    rw [masked, (((((a1.trans a2).trans a3).trans a4).trans a5)).read (r := 15) (n := 64) (by simp)] at hw
    exact hw
  have ag : AgreesExcept [.reg 7, .reg 2, .flags, .rip, .mem (stackPtr u + 8) 1] u u6 := (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).mono (by simp)
  exact ⟨u6, ⟨6, (((((run1.trans run2).trans run3).trans run4).trans run5).trans run6)⟩, f6, e6.rip, selected, ag⟩

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteLogic
open P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Common.Instructions.Neg64
open P256.Proofs.Common.Instructions.CrossPageStore

theorem after_output [Bindings] {s u w : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s u 32 112 112)
    (ready : ReadyToStep w) {offset : Nat} (bound : offset + 8 ≤ 32)
    (agrees : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 offset) 8, .rip] u w) :
    ScalarFrame.FrameState s w 32 112 112 := by
  apply frame.after_effect pre.toCalleePre (by decide) ready agrees ?_ (by simp)
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨registerRegion s .rdi 32, by simp,
      ScalarFrame.output_contains pre.toCalleePre bound ha⟩
  · exact ha.elim

set_option maxHeartbeats 800000 in
theorem stores [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (frame : ScalarFrame.FrameState s u 32 112 112)
    (rip : u.RIP = 0x113794) (pointer : u.regValue .rax = s.regValue .rdi) :
    ∃ w, (∃ fuel, Advances boundary fuel u w) ∧
      ScalarFrame.FrameState s w 32 112 112 ∧ w.RIP = 0x1137a3 ∧
      Nat256At w (s.regValue .rdi)
        (⟨u.regValue .r10, u.regValue .rsi, u.regValue .rcx, u.regValue .rdi⟩ : Limbs).toNat := by
  have f0 := frame
  have ptr1 : (Operand.reg 0 : Operand 64).read u = s.regValue .rdi :=
    (rfl).trans pointer
  obtain ⟨u1, run1, ready1, e1⟩ :=
    (mov_m64_r64_effect_step_any 0x113794 0x4c (by simp [RexWPrefix]) 2
      (.base 0 .none) (by decide) rfl rfl).advances
      (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x13794 _
        (by decide) (by decide +kernel))
      ⟨rip, by
        change Writable u (((Operand.reg 0 : Operand 64).read u) + 0#64) 8
        rw [ptr1]
        exact (ScalarFrame.output_writable pre.toCalleePre (by decide) f0.allocated).add 0 (by decide), by
        change RangeApart (((Operand.reg 0 : Operand 64).read u) + 0#64) 8 0x113794 3
        rw [ptr1]
        exact RangeApart.add_left (ScalarFrame.output_code pre.toCalleePre
          (offset := 0x13794) (len := 3) (by decide)) 0 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13797 (by decide)))
  change (movM64R64Effect 0x113794 10 (.base 0 .none) u).Holds u u1 at e1
  have a1 : AgreesExcept [.mem (s.regValue .rdi + 0#64) 8, .rip] u u1 := by
    have ag : AgreesExcept [.mem (((Operand.reg 0 : Operand 64).read u) + 0#64) 8, .rip] u u1 := by
      simpa [movM64R64Effect, storeEffect, Effect.components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value] using e1.agrees
    rw [ptr1] at ag
    exact ag
  have f1 := after_output pre f0 ready1 (offset := 0) (by decide) a1
  have wr1 : memLoad u1.external (s.regValue .rdi + 0#64) 64 =
      (Operand.reg 10 : Operand 64).read u := by
    have hw := e1.writes
    change memLoad u1.external (((Operand.reg 0 : Operand 64).read u) + 0#64) 64 =
      (Operand.reg 10 : Operand 64).read u at hw
    rw [ptr1] at hw
    exact hw.trans (rfl)
  have ptr2 : (Operand.reg 0 : Operand 64).read u1 = s.regValue .rdi :=
    ((a1).read (r := 0) (n := 64) (by simp)).trans pointer
  obtain ⟨u2, run2, ready2, e2⟩ :=
    (mov_m64_r64_effect_step_any 0x113797 0x48 (by simp [RexWPrefix]) 6
      (.base 0 (.d8 8)) (by decide) rfl rfl).advances
      (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x13797 _
        (by decide) (by decide +kernel))
      ⟨e1.rip, by
        change Writable u1 (((Operand.reg 0 : Operand 64).read u1) + 8#64) 8
        rw [ptr2]
        exact (ScalarFrame.output_writable pre.toCalleePre (by decide) f1.allocated).add 8 (by decide), by
        change RangeApart (((Operand.reg 0 : Operand 64).read u1) + 8#64) 8 0x113797 4
        rw [ptr2]
        exact RangeApart.add_left (ScalarFrame.output_code pre.toCalleePre
          (offset := 0x13797) (len := 4) (by decide)) 8 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1379b (by decide)))
  change (movM64R64Effect 0x113797 6 (.base 0 (.d8 8)) u1).Holds u1 u2 at e2
  have a2 : AgreesExcept [.mem (s.regValue .rdi + 8#64) 8, .rip] u1 u2 := by
    have ag : AgreesExcept [.mem (((Operand.reg 0 : Operand 64).read u1) + 8#64) 8, .rip] u1 u2 := by
      simpa [movM64R64Effect, storeEffect, Effect.components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value] using e2.agrees
    rw [ptr2] at ag
    exact ag
  have f2 := after_output pre f1 ready2 (offset := 8) (by decide) a2
  have wr2 : memLoad u2.external (s.regValue .rdi + 8#64) 64 =
      (Operand.reg 6 : Operand 64).read u := by
    have hw := e2.writes
    change memLoad u2.external (((Operand.reg 0 : Operand 64).read u1) + 8#64) 64 =
      (Operand.reg 6 : Operand 64).read u1 at hw
    rw [ptr2] at hw
    exact hw.trans ((a1).read (r := 6) (n := 64) (by simp))
  have ptr3 : (Operand.reg 0 : Operand 64).read u2 = s.regValue .rdi :=
    (((a1.trans a2)).read (r := 0) (n := 64) (by simp)).trans pointer
  obtain ⟨u3, run3, ready3, e3⟩ :=
    (mov_m64_r64_effect_step_any 0x11379b 0x48 (by simp [RexWPrefix]) 1
      (.base 0 (.d8 16)) (by decide) rfl rfl).advances
      (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x1379b _
        (by decide) (by decide +kernel))
      ⟨e2.rip, by
        change Writable u2 (((Operand.reg 0 : Operand 64).read u2) + 16#64) 8
        rw [ptr3]
        exact (ScalarFrame.output_writable pre.toCalleePre (by decide) f2.allocated).add 16 (by decide), by
        change RangeApart (((Operand.reg 0 : Operand 64).read u2) + 16#64) 8 0x11379b 4
        rw [ptr3]
        exact RangeApart.add_left (ScalarFrame.output_code pre.toCalleePre
          (offset := 0x1379b) (len := 4) (by decide)) 16 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1379f (by decide)))
  change (movM64R64Effect 0x11379b 1 (.base 0 (.d8 16)) u2).Holds u2 u3 at e3
  have a3 : AgreesExcept [.mem (s.regValue .rdi + 16#64) 8, .rip] u2 u3 := by
    have ag : AgreesExcept [.mem (((Operand.reg 0 : Operand 64).read u2) + 16#64) 8, .rip] u2 u3 := by
      simpa [movM64R64Effect, storeEffect, Effect.components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value] using e3.agrees
    rw [ptr3] at ag
    exact ag
  have f3 := after_output pre f2 ready3 (offset := 16) (by decide) a3
  have wr3 : memLoad u3.external (s.regValue .rdi + 16#64) 64 =
      (Operand.reg 1 : Operand 64).read u := by
    have hw := e3.writes
    change memLoad u3.external (((Operand.reg 0 : Operand 64).read u2) + 16#64) 64 =
      (Operand.reg 1 : Operand 64).read u2 at hw
    rw [ptr3] at hw
    exact hw.trans (((a1.trans a2)).read (r := 1) (n := 64) (by simp))
  have ptr4 : (Operand.reg 0 : Operand 64).read u3 = s.regValue .rdi :=
    ((((a1.trans a2).trans a3)).read (r := 0) (n := 64) (by simp)).trans pointer
  obtain ⟨u4, run4, ready4, e4⟩ :=
    (mov_m64_r64_effect_step_any 0x11379f 0x48 (by simp [RexWPrefix]) 7
      (.base 0 (.d8 24)) (by decide) rfl rfl).advances
      (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x1379f _
        (by decide) (by decide +kernel))
      ⟨e3.rip, by
        change Writable u3 (((Operand.reg 0 : Operand 64).read u3) + 24#64) 8
        rw [ptr4]
        exact (ScalarFrame.output_writable pre.toCalleePre (by decide) f3.allocated).add 24 (by decide), by
        change RangeApart (((Operand.reg 0 : Operand 64).read u3) + 24#64) 8 0x11379f 4
        rw [ptr4]
        exact RangeApart.add_left (ScalarFrame.output_code pre.toCalleePre
          (offset := 0x1379f) (len := 4) (by decide)) 24 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137a3 (by decide)))
  change (movM64R64Effect 0x11379f 7 (.base 0 (.d8 24)) u3).Holds u3 u4 at e4
  have a4 : AgreesExcept [.mem (s.regValue .rdi + 24#64) 8, .rip] u3 u4 := by
    have ag : AgreesExcept [.mem (((Operand.reg 0 : Operand 64).read u3) + 24#64) 8, .rip] u3 u4 := by
      simpa [movM64R64Effect, storeEffect, Effect.components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value] using e4.agrees
    rw [ptr4] at ag
    exact ag
  have f4 := after_output pre f3 ready4 (offset := 24) (by decide) a4
  have wr4 : memLoad u4.external (s.regValue .rdi + 24#64) 64 =
      (Operand.reg 7 : Operand 64).read u := by
    have hw := e4.writes
    change memLoad u4.external (((Operand.reg 0 : Operand 64).read u3) + 24#64) 64 =
      (Operand.reg 7 : Operand 64).read u3 at hw
    rw [ptr4] at hw
    exact hw.trans ((((a1.trans a2).trans a3)).read (r := 7) (n := 64) (by simp))
  have keep1 : memLoad u4.external (s.regValue .rdi + 0#64) 64 =
      memLoad u1.external (s.regValue .rdi + 0#64) 64 := by
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ((a2.trans a3).trans a4)
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    all_goals rintro ⟨k, hk, he⟩
    all_goals exact OffsetsApart.ne (base := s.regValue .rdi) (hi := hj) (hj := hk) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have keep2 : memLoad u4.external (s.regValue .rdi + 8#64) 64 =
      memLoad u2.external (s.regValue .rdi + 8#64) 64 := by
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees (a3.trans a4)
    intro j hj c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact id
    all_goals rintro ⟨k, hk, he⟩
    all_goals exact OffsetsApart.ne (base := s.regValue .rdi) (hi := hj) (hj := hk) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have keep3 : memLoad u4.external (s.regValue .rdi + 16#64) 64 =
      memLoad u3.external (s.regValue .rdi + 16#64) 64 := by
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees a4
    intro j hj c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals try exact id
    all_goals rintro ⟨k, hk, he⟩
    all_goals exact OffsetsApart.ne (base := s.regValue .rdi) (hi := hj) (hj := hk) (hl := by decide) (by unfold OffsetsApart; decide +kernel) he
  have output := P256.Proofs.Field.nat256At_readLimbs
    (s := u4) (address := s.regValue .rdi) (fun i hi => f4.allocated _
      (Option.isSome_iff_exists.mpr (pre.outputAllocated _ (memoryRegion_contains_add pre.outputBounded
        (Nat.le_refl _) (Nat.le_refl _) hi))))
  have eqLimbs : P256.Proofs.Field.readLimbs u4 (s.regValue .rdi) =
      (⟨u.regValue .r10, u.regValue .rsi, u.regValue .rcx, u.regValue .rdi⟩ : Limbs) := by
    have h1 := keep1.trans wr1
    have h2 := keep2.trans wr2
    have h3 := keep3.trans wr3
    simp only [BitVec.add_zero] at h1
    unfold P256.Proofs.Field.readLimbs
    congr 1
  rw [eqLimbs] at output
  exact ⟨u4, ⟨4, ((run1.trans run2).trans run3).trans run4⟩, f4, e4.rip, output⟩

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select


set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxHeartbeats 800000 in
theorem select_correct [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (state : Difference s t u)
    (borrowBound : (subRaw (inputLimbs t) modulus).2.toNat ≤ 1) :
    ∃ w, (∃ fuel, Advances boundary fuel u w) ∧
      ScalarFrame.FrameState s w 32 112 112 ∧ w.RIP = 0x1137a3 ∧
      Nat256At w (s.regValue .rdi) (reduce (inputLimbs t) (t.regValue .r12)).toNat := by
  obtain ⟨p, ⟨np, rp⟩, fp, ip, pointer, byte, ap⟩ :=
    Select.prefix_correct pre state.frame state.rip
  obtain ⟨v, ⟨nv, rv⟩, fv, iv, top, av⟩ := Select.scratch pre fp ip
  have before := ap.trans av
  have q : ((Operand.reg 7 : Operand 8).read v).setWidth 64 =
      selector (t.regValue .r12) (subRaw (inputLimbs t) modulus).2 := by
    rw [av.read (r := 7) (n := 8) (by simp), byte, state.high, state.rbp]
    exact selector_byte _ _ (eq_zero_or_one borrowBound)
  have topValue : (Operand.reg 2 : Operand 64).read v = (inputLimbs t).l3 := by
    have pm := ap.external (by simp [Component.Covers])
    have pd : p.regValue .rdx = u.regValue .rdx := ap.read (r := 2) (n := 64) (by simp)
    have sm : slot s p 24 = slot s u 24 := by simp only [slot, pm]
    rw [pd, sm] at top
    exact top.trans (top_add_eq _ _ _ _ _ state.top)
  have a0 : (Operand.reg 3 : Operand 64).read v = (inputLimbs t).l0 :=
    (before.read (by simp)).trans state.low
  have a1 : (Operand.reg 1 : Operand 64).read v = (inputLimbs t).l1 :=
    (before.read (by simp)).trans state.middleLow
  have a2 : (Operand.reg 8 : Operand 64).read v = (inputLimbs t).l2 :=
    (before.read (by simp)).trans state.middleHigh
  have d0 : (Operand.reg 6 : Operand 64).read v = (subRaw (inputLimbs t) modulus).1.l0 :=
    (before.read (by simp)).trans state.rsi
  have d1 : (Operand.reg 9 : Operand 64).read v = (subRaw (inputLimbs t) modulus).1.l1 :=
    (before.read (by simp)).trans state.r9
  have d2 : (Operand.reg 14 : Operand 64).read v = (subRaw (inputLimbs t) modulus).1.l2 :=
    (before.read (by simp)).trans state.r14
  have d3 : (Operand.reg 15 : Operand 64).read v = (subRaw (inputLimbs t) modulus).1.l3 :=
    (before.read (by simp)).trans state.r15
  obtain ⟨v1, ⟨n1, r1⟩, f1, i1, w1, ag1⟩ := Select.select_low pre fv iv
  obtain ⟨v2, ⟨n2, r2⟩, f2, i2, w2, ag2⟩ := Select.select_middleLow pre f1 i1
  obtain ⟨v3, ⟨n3, r3⟩, f3, i3, w3, ag3⟩ := Select.select_middleHigh pre f2 i2
  obtain ⟨v4, ⟨n4, r4⟩, f4, i4, w4, ag4⟩ := Select.select_high pre f3 i3
  have ptr4 : v4.regValue .rax = s.regValue .rdi := by
    exact (((((av.trans ag1).trans ag2).trans ag3).trans ag4).read
      (r := 0) (n := 64) (by simp)).trans (pointer.trans state.rdi)
  have result1 : (Operand.reg 10 : Operand 64).read v4 =
      (reduce (inputLimbs t) (t.regValue .r12)).l0 := by
    rw [(((ag2.trans ag3).trans ag4)).read (r := 10) (n := 64) (by simp), w1]
    rw [a0, d0, q]
    rfl
  have result2 : (Operand.reg 6 : Operand 64).read v4 =
      (reduce (inputLimbs t) (t.regValue .r12)).l1 := by
    rw [((ag3.trans ag4)).read (r := 6) (n := 64) (by simp), w2]
    rw [(ag1).read (r := 1) (n := 64) (by simp)]
    rw [(ag1).read (r := 9) (n := 64) (by simp)]
    rw [(ag1).read (r := 7) (n := 8) (by simp)]
    rw [a1, d1, q]
    rfl
  have result3 : (Operand.reg 1 : Operand 64).read v4 =
      (reduce (inputLimbs t) (t.regValue .r12)).l2 := by
    rw [(ag4).read (r := 1) (n := 64) (by simp), w3]
    rw [((ag1.trans ag2)).read (r := 8) (n := 64) (by simp)]
    rw [((ag1.trans ag2)).read (r := 14) (n := 64) (by simp)]
    rw [((ag1.trans ag2)).read (r := 7) (n := 8) (by simp)]
    rw [a2, d2, q]
    rfl
  have result4 : (Operand.reg 7 : Operand 64).read v4 =
      (reduce (inputLimbs t) (t.regValue .r12)).l3 := by
    rw [w4]
    rw [(((ag1.trans ag2).trans ag3)).read (r := 2) (n := 64) (by simp)]
    rw [(((ag1.trans ag2).trans ag3)).read (r := 15) (n := 64) (by simp)]
    rw [(((ag1.trans ag2).trans ag3)).read (r := 7) (n := 8) (by simp)]
    rw [topValue, d3, q]
    rfl
  obtain ⟨w, ⟨nw, rw'⟩, fw, iw, output⟩ := Select.stores pre f4 i4 ptr4
  have limbs : (⟨v4.regValue .r10, v4.regValue .rsi, v4.regValue .rcx,
      v4.regValue .rdi⟩ : Limbs) = reduce (inputLimbs t) (t.regValue .r12) := by
    change (⟨(Operand.reg 10 : Operand 64).read v4,
      (Operand.reg 6 : Operand 64).read v4, (Operand.reg 1 : Operand 64).read v4,
      (Operand.reg 7 : Operand 64).read v4⟩ : Limbs) = _
    rw [result1, result2, result3, result4]
  rw [limbs] at output
  exact ⟨w, ⟨np + nv + n1 + n2 + n3 + n4 + nw,
    (((((rp.trans rv).trans r1).trans r2).trans r3).trans r4).trans rw'⟩, fw, iw, output⟩

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction