import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Choice.Run
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Program (CalleePre inProgram_of_textOffset)
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step sar_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.Carry (adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.AddByte (add_rsp_disp8_imm8_effect_step)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Choice

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem tail [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t)
    (rip : t.RIP = 0x113a4e) :
    ∃ u, Advances boundary 11 t u ∧ FrameState s u ∧ u.RIP = 0x113a75 ∧
      ∀ r : BitVec 5, r ≠ 7 → (Operand.reg r : Operand 64).read u =
        (Operand.reg r : Operand 64).read t := by
  obtain ⟨t1,a1,f1,e1⟩ := step (offset := 0x13a4e) pre state
    (mov_m8_r8_legacy_effect_step 0x113a4e 1 (by decide) (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
    (by decide +kernel) (by decide +kernel) (by
      refine ⟨rip,?_,?_⟩
      · change MemWritable t (stackPtr t+0#64) 1
        exact writable_byte pre state (by decide)
      · change RangeApart (stackPtr t+0#64) 1
          (Extracted.textAddress+BitVec.ofNat 64 0x13a4e) 3
        exact stack_code pre state (by decide) (by decide))
    (inProgram_of_textOffset 0x13a51 (by decide))
    (by simp [storeEffect, storeAddrAt,Effect.components, frame, AddrMode.addr, AddrMode.reg64, Disp.value,
      Operand.read_reg64, stackPtr, gprIndex])
  have p1 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t1 = (Operand.reg r : Operand 64).read t :=
    e1.agrees.read (by simp [storeEffect,Effect.components])
  obtain ⟨t2,a2,f2,e2⟩ := step (E := movR64R64Effect 0x113a51 7 4) (offset := 0x13a51) pre f1
    (mov_r64_r64_effect_step 0x113a51 0x48 0xe7 (by simp [RexWPrefix]) rfl)
    (by decide +kernel) (by decide +kernel) e1.rip
    (inProgram_of_textOffset 0x13a54 (by decide))
    (by simp [movR64R64Effect,Effect.components, frame,
      Operand.read_reg64, stackPtr, gprIndex])
  have p2 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t2 = (Operand.reg r : Operand 64).read t1 :=
    e2.agrees.read (by simpa [movR64R64Effect,Effect.components] using hr)
  obtain ⟨t3,a3,f3,e3⟩ := step (E := movzxR32M8Effect 0x113a54 4 7 (.sib 4 none 0 .none)) (offset := 0x13a54) pre f2
    (movzx_r32_m8_effect_step 0x113a54 7 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
    (by decide +kernel) (by decide +kernel) (by
      refine ⟨e2.rip,?_⟩
      change MemReadable t2 (stackPtr t2+0#64) 1
      exact stack_readable pre f2 (by decide))
    (inProgram_of_textOffset 0x13a58 (by decide))
    (by simp [movzxR32M8Effect,Effect.components, frame, AddrMode.addr, AddrMode.reg64, Disp.value,
      Operand.read_reg64, stackPtr, gprIndex])
  have p3 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t3 = (Operand.reg r : Operand 64).read t2 :=
    e3.agrees.read (by simpa [movzxR32M8Effect,Effect.components] using hr)
  obtain ⟨t4,a4,f4,e4⟩ := step (E := decR64Effect 0x113a58 7) (offset := 0x13a58) pre f3
    (dec_r64_effect_step 0x113a58 0x48 0xcf (by simp [RexWPrefix]) rfl rfl)
    (by decide +kernel) (by decide +kernel) e3.rip
    (inProgram_of_textOffset 0x13a5b (by decide))
    (by simp [decR64Effect,Effect.components, frame,
      Operand.read_reg64, stackPtr, gprIndex])
  have p4 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t4 = (Operand.reg r : Operand 64).read t3 :=
    e4.agrees.read (by simpa [decR64Effect,Effect.components] using hr)
  obtain ⟨t5,a5,f5,e5⟩ := step (E := andR64R64Effect 0x113a5b 7 13) (offset := 0x13a5b) pre f4
    (and_r64_r64_effect_step 0x113a5b 0x4c 0xef (by simp [RexWPrefix]) rfl)
    (by decide +kernel) (by decide +kernel) e4.rip
    (inProgram_of_textOffset 0x13a5e (by decide))
    (by simp [andR64R64Effect,Effect.components, frame,
      Operand.read_reg64, stackPtr, gprIndex])
  have p5 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t5 = (Operand.reg r : Operand 64).read t4 :=
    e5.agrees.read (by simpa [andR64R64Effect,Effect.components] using hr)
  obtain ⟨t6,a6,f6,e6⟩ := step (E := P256.Proofs.Common.Instructions.sarR64Effect 0x113a5e 4 7 63) (offset := 0x13a5e) pre f5
    (sar_r64_imm8_effect_step 0x113a5e 0x48 0xff 63 (by simp [RexWPrefix]) rfl rfl)
    (by decide +kernel) (by decide +kernel) e5.rip
    (inProgram_of_textOffset 0x13a62 (by decide))
    (by simp [P256.Proofs.Common.Instructions.sarR64Effect,Effect.components, frame,
      Operand.read_reg64, stackPtr, gprIndex])
  have p6 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t6 = (Operand.reg r : Operand 64).read t5 :=
    e6.agrees.read (by simpa [P256.Proofs.Common.Instructions.sarR64Effect,Effect.components] using hr)
  obtain ⟨t7,a7,f7,e7⟩ := step (E := P256.Proofs.Common.Instructions.AddByte.addM8Imm8Effect 0x113a62 5 (.sib 4 none 0 (.d8 15)) 0xff) (offset := 0x13a62) pre f6
    (add_rsp_disp8_imm8_effect_step 0x113a62 15 0xff)
    (by decide +kernel) (by decide +kernel) (by
      refine ⟨e6.rip,?_,?_⟩
      · change MemWritable t6 (stackPtr t6+15#64) 1
        exact writable_byte pre f6 (by decide)
      · change RangeApart (stackPtr t6+15#64) 1
          (Extracted.textAddress+BitVec.ofNat 64 0x13a62) 5
        exact stack_code pre f6 (by decide) (by decide))
    (inProgram_of_textOffset 0x13a67 (by decide))
    (by simp [P256.Proofs.Common.Instructions.AddByte.addM8Imm8Effect,Effect.components, frame, AddrMode.addr, AddrMode.reg64, Disp.value,
      Operand.read_reg64, stackPtr, gprIndex])
  have p7 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t7 = (Operand.reg r : Operand 64).read t6 :=
    e7.agrees.read (by simp [P256.Proofs.Common.Instructions.AddByte.addM8Imm8Effect,Effect.components])
  obtain ⟨t8,a8,f8,e8⟩ := step (E := P256.Proofs.Common.Instructions.Carry.adcR64R64Effect 0x113a67 7 3) (offset := 0x13a67) pre f7
    (adc_r64_r64_effect_step 0x113a67 0x48 0xdf (by simp [RexWPrefix]) rfl)
    (by decide +kernel) (by decide +kernel) e7.rip
    (inProgram_of_textOffset 0x13a6a (by decide))
    (by simp [P256.Proofs.Common.Instructions.Carry.adcR64R64Effect,Effect.components, frame,
      Operand.read_reg64, stackPtr, gprIndex])
  have p8 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t8 = (Operand.reg r : Operand 64).read t7 :=
    e8.agrees.read (by simpa [P256.Proofs.Common.Instructions.Carry.adcR64R64Effect,Effect.components] using hr)
  obtain ⟨t9,a9,f9,e9⟩ := step (E := shrR64Effect 0x113a6a 4 7 63) (offset := 0x13a6a) pre f8
    (shr_r64_imm8_effect_step 0x113a6a 0x48 0xef 63 (by simp [RexWPrefix]) rfl rfl)
    (by decide +kernel) (by decide +kernel) e8.rip
    (inProgram_of_textOffset 0x13a6e (by decide))
    (by simp [shrR64Effect,Effect.components, frame,
      Operand.read_reg64, stackPtr, gprIndex])
  have p9 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t9 = (Operand.reg r : Operand 64).read t8 :=
    e9.agrees.read (by simpa [shrR64Effect,Effect.components] using hr)
  obtain ⟨t10,a10,f10,e10⟩ := step (E := movM64R64Effect 0x113a6e 7 (.sib 4 none 0 .none)) (offset := 0x13a6e) pre f9
    (mov_m64_r64_effect_step 0x113a6e 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
    (by decide +kernel) (by decide +kernel) (by
      refine ⟨e9.rip,?_,?_⟩
      · change MemWritable t9 (stackPtr t9+0#64) 8
        simpa only [BitVec.add_zero] using writable_word pre f9
      · change RangeApart (stackPtr t9+0#64) 8
          (Extracted.textAddress+BitVec.ofNat 64 0x13a6e) 4
        exact stack_code pre f9 (by decide) (by decide))
    (inProgram_of_textOffset 0x13a72 (by decide))
    (by simp [movM64R64Effect, storeEffect, storeAddrAt,Effect.components, frame, AddrMode.addr, AddrMode.reg64, Disp.value,
      Operand.read_reg64, stackPtr, gprIndex])
  have p10 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t10 = (Operand.reg r : Operand 64).read t9 :=
    e10.agrees.read (by simp [movM64R64Effect, storeEffect,Effect.components])
  obtain ⟨t11,a11,f11,e11⟩ := step (E := movR64R64Effect 0x113a72 7 4) (offset := 0x13a72) pre f10
    (mov_r64_r64_effect_step 0x113a72 0x48 0xe7 (by simp [RexWPrefix]) rfl)
    (by decide +kernel) (by decide +kernel) e10.rip
    (inProgram_of_textOffset 0x13a75 (by decide))
    (by simp [movR64R64Effect,Effect.components, frame,
      Operand.read_reg64, stackPtr, gprIndex])
  have p11 (r : BitVec 5) (hr : r ≠ 7) :
      (Operand.reg r : Operand 64).read t11 = (Operand.reg r : Operand 64).read t10 :=
    e11.agrees.read (by simpa [movR64R64Effect,Effect.components] using hr)
  refine ⟨t11,?_,f11,e11.rip,?_⟩
  · exact ((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11)
  · intro r hr
    exact (p11 r hr).trans ((p10 r hr).trans ((p9 r hr).trans ((p8 r hr).trans ((p7 r hr).trans ((p6 r hr).trans ((p5 r hr).trans ((p4 r hr).trans ((p3 r hr).trans ((p2 r hr).trans (p1 r hr))))))))))

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Choice
