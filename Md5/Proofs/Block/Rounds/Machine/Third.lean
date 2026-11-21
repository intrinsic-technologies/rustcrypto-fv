import Md5.Proofs.Block.Rounds.Step
import Md5.Proofs.Block.Rounds.Address
import Md5.Proofs.Block.Rounds.Interface
import Md5.Proofs.Block.Rounds.Register
import Md5.Proofs.Block.Rounds.Load
import Md5.Proofs.Block.Rounds.Store

namespace Md5.Proofs.Block.Rounds
open X86 X86.Machine X86.UserProcess X86Proofs

theorem segment33_runs [Bindings] :
    RunWords 0x1020a2 0x1020ba segment33 := by
  have h1 : RunWords 0x1020a2 0x1020a5 [.mov (.reg 15) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x1020a2 0x1020a5 (movR32R32Effect 0x1020a2 3 15 5) := {
      pre := (fun s ↦ s.RIP = 0x1020a2)
      code := codeRange 0x1020a2 [0x41, 0x89, 0xef]
      step := mov_r32_r32_rex_effect_step 0x1020a2 0x41 0xef (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20a2 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 5))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1020a5 0x1020a8 [.xor (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1020a5 0x1020a8 (xorR32R32Effect 0x1020a5 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x1020a5)
      code := codeRange 0x1020a5 [0x41, 0x31, 0xcf]
      step := xor_r32_r32_rex_effect_step 0x1020a5 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20a5 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1020a8 0x1020ab [.mov (.reg 0) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x1020a8 0x1020ab (movR32R32Effect 0x1020a8 3 0 15) := {
      pre := (fun s ↦ s.RIP = 0x1020a8)
      code := codeRange 0x1020a8 [0x44, 0x89, 0xf8]
      step := mov_r32_r32_rex_effect_step 0x1020a8 0x44 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20a8 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 0) (.location (.reg 15))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1020ab 0x1020ad [.xor (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1020ab 0x1020ad (xorR32R32Effect 0x1020ab 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x1020ab)
      code := codeRange 0x1020ab [0x31, 0xd0]
      step := xor_r32_r32_effect_step 0x1020ab 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x20ab 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 0) (.location (.reg 2))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1020ad 0x1020b0 [.add (.reg 0) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x1020ad 0x1020b0 (addR32R32Effect 0x1020ad 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x1020ad)
      code := codeRange 0x1020ad [0x44, 0x1, 0xe0]
      step := add_r32_r32_rex_effect_step 0x1020ad 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20ad 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 12))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x1020b0 0x1020b5 [.add (.reg 0) (.immediate 0xfffa3942)] := by
    let ex : InstructionExecution 0x1020b0 0x1020b5 (addR32Imm32Effect 0x1020b0 5 0 0xfffa3942) := {
      pre := (fun s ↦ s.RIP = 0x1020b0)
      code := codeRange 0x1020b0 [0x5, 0x42, 0x39, 0xfa, 0xff]
      step := Register.add_eax_imm32_effect_step 0x1020b0 0xfffa3942
      present := fun hc ↦ program_text_slice hc 0x20b0 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0xfffa3942)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1020b5 0x1020b8 [.rol (.reg 0) 4] := by
    let ex : InstructionExecution 0x1020b5 0x1020b8 (rolR32Effect 0x1020b5 3 0 4) := {
      pre := (fun s ↦ s.RIP = 0x1020b5)
      code := codeRange 0x1020b5 [0xc1, 0xc0, 0x4]
      step := rol_r32_imm8_effect_step 0x1020b5 0xc0 0x4 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20b5 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 4) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1020b8 0x1020ba [.add (.reg 0) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x1020b8 0x1020ba (addR32R32Effect 0x1020b8 2 0 5) := {
      pre := (fun s ↦ s.RIP = 0x1020b8)
      code := codeRange 0x1020b8 [0x1, 0xe8]
      step := add_r32_r32_effect_step 0x1020b8 0xe8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x20b8 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 5))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment33, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8)))))))

theorem segment34_runs [Bindings] :
    RunWords 0x1020ba 0x1020ce segment34 := by
  have h1 : RunWords 0x1020ba 0x1020bd [.add (.reg 2) (.location (.reg 14))] := by
    let ex : InstructionExecution 0x1020ba 0x1020bd (addR32R32Effect 0x1020ba 3 2 14) := {
      pre := (fun s ↦ s.RIP = 0x1020ba)
      code := codeRange 0x1020ba [0x44, 0x1, 0xf2]
      step := add_r32_r32_rex_effect_step 0x1020ba 0x44 0xf2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20ba 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 14))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1020bd 0x1020c0 [.xor (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1020bd 0x1020c0 (xorR32R32Effect 0x1020bd 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x1020bd)
      code := codeRange 0x1020bd [0x41, 0x31, 0xc7]
      step := xor_r32_r32_rex_effect_step 0x1020bd 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20bd 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1020c0 0x1020c3 [.add (.reg 2) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x1020c0 0x1020c3 (addR32R32Effect 0x1020c0 3 2 15) := {
      pre := (fun s ↦ s.RIP = 0x1020c0)
      code := codeRange 0x1020c0 [0x44, 0x1, 0xfa]
      step := add_r32_r32_rex_effect_step 0x1020c0 0x44 0xfa (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20c0 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 15))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1020c3 0x1020c9 [.add (.reg 2) (.immediate 0x8771f681)] := by
    let ex : InstructionExecution 0x1020c3 0x1020c9 (addR32Imm32Effect 0x1020c3 6 2 0x8771f681) := {
      pre := (fun s ↦ s.RIP = 0x1020c3)
      code := codeRange 0x1020c3 [0x81, 0xc2, 0x81, 0xf6, 0x71, 0x87]
      step := add_r32_imm32_effect_step 0x1020c3 0xc2 0x8771f681 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20c3 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0x8771f681)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1020c9 0x1020cc [.rol (.reg 2) 11] := by
    let ex : InstructionExecution 0x1020c9 0x1020cc (rolR32Effect 0x1020c9 3 2 11) := {
      pre := (fun s ↦ s.RIP = 0x1020c9)
      code := codeRange 0x1020c9 [0xc1, 0xc2, 0xb]
      step := rol_r32_imm8_effect_step 0x1020c9 0xc2 0xb (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20c9 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 11) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x1020cc 0x1020ce [.add (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1020cc 0x1020ce (addR32R32Effect 0x1020cc 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x1020cc)
      code := codeRange 0x1020cc [0x1, 0xc2]
      step := add_r32_r32_effect_step 0x1020cc 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x20cc 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 0))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment34, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6)))))

theorem segment35_runs [Bindings] :
    RunWords 0x1020ce 0x1020ef segment35 := by
  have h1 : RunWords 0x1020ce 0x1020d1 [.mov (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1020ce 0x1020d1 (movR32R32Effect 0x1020ce 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x1020ce)
      code := codeRange 0x1020ce [0x41, 0x89, 0xd7]
      step := mov_r32_r32_rex_effect_step 0x1020ce 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20ce 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1020d1 0x1020d4 [.xor (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1020d1 0x1020d4 (xorR32R32Effect 0x1020d1 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x1020d1)
      code := codeRange 0x1020d1 [0x41, 0x31, 0xc7]
      step := xor_r32_r32_rex_effect_step 0x1020d1 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20d1 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1020d4 0x1020d7 [.mov (.reg 12) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x1020d4 0x1020d7 (movR32R32Effect 0x1020d4 3 12 15) := {
      pre := (fun s ↦ s.RIP = 0x1020d4)
      code := codeRange 0x1020d4 [0x45, 0x89, 0xfc]
      step := mov_r32_r32_rex_effect_step 0x1020d4 0x45 0xfc (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20d4 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 12) (.location (.reg 15))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1020d7 0x1020da [.xor (.reg 12) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x1020d7 0x1020da (xorR32R32Effect 0x1020d7 3 12 5) := {
      pre := (fun s ↦ s.RIP = 0x1020d7)
      code := codeRange 0x1020d7 [0x41, 0x31, 0xec]
      step := xor_r32_r32_rex_effect_step 0x1020d7 0x41 0xec (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20d7 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 12) (.location (.reg 5))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1020da 0x1020de [.add (.reg 1) (.location (.stack 32))] := by
    let ex : InstructionExecution 0x1020da 0x1020de (addR32M32Effect 0x1020da 4 1 (.sib 4 none 0
      (.d8 0x20))) := {
      pre := (LoadPre 0x1020da (fun s ↦ ((.sib 4 none 0 (.d8 0x20)) : AddrMode).addr s (0x1020da +
        4)) 4)
      code := codeRange 0x1020da [0x3, 0x4c, 0x24, 0x20]
      step := add_r32_m32_noRex_effect_step 0x1020da 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20da 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 32 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.stack 32))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x1020de 0x1020e1 [.add (.reg 12) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1020de 0x1020e1 (addR32R32Effect 0x1020de 3 12 1) := {
      pre := (fun s ↦ s.RIP = 0x1020de)
      code := codeRange 0x1020de [0x41, 0x1, 0xcc]
      step := add_r32_r32_rex_effect_step 0x1020de 0x41 0xcc (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20de 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 1))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1020e1 0x1020e8 [.add (.reg 12) (.immediate 0x6d9d6122)] := by
    let ex : InstructionExecution 0x1020e1 0x1020e8 (addR32Imm32Effect 0x1020e1 7 12 0x6d9d6122) :=
      {
      pre := (fun s ↦ s.RIP = 0x1020e1)
      code := codeRange 0x1020e1 [0x41, 0x81, 0xc4, 0x22, 0x61, 0x9d, 0x6d]
      step := add_r32_imm32_rex_effect_step 0x1020e1 0x41 0xc4 0x6d9d6122 (by simp [RexNoWPrefix])
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20e1 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.immediate 0x6d9d6122)) (dst := 12) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1020e8 0x1020ec [.rol (.reg 12) 16] := by
    let ex : InstructionExecution 0x1020e8 0x1020ec (rolR32Effect 0x1020e8 4 12 16) := {
      pre := (fun s ↦ s.RIP = 0x1020e8)
      code := codeRange 0x1020e8 [0x41, 0xc1, 0xc4, 0x10]
      step := rol_r32_imm8_rex_effect_step 0x1020e8 0x41 0xc4 0x10 (by simp [RexNoWPrefix]) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20e8 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 12) 16) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x1020ec 0x1020ef [.add (.reg 12) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1020ec 0x1020ef (addR32R32Effect 0x1020ec 3 12 2) := {
      pre := (fun s ↦ s.RIP = 0x1020ec)
      code := codeRange 0x1020ec [0x41, 0x1, 0xd4]
      step := add_r32_r32_rex_effect_step 0x1020ec 0x41 0xd4 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20ec 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 2))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment35, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

theorem segment36_runs [Bindings] :
    RunWords 0x1020ef 0x102107 segment36 := by
  have h1 : RunWords 0x1020ef 0x1020f3 [.mov (.reg 3) (.location (.stack 36))] := by
    let ex : InstructionExecution 0x1020ef 0x1020f3 (movR32M32NoRexEffect 0x1020ef 3 (.sib 4 none 0
      (.d8 0x24))) := {
      pre := (LoadPre 0x1020ef (fun s ↦ ((.sib 4 none 0 (.d8 0x24)) : AddrMode).addr s (0x1020ef +
        4)) 4)
      code := codeRange 0x1020ef [0x8b, 0x5c, 0x24, 0x24]
      step := mov_r32_m32_noRex_effect_step 0x1020ef 3 (.sib 4 none 0 (.d8 0x24)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20ef 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 36 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 3) (.location (.stack 36))) (dst := 3) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1020f3 0x1020f5 [.add (.reg 5) (.location (.reg 3))] := by
    let ex : InstructionExecution 0x1020f3 0x1020f5 (addR32R32Effect 0x1020f3 2 5 3) := {
      pre := (fun s ↦ s.RIP = 0x1020f3)
      code := codeRange 0x1020f3 [0x1, 0xdd]
      step := add_r32_r32_effect_step 0x1020f3 0xdd (by decide)
      present := fun hc ↦ program_text_slice hc 0x20f3 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 3))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1020f5 0x1020f8 [.xor (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x1020f5 0x1020f8 (xorR32R32Effect 0x1020f5 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x1020f5)
      code := codeRange 0x1020f5 [0x45, 0x31, 0xe7]
      step := xor_r32_r32_rex_effect_step 0x1020f5 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20f5 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 12))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1020f8 0x1020fb [.add (.reg 5) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x1020f8 0x1020fb (addR32R32Effect 0x1020f8 3 5 15) := {
      pre := (fun s ↦ s.RIP = 0x1020f8)
      code := codeRange 0x1020f8 [0x44, 0x1, 0xfd]
      step := add_r32_r32_rex_effect_step 0x1020f8 0x44 0xfd (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20f8 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 15))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1020fb 0x102101 [.add (.reg 5) (.immediate 0xfde5380c)] := by
    let ex : InstructionExecution 0x1020fb 0x102101 (addR32Imm32Effect 0x1020fb 6 5 0xfde5380c) := {
      pre := (fun s ↦ s.RIP = 0x1020fb)
      code := codeRange 0x1020fb [0x81, 0xc5, 0xc, 0x38, 0xe5, 0xfd]
      step := add_r32_imm32_effect_step 0x1020fb 0xc5 0xfde5380c (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x20fb 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.immediate 0xfde5380c)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102101 0x102104 [.rol (.reg 5) 23] := by
    let ex : InstructionExecution 0x102101 0x102104 (rolR32Effect 0x102101 3 5 23) := {
      pre := (fun s ↦ s.RIP = 0x102101)
      code := codeRange 0x102101 [0xc1, 0xc5, 0x17]
      step := rol_r32_imm8_effect_step 0x102101 0xc5 0x17 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2101 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 5) 23) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102104 0x102107 [.add (.reg 5) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x102104 0x102107 (addR32R32Effect 0x102104 3 5 12) := {
      pre := (fun s ↦ s.RIP = 0x102104)
      code := codeRange 0x102104 [0x44, 0x1, 0xe5]
      step := add_r32_r32_rex_effect_step 0x102104 0x44 0xe5 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2104 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 12))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment36, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7))))))

theorem segment37_runs [Bindings] :
    RunWords 0x102107 0x102123 segment37 := by
  have h1 : RunWords 0x102107 0x10210a [.mov (.reg 15) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x102107 0x10210a (movR32R32Effect 0x102107 3 15 5) := {
      pre := (fun s ↦ s.RIP = 0x102107)
      code := codeRange 0x102107 [0x41, 0x89, 0xef]
      step := mov_r32_r32_rex_effect_step 0x102107 0x41 0xef (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2107 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 5))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x10210a 0x10210d [.xor (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x10210a 0x10210d (xorR32R32Effect 0x10210a 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x10210a)
      code := codeRange 0x10210a [0x45, 0x31, 0xe7]
      step := xor_r32_r32_rex_effect_step 0x10210a 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x210a 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 12))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x10210d 0x102110 [.mov (.reg 1) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x10210d 0x102110 (movR32R32Effect 0x10210d 3 1 15) := {
      pre := (fun s ↦ s.RIP = 0x10210d)
      code := codeRange 0x10210d [0x44, 0x89, 0xf9]
      step := mov_r32_r32_rex_effect_step 0x10210d 0x44 0xf9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x210d 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 1) (.location (.reg 15))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102110 0x102112 [.xor (.reg 1) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102110 0x102112 (xorR32R32Effect 0x102110 2 1 2) := {
      pre := (fun s ↦ s.RIP = 0x102110)
      code := codeRange 0x102110 [0x31, 0xd1]
      step := xor_r32_r32_effect_step 0x102110 0xd1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2110 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 1) (.location (.reg 2))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102112 0x102116 [.add (.reg 0) (.location (.stack 80))] := by
    let ex : InstructionExecution 0x102112 0x102116 (addR32M32Effect 0x102112 4 0 (.sib 4 none 0
      (.d8 0x50))) := {
      pre := (LoadPre 0x102112 (fun s ↦ ((.sib 4 none 0 (.d8 0x50)) : AddrMode).addr s (0x102112 +
        4)) 4)
      code := codeRange 0x102112 [0x3, 0x44, 0x24, 0x50]
      step := add_r32_m32_noRex_effect_step 0x102112 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2112 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 80 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.stack 80))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102116 0x102118 [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102116 0x102118 (addR32R32Effect 0x102116 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x102116)
      code := codeRange 0x102116 [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x102116 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2116 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 0))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102118 0x10211e [.add (.reg 1) (.immediate 0xa4beea44)] := by
    let ex : InstructionExecution 0x102118 0x10211e (addR32Imm32Effect 0x102118 6 1 0xa4beea44) := {
      pre := (fun s ↦ s.RIP = 0x102118)
      code := codeRange 0x102118 [0x81, 0xc1, 0x44, 0xea, 0xbe, 0xa4]
      step := add_r32_imm32_effect_step 0x102118 0xc1 0xa4beea44 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2118 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0xa4beea44)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x10211e 0x102121 [.rol (.reg 1) 4] := by
    let ex : InstructionExecution 0x10211e 0x102121 (rolR32Effect 0x10211e 3 1 4) := {
      pre := (fun s ↦ s.RIP = 0x10211e)
      code := codeRange 0x10211e [0xc1, 0xc1, 0x4]
      step := rol_r32_imm8_effect_step 0x10211e 0xc1 0x4 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x211e 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 4) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x102121 0x102123 [.add (.reg 1) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x102121 0x102123 (addR32R32Effect 0x102121 2 1 5) := {
      pre := (fun s ↦ s.RIP = 0x102121)
      code := codeRange 0x102121 [0x1, 0xe9]
      step := add_r32_r32_effect_step 0x102121 0xe9 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2121 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 5))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment37, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

theorem segment38_runs [Bindings] :
    RunWords 0x102123 0x102136 segment38 := by
  have h1 : RunWords 0x102123 0x102125 [.add (.reg 2) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x102123 0x102125 (addR32R32Effect 0x102123 2 2 7) := {
      pre := (fun s ↦ s.RIP = 0x102123)
      code := codeRange 0x102123 [0x1, 0xfa]
      step := add_r32_r32_effect_step 0x102123 0xfa (by decide)
      present := fun hc ↦ program_text_slice hc 0x2123 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 7))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x102125 0x102128 [.xor (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102125 0x102128 (xorR32R32Effect 0x102125 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x102125)
      code := codeRange 0x102125 [0x41, 0x31, 0xcf]
      step := xor_r32_r32_rex_effect_step 0x102125 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2125 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102128 0x10212b [.add (.reg 2) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x102128 0x10212b (addR32R32Effect 0x102128 3 2 15) := {
      pre := (fun s ↦ s.RIP = 0x102128)
      code := codeRange 0x102128 [0x44, 0x1, 0xfa]
      step := add_r32_r32_rex_effect_step 0x102128 0x44 0xfa (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2128 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 15))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x10212b 0x102131 [.add (.reg 2) (.immediate 0x4bdecfa9)] := by
    let ex : InstructionExecution 0x10212b 0x102131 (addR32Imm32Effect 0x10212b 6 2 0x4bdecfa9) := {
      pre := (fun s ↦ s.RIP = 0x10212b)
      code := codeRange 0x10212b [0x81, 0xc2, 0xa9, 0xcf, 0xde, 0x4b]
      step := add_r32_imm32_effect_step 0x10212b 0xc2 0x4bdecfa9 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x212b 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0x4bdecfa9)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102131 0x102134 [.rol (.reg 2) 11] := by
    let ex : InstructionExecution 0x102131 0x102134 (rolR32Effect 0x102131 3 2 11) := {
      pre := (fun s ↦ s.RIP = 0x102131)
      code := codeRange 0x102131 [0xc1, 0xc2, 0xb]
      step := rol_r32_imm8_effect_step 0x102131 0xc2 0xb (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2131 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 11) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102134 0x102136 [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102134 0x102136 (addR32R32Effect 0x102134 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x102134)
      code := codeRange 0x102134 [0x1, 0xca]
      step := add_r32_r32_effect_step 0x102134 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x2134 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 1))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment38, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6)))))

theorem segment39_runs [Bindings] :
    RunWords 0x102136 0x102154 segment39 := by
  have h1 : RunWords 0x102136 0x102138 [.mov (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102136 0x102138 (movR32R32Effect 0x102136 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x102136)
      code := codeRange 0x102136 [0x89, 0xd0]
      step := mov_r32_r32_effect_step 0x102136 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2136 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 0) (.location (.reg 2))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x102138 0x10213a [.xor (.reg 0) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102138 0x10213a (xorR32R32Effect 0x102138 2 0 1) := {
      pre := (fun s ↦ s.RIP = 0x102138)
      code := codeRange 0x102138 [0x31, 0xc8]
      step := xor_r32_r32_effect_step 0x102138 0xc8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2138 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 0) (.location (.reg 1))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x10213a 0x10213d [.mov (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x10213a 0x10213d (movR32R32Effect 0x10213a 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x10213a)
      code := codeRange 0x10213a [0x41, 0x89, 0xc7]
      step := mov_r32_r32_rex_effect_step 0x10213a 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x213a 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x10213d 0x102140 [.xor (.reg 15) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x10213d 0x102140 (xorR32R32Effect 0x10213d 3 15 5) := {
      pre := (fun s ↦ s.RIP = 0x10213d)
      code := codeRange 0x10213d [0x41, 0x31, 0xef]
      step := xor_r32_r32_rex_effect_step 0x10213d 0x41 0xef (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x213d 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 5))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102140 0x102143 [.add (.reg 12) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x102140 0x102143 (addR32R32Effect 0x102140 3 12 8) := {
      pre := (fun s ↦ s.RIP = 0x102140)
      code := codeRange 0x102140 [0x45, 0x1, 0xc4]
      step := add_r32_r32_rex_effect_step 0x102140 0x45 0xc4 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2140 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 8))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102143 0x102146 [.add (.reg 12) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x102143 0x102146 (addR32R32Effect 0x102143 3 12 15) := {
      pre := (fun s ↦ s.RIP = 0x102143)
      code := codeRange 0x102143 [0x45, 0x1, 0xfc]
      step := add_r32_r32_rex_effect_step 0x102143 0x45 0xfc (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2143 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 15))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102146 0x10214d [.add (.reg 12) (.immediate 0xf6bb4b60)] := by
    let ex : InstructionExecution 0x102146 0x10214d (addR32Imm32Effect 0x102146 7 12 0xf6bb4b60) :=
      {
      pre := (fun s ↦ s.RIP = 0x102146)
      code := codeRange 0x102146 [0x41, 0x81, 0xc4, 0x60, 0x4b, 0xbb, 0xf6]
      step := add_r32_imm32_rex_effect_step 0x102146 0x41 0xc4 0xf6bb4b60 (by simp [RexNoWPrefix])
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2146 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.immediate 0xf6bb4b60)) (dst := 12) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x10214d 0x102151 [.rol (.reg 12) 16] := by
    let ex : InstructionExecution 0x10214d 0x102151 (rolR32Effect 0x10214d 4 12 16) := {
      pre := (fun s ↦ s.RIP = 0x10214d)
      code := codeRange 0x10214d [0x41, 0xc1, 0xc4, 0x10]
      step := rol_r32_imm8_rex_effect_step 0x10214d 0x41 0xc4 0x10 (by simp [RexNoWPrefix]) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x214d 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 12) 16) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x102151 0x102154 [.add (.reg 12) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102151 0x102154 (addR32R32Effect 0x102151 3 12 2) := {
      pre := (fun s ↦ s.RIP = 0x102151)
      code := codeRange 0x102151 [0x41, 0x1, 0xd4]
      step := add_r32_r32_rex_effect_step 0x102151 0x41 0xd4 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2151 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 2))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment39, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

theorem segment40_runs [Bindings] :
    RunWords 0x102154 0x10216c segment40 := by
  have h1 : RunWords 0x102154 0x102159 [.mov (.reg 14) (.location (.stack 40))] := by
    let ex : InstructionExecution 0x102154 0x102159 (movR32M32Effect 0x102154 14 (.sib 4 none 0 (.d8
      0x28))) := {
      pre := (LoadPre 0x102154 (fun s ↦ ((.sib 4 none 0 (.d8 0x28)) : AddrMode).addr s (0x102154 +
        5)) 4)
      code := codeRange 0x102154 [0x44, 0x8b, 0x74, 0x24, 0x28]
      step := mov_r32_m32_effect_step 0x102154 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8
        0x28)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2154 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 40 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 14) (.location (.stack 40))) (dst := 14) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x102159 0x10215c [.add (.reg 5) (.location (.reg 14))] := by
    let ex : InstructionExecution 0x102159 0x10215c (addR32R32Effect 0x102159 3 5 14) := {
      pre := (fun s ↦ s.RIP = 0x102159)
      code := codeRange 0x102159 [0x44, 0x1, 0xf5]
      step := add_r32_r32_rex_effect_step 0x102159 0x44 0xf5 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2159 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 14))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x10215c 0x10215f [.xor (.reg 0) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x10215c 0x10215f (xorR32R32Effect 0x10215c 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x10215c)
      code := codeRange 0x10215c [0x44, 0x31, 0xe0]
      step := xor_r32_r32_rex_effect_step 0x10215c 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x215c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 0) (.location (.reg 12))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x10215f 0x102161 [.add (.reg 0) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x10215f 0x102161 (addR32R32Effect 0x10215f 2 0 5) := {
      pre := (fun s ↦ s.RIP = 0x10215f)
      code := codeRange 0x10215f [0x1, 0xe8]
      step := add_r32_r32_effect_step 0x10215f 0xe8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x215f 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 5))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102161 0x102166 [.add (.reg 0) (.immediate 0xbebfbc70)] := by
    let ex : InstructionExecution 0x102161 0x102166 (addR32Imm32Effect 0x102161 5 0 0xbebfbc70) := {
      pre := (fun s ↦ s.RIP = 0x102161)
      code := codeRange 0x102161 [0x5, 0x70, 0xbc, 0xbf, 0xbe]
      step := Register.add_eax_imm32_effect_step 0x102161 0xbebfbc70
      present := fun hc ↦ program_text_slice hc 0x2161 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0xbebfbc70)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102166 0x102169 [.rol (.reg 0) 23] := by
    let ex : InstructionExecution 0x102166 0x102169 (rolR32Effect 0x102166 3 0 23) := {
      pre := (fun s ↦ s.RIP = 0x102166)
      code := codeRange 0x102166 [0xc1, 0xc0, 0x17]
      step := rol_r32_imm8_effect_step 0x102166 0xc0 0x17 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2166 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 23) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102169 0x10216c [.add (.reg 0) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x102169 0x10216c (addR32R32Effect 0x102169 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x102169)
      code := codeRange 0x102169 [0x44, 0x1, 0xe0]
      step := add_r32_r32_rex_effect_step 0x102169 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2169 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 12))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment40, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7))))))

theorem segment41_runs [Bindings] :
    RunWords 0x10216c 0x102186 segment41 := by
  have h1 : RunWords 0x10216c 0x10216f [.mov (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x10216c 0x10216f (movR32R32Effect 0x10216c 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x10216c)
      code := codeRange 0x10216c [0x45, 0x89, 0xe7]
      step := mov_r32_r32_rex_effect_step 0x10216c 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x216c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 12))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x10216f 0x102172 [.xor (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x10216f 0x102172 (xorR32R32Effect 0x10216f 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x10216f)
      code := codeRange 0x10216f [0x41, 0x31, 0xd7]
      step := xor_r32_r32_rex_effect_step 0x10216f 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x216f 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102172 0x102175 [.add (.reg 1) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x102172 0x102175 (addR32R32Effect 0x102172 3 1 10) := {
      pre := (fun s ↦ s.RIP = 0x102172)
      code := codeRange 0x102172 [0x44, 0x1, 0xd1]
      step := add_r32_r32_rex_effect_step 0x102172 0x44 0xd1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2172 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 10))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102175 0x102178 [.xor (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102175 0x102178 (xorR32R32Effect 0x102175 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x102175)
      code := codeRange 0x102175 [0x41, 0x31, 0xc7]
      step := xor_r32_r32_rex_effect_step 0x102175 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2175 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102178 0x10217b [.add (.reg 1) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x102178 0x10217b (addR32R32Effect 0x102178 3 1 15) := {
      pre := (fun s ↦ s.RIP = 0x102178)
      code := codeRange 0x102178 [0x44, 0x1, 0xf9]
      step := add_r32_r32_rex_effect_step 0x102178 0x44 0xf9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2178 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 15))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x10217b 0x102181 [.add (.reg 1) (.immediate 0x289b7ec6)] := by
    let ex : InstructionExecution 0x10217b 0x102181 (addR32Imm32Effect 0x10217b 6 1 0x289b7ec6) := {
      pre := (fun s ↦ s.RIP = 0x10217b)
      code := codeRange 0x10217b [0x81, 0xc1, 0xc6, 0x7e, 0x9b, 0x28]
      step := add_r32_imm32_effect_step 0x10217b 0xc1 0x289b7ec6 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x217b 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0x289b7ec6)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102181 0x102184 [.rol (.reg 1) 4] := by
    let ex : InstructionExecution 0x102181 0x102184 (rolR32Effect 0x102181 3 1 4) := {
      pre := (fun s ↦ s.RIP = 0x102181)
      code := codeRange 0x102181 [0xc1, 0xc1, 0x4]
      step := rol_r32_imm8_effect_step 0x102181 0xc1 0x4 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2181 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 4) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x102184 0x102186 [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102184 0x102186 (addR32R32Effect 0x102184 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x102184)
      code := codeRange 0x102184 [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x102184 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2184 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 0))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment41, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8)))))))

theorem segment42_runs [Bindings] :
    RunWords 0x102186 0x1021a4 segment42 := by
  have h1 : RunWords 0x102186 0x102189 [.mov (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102186 0x102189 (movR32R32Effect 0x102186 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x102186)
      code := codeRange 0x102186 [0x41, 0x89, 0xc7]
      step := mov_r32_r32_rex_effect_step 0x102186 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2186 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x102189 0x10218c [.xor (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x102189 0x10218c (xorR32R32Effect 0x102189 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x102189)
      code := codeRange 0x102189 [0x45, 0x31, 0xe7]
      step := xor_r32_r32_rex_effect_step 0x102189 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2189 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 12))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x10218c 0x102191 [.mov (.reg 7) (.location (.stack 88))] := by
    let ex : InstructionExecution 0x10218c 0x102191 (movR64M64Effect 0x10218c 7 (.sib 4 none 0 (.d8
      0x58))) := {
      pre := (LoadPre 0x10218c (fun s ↦ ((.sib 4 none 0 (.d8 0x58)) : AddrMode).addr s (0x10218c +
        5)) 8)
      code := codeRange 0x10218c [0x48, 0x8b, 0x7c, 0x24, 0x58]
      step := mov_r64_m64_effect_step 0x10218c 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8
        0x58)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x218c 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 88 8 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 7) (.location (.stack 88))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102191 0x102193 [.add (.reg 2) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x102191 0x102193 (addR32R32Effect 0x102191 2 2 7) := {
      pre := (fun s ↦ s.RIP = 0x102191)
      code := codeRange 0x102191 [0x1, 0xfa]
      step := add_r32_r32_effect_step 0x102191 0xfa (by decide)
      present := fun hc ↦ program_text_slice hc 0x2191 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 7))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102193 0x102196 [.xor (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102193 0x102196 (xorR32R32Effect 0x102193 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x102193)
      code := codeRange 0x102193 [0x41, 0x31, 0xcf]
      step := xor_r32_r32_rex_effect_step 0x102193 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2193 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102196 0x102199 [.add (.reg 2) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x102196 0x102199 (addR32R32Effect 0x102196 3 2 15) := {
      pre := (fun s ↦ s.RIP = 0x102196)
      code := codeRange 0x102196 [0x44, 0x1, 0xfa]
      step := add_r32_r32_rex_effect_step 0x102196 0x44 0xfa (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2196 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 15))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102199 0x10219f [.add (.reg 2) (.immediate 0xeaa127fa)] := by
    let ex : InstructionExecution 0x102199 0x10219f (addR32Imm32Effect 0x102199 6 2 0xeaa127fa) := {
      pre := (fun s ↦ s.RIP = 0x102199)
      code := codeRange 0x102199 [0x81, 0xc2, 0xfa, 0x27, 0xa1, 0xea]
      step := add_r32_imm32_effect_step 0x102199 0xc2 0xeaa127fa (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2199 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0xeaa127fa)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x10219f 0x1021a2 [.rol (.reg 2) 11] := by
    let ex : InstructionExecution 0x10219f 0x1021a2 (rolR32Effect 0x10219f 3 2 11) := {
      pre := (fun s ↦ s.RIP = 0x10219f)
      code := codeRange 0x10219f [0xc1, 0xc2, 0xb]
      step := rol_r32_imm8_effect_step 0x10219f 0xc2 0xb (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x219f 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 11) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x1021a2 0x1021a4 [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1021a2 0x1021a4 (addR32R32Effect 0x1021a2 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x1021a2)
      code := codeRange 0x1021a2 [0x1, 0xca]
      step := add_r32_r32_effect_step 0x1021a2 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x21a2 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 1))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment42, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

theorem segment43_runs [Bindings] :
    RunWords 0x1021a4 0x1021c1 segment43 := by
  have h1 : RunWords 0x1021a4 0x1021a7 [.mov (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1021a4 0x1021a7 (movR32R32Effect 0x1021a4 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x1021a4)
      code := codeRange 0x1021a4 [0x41, 0x89, 0xcf]
      step := mov_r32_r32_rex_effect_step 0x1021a4 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21a4 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1021a7 0x1021aa [.xor (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1021a7 0x1021aa (xorR32R32Effect 0x1021a7 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x1021a7)
      code := codeRange 0x1021a7 [0x41, 0x31, 0xc7]
      step := xor_r32_r32_rex_effect_step 0x1021a7 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21a7 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1021aa 0x1021ad [.add (.reg 12) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x1021aa 0x1021ad (addR32R32Effect 0x1021aa 3 12 9) := {
      pre := (fun s ↦ s.RIP = 0x1021aa)
      code := codeRange 0x1021aa [0x45, 0x1, 0xcc]
      step := add_r32_r32_rex_effect_step 0x1021aa 0x45 0xcc (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21aa 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 9))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1021ad 0x1021b0 [.xor (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1021ad 0x1021b0 (xorR32R32Effect 0x1021ad 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x1021ad)
      code := codeRange 0x1021ad [0x41, 0x31, 0xd7]
      step := xor_r32_r32_rex_effect_step 0x1021ad 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21ad 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1021b0 0x1021b3 [.add (.reg 12) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x1021b0 0x1021b3 (addR32R32Effect 0x1021b0 3 12 15) := {
      pre := (fun s ↦ s.RIP = 0x1021b0)
      code := codeRange 0x1021b0 [0x45, 0x1, 0xfc]
      step := add_r32_r32_rex_effect_step 0x1021b0 0x45 0xfc (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21b0 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 15))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x1021b3 0x1021ba [.add (.reg 12) (.immediate 0xd4ef3085)] := by
    let ex : InstructionExecution 0x1021b3 0x1021ba (addR32Imm32Effect 0x1021b3 7 12 0xd4ef3085) :=
      {
      pre := (fun s ↦ s.RIP = 0x1021b3)
      code := codeRange 0x1021b3 [0x41, 0x81, 0xc4, 0x85, 0x30, 0xef, 0xd4]
      step := add_r32_imm32_rex_effect_step 0x1021b3 0x41 0xc4 0xd4ef3085 (by simp [RexNoWPrefix])
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21b3 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.immediate 0xd4ef3085)) (dst := 12) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1021ba 0x1021be [.rol (.reg 12) 16] := by
    let ex : InstructionExecution 0x1021ba 0x1021be (rolR32Effect 0x1021ba 4 12 16) := {
      pre := (fun s ↦ s.RIP = 0x1021ba)
      code := codeRange 0x1021ba [0x41, 0xc1, 0xc4, 0x10]
      step := rol_r32_imm8_rex_effect_step 0x1021ba 0x41 0xc4 0x10 (by simp [RexNoWPrefix]) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21ba 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 12) 16) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1021be 0x1021c1 [.add (.reg 12) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1021be 0x1021c1 (addR32R32Effect 0x1021be 3 12 2) := {
      pre := (fun s ↦ s.RIP = 0x1021be)
      code := codeRange 0x1021be [0x41, 0x1, 0xd4]
      step := add_r32_r32_rex_effect_step 0x1021be 0x41 0xd4 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21be 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 2))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment43, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8)))))))

theorem segment44_runs [Bindings] :
    RunWords 0x1021c1 0x1021de segment44 := by
  have h1 : RunWords 0x1021c1 0x1021c4 [.mov (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1021c1 0x1021c4 (movR32R32Effect 0x1021c1 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x1021c1)
      code := codeRange 0x1021c1 [0x41, 0x89, 0xd7]
      step := mov_r32_r32_rex_effect_step 0x1021c1 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21c1 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1021c4 0x1021c7 [.xor (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1021c4 0x1021c7 (xorR32R32Effect 0x1021c4 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x1021c4)
      code := codeRange 0x1021c4 [0x41, 0x31, 0xcf]
      step := xor_r32_r32_rex_effect_step 0x1021c4 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21c4 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1021c7 0x1021cb [.mov (.reg 5) (.location (.stack 56))] := by
    let ex : InstructionExecution 0x1021c7 0x1021cb (movR32M32NoRexEffect 0x1021c7 5 (.sib 4 none 0
      (.d8 0x38))) := {
      pre := (LoadPre 0x1021c7 (fun s ↦ ((.sib 4 none 0 (.d8 0x38)) : AddrMode).addr s (0x1021c7 +
        4)) 4)
      code := codeRange 0x1021c7 [0x8b, 0x6c, 0x24, 0x38]
      step := mov_r32_m32_noRex_effect_step 0x1021c7 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21c7 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 56 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 5) (.location (.stack 56))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1021cb 0x1021cd [.add (.reg 0) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x1021cb 0x1021cd (addR32R32Effect 0x1021cb 2 0 5) := {
      pre := (fun s ↦ s.RIP = 0x1021cb)
      code := codeRange 0x1021cb [0x1, 0xe8]
      step := add_r32_r32_effect_step 0x1021cb 0xe8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x21cb 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 5))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1021cd 0x1021d0 [.xor (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x1021cd 0x1021d0 (xorR32R32Effect 0x1021cd 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x1021cd)
      code := codeRange 0x1021cd [0x45, 0x31, 0xe7]
      step := xor_r32_r32_rex_effect_step 0x1021cd 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21cd 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 12))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x1021d0 0x1021d3 [.add (.reg 0) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x1021d0 0x1021d3 (addR32R32Effect 0x1021d0 3 0 15) := {
      pre := (fun s ↦ s.RIP = 0x1021d0)
      code := codeRange 0x1021d0 [0x44, 0x1, 0xf8]
      step := add_r32_r32_rex_effect_step 0x1021d0 0x44 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21d0 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 15))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1021d3 0x1021d8 [.add (.reg 0) (.immediate 0x4881d05)] := by
    let ex : InstructionExecution 0x1021d3 0x1021d8 (addR32Imm32Effect 0x1021d3 5 0 0x4881d05) := {
      pre := (fun s ↦ s.RIP = 0x1021d3)
      code := codeRange 0x1021d3 [0x5, 0x5, 0x1d, 0x88, 0x4]
      step := Register.add_eax_imm32_effect_step 0x1021d3 0x4881d05
      present := fun hc ↦ program_text_slice hc 0x21d3 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0x4881d05)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1021d8 0x1021db [.rol (.reg 0) 23] := by
    let ex : InstructionExecution 0x1021d8 0x1021db (rolR32Effect 0x1021d8 3 0 23) := {
      pre := (fun s ↦ s.RIP = 0x1021d8)
      code := codeRange 0x1021d8 [0xc1, 0xc0, 0x17]
      step := rol_r32_imm8_effect_step 0x1021d8 0xc0 0x17 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21d8 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 23) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x1021db 0x1021de [.add (.reg 0) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x1021db 0x1021de (addR32R32Effect 0x1021db 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x1021db)
      code := codeRange 0x1021db [0x44, 0x1, 0xe0]
      step := add_r32_r32_rex_effect_step 0x1021db 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21db 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 12))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment44, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

theorem segment45_runs [Bindings] :
    RunWords 0x1021de 0x1021f9 segment45 := by
  have h1 : RunWords 0x1021de 0x1021e1 [.mov (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x1021de 0x1021e1 (movR32R32Effect 0x1021de 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x1021de)
      code := codeRange 0x1021de [0x45, 0x89, 0xe7]
      step := mov_r32_r32_rex_effect_step 0x1021de 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21de 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 12))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1021e1 0x1021e4 [.xor (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1021e1 0x1021e4 (xorR32R32Effect 0x1021e1 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x1021e1)
      code := codeRange 0x1021e1 [0x41, 0x31, 0xd7]
      step := xor_r32_r32_rex_effect_step 0x1021e1 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21e1 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1021e4 0x1021e8 [.add (.reg 1) (.location (.stack 4))] := by
    let ex : InstructionExecution 0x1021e4 0x1021e8 (addR32M32Effect 0x1021e4 4 1 (.sib 4 none 0
      (.d8 0x4))) := {
      pre := (LoadPre 0x1021e4 (fun s ↦ ((.sib 4 none 0 (.d8 0x4)) : AddrMode).addr s (0x1021e4 +
        4)) 4)
      code := codeRange 0x1021e4 [0x3, 0x4c, 0x24, 0x4]
      step := add_r32_m32_noRex_effect_step 0x1021e4 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21e4 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 4 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.stack 4))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1021e8 0x1021eb [.xor (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1021e8 0x1021eb (xorR32R32Effect 0x1021e8 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x1021e8)
      code := codeRange 0x1021e8 [0x41, 0x31, 0xc7]
      step := xor_r32_r32_rex_effect_step 0x1021e8 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21e8 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1021eb 0x1021ee [.add (.reg 1) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x1021eb 0x1021ee (addR32R32Effect 0x1021eb 3 1 15) := {
      pre := (fun s ↦ s.RIP = 0x1021eb)
      code := codeRange 0x1021eb [0x44, 0x1, 0xf9]
      step := add_r32_r32_rex_effect_step 0x1021eb 0x44 0xf9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21eb 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 15))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x1021ee 0x1021f4 [.add (.reg 1) (.immediate 0xd9d4d039)] := by
    let ex : InstructionExecution 0x1021ee 0x1021f4 (addR32Imm32Effect 0x1021ee 6 1 0xd9d4d039) := {
      pre := (fun s ↦ s.RIP = 0x1021ee)
      code := codeRange 0x1021ee [0x81, 0xc1, 0x39, 0xd0, 0xd4, 0xd9]
      step := add_r32_imm32_effect_step 0x1021ee 0xc1 0xd9d4d039 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21ee 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0xd9d4d039)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1021f4 0x1021f7 [.rol (.reg 1) 4] := by
    let ex : InstructionExecution 0x1021f4 0x1021f7 (rolR32Effect 0x1021f4 3 1 4) := {
      pre := (fun s ↦ s.RIP = 0x1021f4)
      code := codeRange 0x1021f4 [0xc1, 0xc1, 0x4]
      step := rol_r32_imm8_effect_step 0x1021f4 0xc1 0x4 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21f4 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 4) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1021f7 0x1021f9 [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1021f7 0x1021f9 (addR32R32Effect 0x1021f7 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x1021f7)
      code := codeRange 0x1021f7 [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x1021f7 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x21f7 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 0))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment45, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8)))))))

theorem segment46_runs [Bindings] :
    RunWords 0x1021f9 0x102213 segment46 := by
  have h1 : RunWords 0x1021f9 0x1021fc [.mov (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1021f9 0x1021fc (movR32R32Effect 0x1021f9 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x1021f9)
      code := codeRange 0x1021f9 [0x41, 0x89, 0xc7]
      step := mov_r32_r32_rex_effect_step 0x1021f9 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21f9 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1021fc 0x1021ff [.xor (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x1021fc 0x1021ff (xorR32R32Effect 0x1021fc 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x1021fc)
      code := codeRange 0x1021fc [0x45, 0x31, 0xe7]
      step := xor_r32_r32_rex_effect_step 0x1021fc 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21fc 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 12))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1021ff 0x102202 [.add (.reg 2) (.location (.reg 11))] := by
    let ex : InstructionExecution 0x1021ff 0x102202 (addR32R32Effect 0x1021ff 3 2 11) := {
      pre := (fun s ↦ s.RIP = 0x1021ff)
      code := codeRange 0x1021ff [0x44, 0x1, 0xda]
      step := add_r32_r32_rex_effect_step 0x1021ff 0x44 0xda (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x21ff 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 11))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102202 0x102205 [.xor (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102202 0x102205 (xorR32R32Effect 0x102202 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x102202)
      code := codeRange 0x102202 [0x41, 0x31, 0xcf]
      step := xor_r32_r32_rex_effect_step 0x102202 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2202 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102205 0x102208 [.add (.reg 2) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x102205 0x102208 (addR32R32Effect 0x102205 3 2 15) := {
      pre := (fun s ↦ s.RIP = 0x102205)
      code := codeRange 0x102205 [0x44, 0x1, 0xfa]
      step := add_r32_r32_rex_effect_step 0x102205 0x44 0xfa (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2205 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 15))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102208 0x10220e [.add (.reg 2) (.immediate 0xe6db99e5)] := by
    let ex : InstructionExecution 0x102208 0x10220e (addR32Imm32Effect 0x102208 6 2 0xe6db99e5) := {
      pre := (fun s ↦ s.RIP = 0x102208)
      code := codeRange 0x102208 [0x81, 0xc2, 0xe5, 0x99, 0xdb, 0xe6]
      step := add_r32_imm32_effect_step 0x102208 0xc2 0xe6db99e5 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2208 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0xe6db99e5)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x10220e 0x102211 [.rol (.reg 2) 11] := by
    let ex : InstructionExecution 0x10220e 0x102211 (rolR32Effect 0x10220e 3 2 11) := {
      pre := (fun s ↦ s.RIP = 0x10220e)
      code := codeRange 0x10220e [0xc1, 0xc2, 0xb]
      step := rol_r32_imm8_effect_step 0x10220e 0xc2 0xb (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x220e 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 11) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x102211 0x102213 [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102211 0x102213 (addR32R32Effect 0x102211 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x102211)
      code := codeRange 0x102211 [0x1, 0xca]
      step := add_r32_r32_effect_step 0x102211 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x2211 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 1))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment46, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8)))))))

theorem segment47_runs [Bindings] :
    RunWords 0x102213 0x102235 segment47 := by
  have h1 : RunWords 0x102213 0x102216 [.mov (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102213 0x102216 (movR32R32Effect 0x102213 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x102213)
      code := codeRange 0x102213 [0x41, 0x89, 0xcf]
      step := mov_r32_r32_rex_effect_step 0x102213 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2213 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x102216 0x102219 [.xor (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102216 0x102219 (xorR32R32Effect 0x102216 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x102216)
      code := codeRange 0x102216 [0x41, 0x31, 0xc7]
      step := xor_r32_r32_rex_effect_step 0x102216 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2216 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102219 0x10221e [.mov (.reg 10) (.location (.stack 48))] := by
    let ex : InstructionExecution 0x102219 0x10221e (movR32M32Effect 0x102219 10 (.sib 4 none 0 (.d8
      0x30))) := {
      pre := (LoadPre 0x102219 (fun s ↦ ((.sib 4 none 0 (.d8 0x30)) : AddrMode).addr s (0x102219 +
        5)) 4)
      code := codeRange 0x102219 [0x44, 0x8b, 0x54, 0x24, 0x30]
      step := mov_r32_m32_effect_step 0x102219 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8
        0x30)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2219 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 48 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.stack 48))) (dst := 10) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x10221e 0x102221 [.add (.reg 12) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x10221e 0x102221 (addR32R32Effect 0x10221e 3 12 10) := {
      pre := (fun s ↦ s.RIP = 0x10221e)
      code := codeRange 0x10221e [0x45, 0x1, 0xd4]
      step := add_r32_r32_rex_effect_step 0x10221e 0x45 0xd4 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x221e 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 10))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102221 0x102224 [.xor (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102221 0x102224 (xorR32R32Effect 0x102221 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x102221)
      code := codeRange 0x102221 [0x41, 0x31, 0xd7]
      step := xor_r32_r32_rex_effect_step 0x102221 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2221 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102224 0x102227 [.add (.reg 12) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x102224 0x102227 (addR32R32Effect 0x102224 3 12 15) := {
      pre := (fun s ↦ s.RIP = 0x102224)
      code := codeRange 0x102224 [0x45, 0x1, 0xfc]
      step := add_r32_r32_rex_effect_step 0x102224 0x45 0xfc (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2224 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 15))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102227 0x10222e [.add (.reg 12) (.immediate 0x1fa27cf8)] := by
    let ex : InstructionExecution 0x102227 0x10222e (addR32Imm32Effect 0x102227 7 12 0x1fa27cf8) :=
      {
      pre := (fun s ↦ s.RIP = 0x102227)
      code := codeRange 0x102227 [0x41, 0x81, 0xc4, 0xf8, 0x7c, 0xa2, 0x1f]
      step := add_r32_imm32_rex_effect_step 0x102227 0x41 0xc4 0x1fa27cf8 (by simp [RexNoWPrefix])
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2227 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.immediate 0x1fa27cf8)) (dst := 12) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x10222e 0x102232 [.rol (.reg 12) 16] := by
    let ex : InstructionExecution 0x10222e 0x102232 (rolR32Effect 0x10222e 4 12 16) := {
      pre := (fun s ↦ s.RIP = 0x10222e)
      code := codeRange 0x10222e [0x41, 0xc1, 0xc4, 0x10]
      step := rol_r32_imm8_rex_effect_step 0x10222e 0x41 0xc4 0x10 (by simp [RexNoWPrefix]) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x222e 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 12) 16) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x102232 0x102235 [.add (.reg 12) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102232 0x102235 (addR32R32Effect 0x102232 3 12 2) := {
      pre := (fun s ↦ s.RIP = 0x102232)
      code := codeRange 0x102232 [0x41, 0x1, 0xd4]
      step := add_r32_r32_rex_effect_step 0x102232 0x41 0xd4 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2232 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 2))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment47, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

theorem segment48_runs [Bindings] :
    RunWords 0x102235 0x102251 segment48 := by
  have h1 : RunWords 0x102235 0x102238 [.mov (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102235 0x102238 (movR32R32Effect 0x102235 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x102235)
      code := codeRange 0x102235 [0x41, 0x89, 0xd7]
      step := mov_r32_r32_rex_effect_step 0x102235 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2235 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x102238 0x10223b [.xor (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102238 0x10223b (xorR32R32Effect 0x102238 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x102238)
      code := codeRange 0x102238 [0x41, 0x31, 0xcf]
      step := xor_r32_r32_rex_effect_step 0x102238 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2238 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x10223b 0x10223e [.add (.reg 0) (.location (.reg 13))] := by
    let ex : InstructionExecution 0x10223b 0x10223e (addR32R32Effect 0x10223b 3 0 13) := {
      pre := (fun s ↦ s.RIP = 0x10223b)
      code := codeRange 0x10223b [0x44, 0x1, 0xe8]
      step := add_r32_r32_rex_effect_step 0x10223b 0x44 0xe8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x223b 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 13))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x10223e 0x102241 [.xor (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x10223e 0x102241 (xorR32R32Effect 0x10223e 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x10223e)
      code := codeRange 0x10223e [0x45, 0x31, 0xe7]
      step := xor_r32_r32_rex_effect_step 0x10223e 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x223e 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 15) (.location (.reg 12))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102241 0x102244 [.add (.reg 0) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x102241 0x102244 (addR32R32Effect 0x102241 3 0 15) := {
      pre := (fun s ↦ s.RIP = 0x102241)
      code := codeRange 0x102241 [0x44, 0x1, 0xf8]
      step := add_r32_r32_rex_effect_step 0x102241 0x44 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2241 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 15))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102244 0x102249 [.add (.reg 0) (.immediate 0xc4ac5665)] := by
    let ex : InstructionExecution 0x102244 0x102249 (addR32Imm32Effect 0x102244 5 0 0xc4ac5665) := {
      pre := (fun s ↦ s.RIP = 0x102244)
      code := codeRange 0x102244 [0x5, 0x65, 0x56, 0xac, 0xc4]
      step := Register.add_eax_imm32_effect_step 0x102244 0xc4ac5665
      present := fun hc ↦ program_text_slice hc 0x2244 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0xc4ac5665)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102249 0x10224b [.add (.reg 1) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x102249 0x10224b (addR32R32Effect 0x102249 2 1 7) := {
      pre := (fun s ↦ s.RIP = 0x102249)
      code := codeRange 0x102249 [0x1, 0xf9]
      step := add_r32_r32_effect_step 0x102249 0xf9 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2249 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 7))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x10224b 0x10224e [.rol (.reg 0) 23] := by
    let ex : InstructionExecution 0x10224b 0x10224e (rolR32Effect 0x10224b 3 0 23) := {
      pre := (fun s ↦ s.RIP = 0x10224b)
      code := codeRange 0x10224b [0xc1, 0xc0, 0x17]
      step := rol_r32_imm8_effect_step 0x10224b 0xc0 0x17 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x224b 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 23) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x10224e 0x102251 [.add (.reg 0) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x10224e 0x102251 (addR32R32Effect 0x10224e 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x10224e)
      code := codeRange 0x10224e [0x44, 0x1, 0xe0]
      step := add_r32_r32_rex_effect_step 0x10224e 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x224e 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 12))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment48, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

end Md5.Proofs.Block.Rounds
