import Md5.Proofs.Block.Rounds.Step
import Md5.Proofs.Block.Rounds.Address
import Md5.Proofs.Block.Rounds.Interface
import Md5.Proofs.Block.Rounds.Register
import Md5.Proofs.Block.Rounds.Load
import Md5.Proofs.Block.Rounds.Store

namespace Md5.Proofs.Block.Rounds
open X86 X86.Machine X86.UserProcess X86Proofs

theorem segment17_runs [Bindings] :
    RunWords 0x101e78 0x101e99 segment17 := by
  have h1 : RunWords 0x101e78 0x101e7b [.mov (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101e78 0x101e7b (movR32R32Effect 0x101e78 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x101e78)
      code := codeRange 0x101e78 [0x41, 0x89, 0xd7]
      step := mov_r32_r32_rex_effect_step 0x101e78 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e78 3 (by decide +kernel)
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
  have h2 : RunWords 0x101e7b 0x101e7e [.and (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101e7b 0x101e7e (andR32R32Effect 0x101e7b 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x101e7b)
      code := codeRange 0x101e7b [0x41, 0x21, 0xc7]
      step := and_r32_r32_rex_effect_step 0x101e7b 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e7b 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101e7e 0x101e82 [.lea (.reg 12) (.reg 15) (.reg 5)] := by
    let ex : InstructionExecution 0x101e7e 0x101e82 (Register.leaR32Effect 0x101e7e 4 12 (.sib 15
      (some 5) 0 .none)) := {
      pre := (fun s ↦ s.RIP = 0x101e7e)
      code := codeRange 0x101e7e [0x45, 0x8d, 0x24, 0x2f]
      step := Register.lea_r32_rex_effect_step 0x101e7e 0x45 (by simp [RexNoWPrefix]) 4 (.sib 15
        (some 5) 0 .none) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e7e 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .lea (.reg 12) (.reg 15) (.reg 5)) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x101e82 0x101e89 [.add (.reg 12) (.immediate 0xf61e2562)] := by
    let ex : InstructionExecution 0x101e82 0x101e89 (addR32Imm32Effect 0x101e82 7 12 0xf61e2562) :=
      {
      pre := (fun s ↦ s.RIP = 0x101e82)
      code := codeRange 0x101e82 [0x41, 0x81, 0xc4, 0x62, 0x25, 0x1e, 0xf6]
      step := add_r32_imm32_rex_effect_step 0x101e82 0x41 0xc4 0xf61e2562 (by simp [RexNoWPrefix])
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e82 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.immediate 0xf61e2562)) (dst := 12) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101e89 0x101e8c [.and (.reg 13) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101e89 0x101e8c (andR32R32Effect 0x101e89 3 13 2) := {
      pre := (fun s ↦ s.RIP = 0x101e89)
      code := codeRange 0x101e89 [0x41, 0x21, 0xd5]
      step := and_r32_r32_rex_effect_step 0x101e89 0x41 0xd5 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e89 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 13) (.location (.reg 2))) (dst := 13) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101e8c 0x101e8f [.add (.reg 0) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x101e8c 0x101e8f (addR32R32Effect 0x101e8c 3 0 9) := {
      pre := (fun s ↦ s.RIP = 0x101e8c)
      code := codeRange 0x101e8c [0x44, 0x1, 0xc8]
      step := add_r32_r32_rex_effect_step 0x101e8c 0x44 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e8c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 9))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101e8f 0x101e92 [.add (.reg 0) (.location (.reg 13))] := by
    let ex : InstructionExecution 0x101e8f 0x101e92 (addR32R32Effect 0x101e8f 3 0 13) := {
      pre := (fun s ↦ s.RIP = 0x101e8f)
      code := codeRange 0x101e8f [0x44, 0x1, 0xe8]
      step := add_r32_r32_rex_effect_step 0x101e8f 0x44 0xe8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e8f 3 (by decide +kernel)
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
  have h8 : RunWords 0x101e92 0x101e96 [.rol (.reg 12) 5] := by
    let ex : InstructionExecution 0x101e92 0x101e96 (rolR32Effect 0x101e92 4 12 5) := {
      pre := (fun s ↦ s.RIP = 0x101e92)
      code := codeRange 0x101e92 [0x41, 0xc1, 0xc4, 0x5]
      step := rol_r32_imm8_rex_effect_step 0x101e92 0x41 0xc4 0x5 (by simp [RexNoWPrefix]) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e92 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 12) 5) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101e96 0x101e99 [.add (.reg 12) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101e96 0x101e99 (addR32R32Effect 0x101e96 3 12 2) := {
      pre := (fun s ↦ s.RIP = 0x101e96)
      code := codeRange 0x101e96 [0x41, 0x1, 0xd4]
      step := add_r32_r32_rex_effect_step 0x101e96 0x41 0xd4 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e96 3 (by decide +kernel)
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
  simpa only [segment17, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

theorem segment18_runs [Bindings] :
    RunWords 0x101e99 0x101eb9 segment18 := by
  have h1 : RunWords 0x101e99 0x101e9c [.mov (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101e99 0x101e9c (movR32R32Effect 0x101e99 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x101e99)
      code := codeRange 0x101e99 [0x45, 0x89, 0xe7]
      step := mov_r32_r32_rex_effect_step 0x101e99 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e99 3 (by decide +kernel)
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
  have h2 : RunWords 0x101e9c 0x101e9f [.and (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101e9c 0x101e9f (andR32R32Effect 0x101e9c 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x101e9c)
      code := codeRange 0x101e9c [0x41, 0x21, 0xcf]
      step := and_r32_r32_rex_effect_step 0x101e9c 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e9c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101e9f 0x101ea2 [.add (.reg 0) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101e9f 0x101ea2 (addR32R32Effect 0x101e9f 3 0 15) := {
      pre := (fun s ↦ s.RIP = 0x101e9f)
      code := codeRange 0x101e9f [0x44, 0x1, 0xf8]
      step := add_r32_r32_rex_effect_step 0x101e9f 0x44 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e9f 3 (by decide +kernel)
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
  have h4 : RunWords 0x101ea2 0x101ea7 [.add (.reg 0) (.immediate 0xc040b340)] := by
    let ex : InstructionExecution 0x101ea2 0x101ea7 (addR32Imm32Effect 0x101ea2 5 0 0xc040b340) := {
      pre := (fun s ↦ s.RIP = 0x101ea2)
      code := codeRange 0x101ea2 [0x5, 0x40, 0xb3, 0x40, 0xc0]
      step := Register.add_eax_imm32_effect_step 0x101ea2 0xc040b340
      present := fun hc ↦ program_text_slice hc 0x1ea2 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0xc040b340)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101ea7 0x101ea9 [.mov (.reg 5) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101ea7 0x101ea9 (movR32R32Effect 0x101ea7 2 5 2) := {
      pre := (fun s ↦ s.RIP = 0x101ea7)
      code := codeRange 0x101ea7 [0x89, 0xd5]
      step := mov_r32_r32_effect_step 0x101ea7 0xd5 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ea7 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 5) (.location (.reg 2))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101ea9 0x101eab [.not (.reg 5)] := by
    let ex : InstructionExecution 0x101ea9 0x101eab (notR32Effect 0x101ea9 2 5) := {
      pre := (fun s ↦ s.RIP = 0x101ea9)
      code := codeRange 0x101ea9 [0xf7, 0xd5]
      step := not_r32_effect_step 0x101ea9 0xd5 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ea9 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 5)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101eab 0x101eae [.and (.reg 5) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101eab 0x101eae (andR32R32Effect 0x101eab 3 5 12) := {
      pre := (fun s ↦ s.RIP = 0x101eab)
      code := codeRange 0x101eab [0x44, 0x21, 0xe5]
      step := and_r32_r32_rex_effect_step 0x101eab 0x44 0xe5 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eab 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 5) (.location (.reg 12))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101eae 0x101eb1 [.add (.reg 1) (.location (.reg 14))] := by
    let ex : InstructionExecution 0x101eae 0x101eb1 (addR32R32Effect 0x101eae 3 1 14) := {
      pre := (fun s ↦ s.RIP = 0x101eae)
      code := codeRange 0x101eae [0x44, 0x1, 0xf1]
      step := add_r32_r32_rex_effect_step 0x101eae 0x44 0xf1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eae 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 14))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101eb1 0x101eb3 [.add (.reg 1) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101eb1 0x101eb3 (addR32R32Effect 0x101eb1 2 1 5) := {
      pre := (fun s ↦ s.RIP = 0x101eb1)
      code := codeRange 0x101eb1 [0x1, 0xe9]
      step := add_r32_r32_effect_step 0x101eb1 0xe9 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eb1 2 (by decide +kernel)
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
  have h10 : RunWords 0x101eb3 0x101eb6 [.rol (.reg 0) 9] := by
    let ex : InstructionExecution 0x101eb3 0x101eb6 (rolR32Effect 0x101eb3 3 0 9) := {
      pre := (fun s ↦ s.RIP = 0x101eb3)
      code := codeRange 0x101eb3 [0xc1, 0xc0, 0x9]
      step := rol_r32_imm8_effect_step 0x101eb3 0xc0 0x9 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eb3 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 9) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101eb6 0x101eb9 [.add (.reg 0) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101eb6 0x101eb9 (addR32R32Effect 0x101eb6 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x101eb6)
      code := codeRange 0x101eb6 [0x44, 0x1, 0xe0]
      step := add_r32_r32_rex_effect_step 0x101eb6 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eb6 3 (by decide +kernel)
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
  simpa only [segment18, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment19_runs [Bindings] :
    RunWords 0x101eb9 0x101eda segment19 := by
  have h1 : RunWords 0x101eb9 0x101ebc [.mov (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101eb9 0x101ebc (movR32R32Effect 0x101eb9 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x101eb9)
      code := codeRange 0x101eb9 [0x41, 0x89, 0xc7]
      step := mov_r32_r32_rex_effect_step 0x101eb9 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eb9 3 (by decide +kernel)
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
  have h2 : RunWords 0x101ebc 0x101ebf [.and (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101ebc 0x101ebf (andR32R32Effect 0x101ebc 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x101ebc)
      code := codeRange 0x101ebc [0x41, 0x21, 0xd7]
      step := and_r32_r32_rex_effect_step 0x101ebc 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ebc 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101ebf 0x101ec2 [.add (.reg 1) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101ebf 0x101ec2 (addR32R32Effect 0x101ebf 3 1 15) := {
      pre := (fun s ↦ s.RIP = 0x101ebf)
      code := codeRange 0x101ebf [0x44, 0x1, 0xf9]
      step := add_r32_r32_rex_effect_step 0x101ebf 0x44 0xf9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ebf 3 (by decide +kernel)
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
  have h4 : RunWords 0x101ec2 0x101ec8 [.add (.reg 1) (.immediate 0x265e5a51)] := by
    let ex : InstructionExecution 0x101ec2 0x101ec8 (addR32Imm32Effect 0x101ec2 6 1 0x265e5a51) := {
      pre := (fun s ↦ s.RIP = 0x101ec2)
      code := codeRange 0x101ec2 [0x81, 0xc1, 0x51, 0x5a, 0x5e, 0x26]
      step := add_r32_imm32_effect_step 0x101ec2 0xc1 0x265e5a51 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ec2 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0x265e5a51)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101ec8 0x101ecb [.rol (.reg 1) 14] := by
    let ex : InstructionExecution 0x101ec8 0x101ecb (rolR32Effect 0x101ec8 3 1 14) := {
      pre := (fun s ↦ s.RIP = 0x101ec8)
      code := codeRange 0x101ec8 [0xc1, 0xc1, 0xe]
      step := rol_r32_imm8_effect_step 0x101ec8 0xc1 0xe (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ec8 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 14) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101ecb 0x101ece [.mov (.reg 5) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101ecb 0x101ece (movR32R32Effect 0x101ecb 3 5 12) := {
      pre := (fun s ↦ s.RIP = 0x101ecb)
      code := codeRange 0x101ecb [0x44, 0x89, 0xe5]
      step := mov_r32_r32_rex_effect_step 0x101ecb 0x44 0xe5 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ecb 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 5) (.location (.reg 12))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101ece 0x101ed0 [.not (.reg 5)] := by
    let ex : InstructionExecution 0x101ece 0x101ed0 (notR32Effect 0x101ece 2 5) := {
      pre := (fun s ↦ s.RIP = 0x101ece)
      code := codeRange 0x101ece [0xf7, 0xd5]
      step := not_r32_effect_step 0x101ece 0xd5 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ece 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 5)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101ed0 0x101ed2 [.and (.reg 5) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101ed0 0x101ed2 (andR32R32Effect 0x101ed0 2 5 0) := {
      pre := (fun s ↦ s.RIP = 0x101ed0)
      code := codeRange 0x101ed0 [0x21, 0xc5]
      step := and_r32_r32_effect_step 0x101ed0 0xc5 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ed0 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 5) (.location (.reg 0))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101ed2 0x101ed6 [.add (.reg 2) (.location (.stack 88))] := by
    let ex : InstructionExecution 0x101ed2 0x101ed6 (addR32M32Effect 0x101ed2 4 2 (.sib 4 none 0
      (.d8 0x58))) := {
      pre := (LoadPre 0x101ed2 (fun s ↦ ((.sib 4 none 0 (.d8 0x58)) : AddrMode).addr s (0x101ed2 +
        4)) 4)
      code := codeRange 0x101ed2 [0x3, 0x54, 0x24, 0x58]
      step := add_r32_m32_noRex_effect_step 0x101ed2 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ed2 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 88 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.stack 88))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101ed6 0x101ed8 [.add (.reg 2) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101ed6 0x101ed8 (addR32R32Effect 0x101ed6 2 2 5) := {
      pre := (fun s ↦ s.RIP = 0x101ed6)
      code := codeRange 0x101ed6 [0x1, 0xea]
      step := add_r32_r32_effect_step 0x101ed6 0xea (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ed6 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 5))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101ed8 0x101eda [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101ed8 0x101eda (addR32R32Effect 0x101ed8 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x101ed8)
      code := codeRange 0x101ed8 [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x101ed8 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ed8 2 (by decide +kernel)
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
  simpa only [segment19, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment20_runs [Bindings] :
    RunWords 0x101eda 0x101eff segment20 := by
  have h1 : RunWords 0x101eda 0x101edd [.mov (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101eda 0x101edd (movR32R32Effect 0x101eda 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x101eda)
      code := codeRange 0x101eda [0x41, 0x89, 0xcf]
      step := mov_r32_r32_rex_effect_step 0x101eda 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eda 3 (by decide +kernel)
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
  have h2 : RunWords 0x101edd 0x101ee0 [.and (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101edd 0x101ee0 (andR32R32Effect 0x101edd 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x101edd)
      code := codeRange 0x101edd [0x45, 0x21, 0xe7]
      step := and_r32_r32_rex_effect_step 0x101edd 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1edd 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 12))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101ee0 0x101ee3 [.add (.reg 2) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101ee0 0x101ee3 (addR32R32Effect 0x101ee0 3 2 15) := {
      pre := (fun s ↦ s.RIP = 0x101ee0)
      code := codeRange 0x101ee0 [0x44, 0x1, 0xfa]
      step := add_r32_r32_rex_effect_step 0x101ee0 0x44 0xfa (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ee0 3 (by decide +kernel)
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
  have h4 : RunWords 0x101ee3 0x101ee9 [.add (.reg 2) (.immediate 0xe9b6c7aa)] := by
    let ex : InstructionExecution 0x101ee3 0x101ee9 (addR32Imm32Effect 0x101ee3 6 2 0xe9b6c7aa) := {
      pre := (fun s ↦ s.RIP = 0x101ee3)
      code := codeRange 0x101ee3 [0x81, 0xc2, 0xaa, 0xc7, 0xb6, 0xe9]
      step := add_r32_imm32_effect_step 0x101ee3 0xc2 0xe9b6c7aa (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ee3 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0xe9b6c7aa)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101ee9 0x101eeb [.mov (.reg 5) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101ee9 0x101eeb (movR32R32Effect 0x101ee9 2 5 0) := {
      pre := (fun s ↦ s.RIP = 0x101ee9)
      code := codeRange 0x101ee9 [0x89, 0xc5]
      step := mov_r32_r32_effect_step 0x101ee9 0xc5 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ee9 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 5) (.location (.reg 0))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101eeb 0x101eed [.not (.reg 5)] := by
    let ex : InstructionExecution 0x101eeb 0x101eed (notR32Effect 0x101eeb 2 5) := {
      pre := (fun s ↦ s.RIP = 0x101eeb)
      code := codeRange 0x101eeb [0xf7, 0xd5]
      step := not_r32_effect_step 0x101eeb 0xd5 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eeb 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 5)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101eed 0x101eef [.and (.reg 5) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101eed 0x101eef (andR32R32Effect 0x101eed 2 5 1) := {
      pre := (fun s ↦ s.RIP = 0x101eed)
      code := codeRange 0x101eed [0x21, 0xcd]
      step := and_r32_r32_effect_step 0x101eed 0xcd (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eed 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 5) (.location (.reg 1))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101eef 0x101ef4 [.mov (.reg 3) (.location (.stack 64))] := by
    let ex : InstructionExecution 0x101eef 0x101ef4 (movR64M64Effect 0x101eef 3 (.sib 4 none 0 (.d8
      0x40))) := {
      pre := (LoadPre 0x101eef (fun s ↦ ((.sib 4 none 0 (.d8 0x40)) : AddrMode).addr s (0x101eef +
        5)) 8)
      code := codeRange 0x101eef [0x48, 0x8b, 0x5c, 0x24, 0x40]
      step := mov_r64_m64_effect_step 0x101eef 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8
        0x40)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eef 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 64 8 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 3) (.location (.stack 64))) (dst := 3) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101ef4 0x101ef7 [.add (.reg 12) (.location (.reg 3))] := by
    let ex : InstructionExecution 0x101ef4 0x101ef7 (addR32R32Effect 0x101ef4 3 12 3) := {
      pre := (fun s ↦ s.RIP = 0x101ef4)
      code := codeRange 0x101ef4 [0x41, 0x1, 0xdc]
      step := add_r32_r32_rex_effect_step 0x101ef4 0x41 0xdc (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ef4 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 3))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101ef7 0x101efa [.add (.reg 12) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101ef7 0x101efa (addR32R32Effect 0x101ef7 3 12 5) := {
      pre := (fun s ↦ s.RIP = 0x101ef7)
      code := codeRange 0x101ef7 [0x41, 0x1, 0xec]
      step := add_r32_r32_rex_effect_step 0x101ef7 0x41 0xec (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ef7 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 5))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101efa 0x101efd [.rol (.reg 2) 20] := by
    let ex : InstructionExecution 0x101efa 0x101efd (rolR32Effect 0x101efa 3 2 20) := {
      pre := (fun s ↦ s.RIP = 0x101efa)
      code := codeRange 0x101efa [0xc1, 0xc2, 0x14]
      step := rol_r32_imm8_effect_step 0x101efa 0xc2 0x14 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1efa 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 20) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x101efd 0x101eff [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101efd 0x101eff (addR32R32Effect 0x101efd 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x101efd)
      code := codeRange 0x101efd [0x1, 0xca]
      step := add_r32_r32_effect_step 0x101efd 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x1efd 2 (by decide +kernel)
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
  simpa only [segment20, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12)))))))))))

theorem segment21_runs [Bindings] :
    RunWords 0x101eff 0x101f23 segment21 := by
  have h1 : RunWords 0x101eff 0x101f02 [.mov (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101eff 0x101f02 (movR32R32Effect 0x101eff 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x101eff)
      code := codeRange 0x101eff [0x41, 0x89, 0xd7]
      step := mov_r32_r32_rex_effect_step 0x101eff 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1eff 3 (by decide +kernel)
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
  have h2 : RunWords 0x101f02 0x101f05 [.and (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101f02 0x101f05 (andR32R32Effect 0x101f02 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x101f02)
      code := codeRange 0x101f02 [0x41, 0x21, 0xc7]
      step := and_r32_r32_rex_effect_step 0x101f02 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f02 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101f05 0x101f09 [.lea (.reg 5) (.reg 15) (.reg 12)] := by
    let ex : InstructionExecution 0x101f05 0x101f09 (Register.leaR32Effect 0x101f05 4 5 (.sib 15
      (some 12) 0 .none)) := {
      pre := (fun s ↦ s.RIP = 0x101f05)
      code := codeRange 0x101f05 [0x43, 0x8d, 0x2c, 0x27]
      step := Register.lea_r32_rex_effect_step 0x101f05 0x43 (by simp [RexNoWPrefix]) 5 (.sib 15
        (some 12) 0 .none) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f05 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .lea (.reg 5) (.reg 15) (.reg 12)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x101f09 0x101f0f [.add (.reg 5) (.immediate 0xd62f105d)] := by
    let ex : InstructionExecution 0x101f09 0x101f0f (addR32Imm32Effect 0x101f09 6 5 0xd62f105d) := {
      pre := (fun s ↦ s.RIP = 0x101f09)
      code := codeRange 0x101f09 [0x81, 0xc5, 0x5d, 0x10, 0x2f, 0xd6]
      step := add_r32_imm32_effect_step 0x101f09 0xc5 0xd62f105d (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f09 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.immediate 0xd62f105d)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101f0f 0x101f12 [.mov (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101f0f 0x101f12 (movR32R32Effect 0x101f0f 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x101f0f)
      code := codeRange 0x101f0f [0x41, 0x89, 0xcf]
      step := mov_r32_r32_rex_effect_step 0x101f0f 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f0f 3 (by decide +kernel)
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
  have h6 : RunWords 0x101f12 0x101f15 [.not (.reg 15)] := by
    let ex : InstructionExecution 0x101f12 0x101f15 (notR32Effect 0x101f12 3 15) := {
      pre := (fun s ↦ s.RIP = 0x101f12)
      code := codeRange 0x101f12 [0x41, 0xf7, 0xd7]
      step := not_r32_rex_effect_step 0x101f12 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1f12 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 15)) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101f15 0x101f18 [.and (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101f15 0x101f18 (andR32R32Effect 0x101f15 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x101f15)
      code := codeRange 0x101f15 [0x41, 0x21, 0xd7]
      step := and_r32_r32_rex_effect_step 0x101f15 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f15 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101f18 0x101f1b [.add (.reg 0) (.location (.reg 11))] := by
    let ex : InstructionExecution 0x101f18 0x101f1b (addR32R32Effect 0x101f18 3 0 11) := {
      pre := (fun s ↦ s.RIP = 0x101f18)
      code := codeRange 0x101f18 [0x44, 0x1, 0xd8]
      step := add_r32_r32_rex_effect_step 0x101f18 0x44 0xd8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f18 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 11))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101f1b 0x101f1e [.add (.reg 0) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101f1b 0x101f1e (addR32R32Effect 0x101f1b 3 0 15) := {
      pre := (fun s ↦ s.RIP = 0x101f1b)
      code := codeRange 0x101f1b [0x44, 0x1, 0xf8]
      step := add_r32_r32_rex_effect_step 0x101f1b 0x44 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f1b 3 (by decide +kernel)
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
  have h10 : RunWords 0x101f1e 0x101f21 [.rol (.reg 5) 5] := by
    let ex : InstructionExecution 0x101f1e 0x101f21 (rolR32Effect 0x101f1e 3 5 5) := {
      pre := (fun s ↦ s.RIP = 0x101f1e)
      code := codeRange 0x101f1e [0xc1, 0xc5, 0x5]
      step := rol_r32_imm8_effect_step 0x101f1e 0xc5 0x5 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f1e 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 5) 5) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101f21 0x101f23 [.add (.reg 5) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101f21 0x101f23 (addR32R32Effect 0x101f21 2 5 2) := {
      pre := (fun s ↦ s.RIP = 0x101f21)
      code := codeRange 0x101f21 [0x1, 0xd5]
      step := add_r32_r32_effect_step 0x101f21 0xd5 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f21 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 2))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment21, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment22_runs [Bindings] :
    RunWords 0x101f23 0x101f44 segment22 := by
  have h1 : RunWords 0x101f23 0x101f26 [.mov (.reg 15) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101f23 0x101f26 (movR32R32Effect 0x101f23 3 15 5) := {
      pre := (fun s ↦ s.RIP = 0x101f23)
      code := codeRange 0x101f23 [0x41, 0x89, 0xef]
      step := mov_r32_r32_rex_effect_step 0x101f23 0x41 0xef (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f23 3 (by decide +kernel)
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
  have h2 : RunWords 0x101f26 0x101f29 [.and (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101f26 0x101f29 (andR32R32Effect 0x101f26 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x101f26)
      code := codeRange 0x101f26 [0x41, 0x21, 0xcf]
      step := and_r32_r32_rex_effect_step 0x101f26 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f26 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101f29 0x101f2c [.add (.reg 0) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101f29 0x101f2c (addR32R32Effect 0x101f29 3 0 15) := {
      pre := (fun s ↦ s.RIP = 0x101f29)
      code := codeRange 0x101f29 [0x44, 0x1, 0xf8]
      step := add_r32_r32_rex_effect_step 0x101f29 0x44 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f29 3 (by decide +kernel)
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
  have h4 : RunWords 0x101f2c 0x101f31 [.add (.reg 0) (.immediate 0x2441453)] := by
    let ex : InstructionExecution 0x101f2c 0x101f31 (addR32Imm32Effect 0x101f2c 5 0 0x2441453) := {
      pre := (fun s ↦ s.RIP = 0x101f2c)
      code := codeRange 0x101f2c [0x5, 0x53, 0x14, 0x44, 0x2]
      step := Register.add_eax_imm32_effect_step 0x101f2c 0x2441453
      present := fun hc ↦ program_text_slice hc 0x1f2c 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0x2441453)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101f31 0x101f34 [.mov (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101f31 0x101f34 (movR32R32Effect 0x101f31 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x101f31)
      code := codeRange 0x101f31 [0x41, 0x89, 0xd7]
      step := mov_r32_r32_rex_effect_step 0x101f31 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f31 3 (by decide +kernel)
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
  have h6 : RunWords 0x101f34 0x101f37 [.not (.reg 15)] := by
    let ex : InstructionExecution 0x101f34 0x101f37 (notR32Effect 0x101f34 3 15) := {
      pre := (fun s ↦ s.RIP = 0x101f34)
      code := codeRange 0x101f34 [0x41, 0xf7, 0xd7]
      step := not_r32_rex_effect_step 0x101f34 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1f34 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 15)) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101f37 0x101f3a [.and (.reg 15) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101f37 0x101f3a (andR32R32Effect 0x101f37 3 15 5) := {
      pre := (fun s ↦ s.RIP = 0x101f37)
      code := codeRange 0x101f37 [0x41, 0x21, 0xef]
      step := and_r32_r32_rex_effect_step 0x101f37 0x41 0xef (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f37 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 5))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101f3a 0x101f3c [.add (.reg 1) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101f3a 0x101f3c (addR32R32Effect 0x101f3a 2 1 7) := {
      pre := (fun s ↦ s.RIP = 0x101f3a)
      code := codeRange 0x101f3a [0x1, 0xf9]
      step := add_r32_r32_effect_step 0x101f3a 0xf9 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f3a 2 (by decide +kernel)
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
  have h9 : RunWords 0x101f3c 0x101f3f [.add (.reg 1) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101f3c 0x101f3f (addR32R32Effect 0x101f3c 3 1 15) := {
      pre := (fun s ↦ s.RIP = 0x101f3c)
      code := codeRange 0x101f3c [0x44, 0x1, 0xf9]
      step := add_r32_r32_rex_effect_step 0x101f3c 0x44 0xf9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f3c 3 (by decide +kernel)
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
  have h10 : RunWords 0x101f3f 0x101f42 [.rol (.reg 0) 9] := by
    let ex : InstructionExecution 0x101f3f 0x101f42 (rolR32Effect 0x101f3f 3 0 9) := {
      pre := (fun s ↦ s.RIP = 0x101f3f)
      code := codeRange 0x101f3f [0xc1, 0xc0, 0x9]
      step := rol_r32_imm8_effect_step 0x101f3f 0xc0 0x9 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f3f 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 9) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101f42 0x101f44 [.add (.reg 0) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101f42 0x101f44 (addR32R32Effect 0x101f42 2 0 5) := {
      pre := (fun s ↦ s.RIP = 0x101f42)
      code := codeRange 0x101f42 [0x1, 0xe8]
      step := add_r32_r32_effect_step 0x101f42 0xe8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f42 2 (by decide +kernel)
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
  simpa only [segment22, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment23_runs [Bindings] :
    RunWords 0x101f44 0x101f6a segment23 := by
  have h1 : RunWords 0x101f44 0x101f47 [.mov (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101f44 0x101f47 (movR32R32Effect 0x101f44 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x101f44)
      code := codeRange 0x101f44 [0x41, 0x89, 0xc7]
      step := mov_r32_r32_rex_effect_step 0x101f44 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f44 3 (by decide +kernel)
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
  have h2 : RunWords 0x101f47 0x101f4a [.and (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101f47 0x101f4a (andR32R32Effect 0x101f47 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x101f47)
      code := codeRange 0x101f47 [0x41, 0x21, 0xd7]
      step := and_r32_r32_rex_effect_step 0x101f47 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f47 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101f4a 0x101f4d [.add (.reg 1) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101f4a 0x101f4d (addR32R32Effect 0x101f4a 3 1 15) := {
      pre := (fun s ↦ s.RIP = 0x101f4a)
      code := codeRange 0x101f4a [0x44, 0x1, 0xf9]
      step := add_r32_r32_rex_effect_step 0x101f4a 0x44 0xf9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f4a 3 (by decide +kernel)
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
  have h4 : RunWords 0x101f4d 0x101f53 [.add (.reg 1) (.immediate 0xd8a1e681)] := by
    let ex : InstructionExecution 0x101f4d 0x101f53 (addR32Imm32Effect 0x101f4d 6 1 0xd8a1e681) := {
      pre := (fun s ↦ s.RIP = 0x101f4d)
      code := codeRange 0x101f4d [0x81, 0xc1, 0x81, 0xe6, 0xa1, 0xd8]
      step := add_r32_imm32_effect_step 0x101f4d 0xc1 0xd8a1e681 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f4d 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0xd8a1e681)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101f53 0x101f56 [.rol (.reg 1) 14] := by
    let ex : InstructionExecution 0x101f53 0x101f56 (rolR32Effect 0x101f53 3 1 14) := {
      pre := (fun s ↦ s.RIP = 0x101f53)
      code := codeRange 0x101f53 [0xc1, 0xc1, 0xe]
      step := rol_r32_imm8_effect_step 0x101f53 0xc1 0xe (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f53 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 14) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101f56 0x101f59 [.mov (.reg 15) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101f56 0x101f59 (movR32R32Effect 0x101f56 3 15 5) := {
      pre := (fun s ↦ s.RIP = 0x101f56)
      code := codeRange 0x101f56 [0x41, 0x89, 0xef]
      step := mov_r32_r32_rex_effect_step 0x101f56 0x41 0xef (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f56 3 (by decide +kernel)
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
  have h7 : RunWords 0x101f59 0x101f5c [.not (.reg 15)] := by
    let ex : InstructionExecution 0x101f59 0x101f5c (notR32Effect 0x101f59 3 15) := {
      pre := (fun s ↦ s.RIP = 0x101f59)
      code := codeRange 0x101f59 [0x41, 0xf7, 0xd7]
      step := not_r32_rex_effect_step 0x101f59 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1f59 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 15)) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101f5c 0x101f5f [.and (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101f5c 0x101f5f (andR32R32Effect 0x101f5c 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x101f5c)
      code := codeRange 0x101f5c [0x41, 0x21, 0xc7]
      step := and_r32_r32_rex_effect_step 0x101f5c 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f5c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101f5f 0x101f63 [.mov (.reg 7) (.location (.stack 28))] := by
    let ex : InstructionExecution 0x101f5f 0x101f63 (movR32M32NoRexEffect 0x101f5f 7 (.sib 4 none 0
      (.d8 0x1c))) := {
      pre := (LoadPre 0x101f5f (fun s ↦ ((.sib 4 none 0 (.d8 0x1c)) : AddrMode).addr s (0x101f5f +
        4)) 4)
      code := codeRange 0x101f5f [0x8b, 0x7c, 0x24, 0x1c]
      step := mov_r32_m32_noRex_effect_step 0x101f5f 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f5f 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 28 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 7) (.location (.stack 28))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101f63 0x101f65 [.add (.reg 2) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101f63 0x101f65 (addR32R32Effect 0x101f63 2 2 7) := {
      pre := (fun s ↦ s.RIP = 0x101f63)
      code := codeRange 0x101f63 [0x1, 0xfa]
      step := add_r32_r32_effect_step 0x101f63 0xfa (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f63 2 (by decide +kernel)
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
  have h11 : RunWords 0x101f65 0x101f68 [.add (.reg 2) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101f65 0x101f68 (addR32R32Effect 0x101f65 3 2 15) := {
      pre := (fun s ↦ s.RIP = 0x101f65)
      code := codeRange 0x101f65 [0x44, 0x1, 0xfa]
      step := add_r32_r32_rex_effect_step 0x101f65 0x44 0xfa (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f65 3 (by decide +kernel)
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
  have h12 : RunWords 0x101f68 0x101f6a [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101f68 0x101f6a (addR32R32Effect 0x101f68 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x101f68)
      code := codeRange 0x101f68 [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x101f68 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f68 2 (by decide +kernel)
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
  simpa only [segment23, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12)))))))))))

theorem segment24_runs [Bindings] :
    RunWords 0x101f6a 0x101f8e segment24 := by
  have h1 : RunWords 0x101f6a 0x101f6d [.mov (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101f6a 0x101f6d (movR32R32Effect 0x101f6a 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x101f6a)
      code := codeRange 0x101f6a [0x41, 0x89, 0xcf]
      step := mov_r32_r32_rex_effect_step 0x101f6a 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f6a 3 (by decide +kernel)
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
  have h2 : RunWords 0x101f6d 0x101f70 [.and (.reg 15) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101f6d 0x101f70 (andR32R32Effect 0x101f6d 3 15 5) := {
      pre := (fun s ↦ s.RIP = 0x101f6d)
      code := codeRange 0x101f6d [0x41, 0x21, 0xef]
      step := and_r32_r32_rex_effect_step 0x101f6d 0x41 0xef (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f6d 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 5))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101f70 0x101f73 [.add (.reg 2) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101f70 0x101f73 (addR32R32Effect 0x101f70 3 2 15) := {
      pre := (fun s ↦ s.RIP = 0x101f70)
      code := codeRange 0x101f70 [0x44, 0x1, 0xfa]
      step := add_r32_r32_rex_effect_step 0x101f70 0x44 0xfa (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f70 3 (by decide +kernel)
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
  have h4 : RunWords 0x101f73 0x101f79 [.add (.reg 2) (.immediate 0xe7d3fbc8)] := by
    let ex : InstructionExecution 0x101f73 0x101f79 (addR32Imm32Effect 0x101f73 6 2 0xe7d3fbc8) := {
      pre := (fun s ↦ s.RIP = 0x101f73)
      code := codeRange 0x101f73 [0x81, 0xc2, 0xc8, 0xfb, 0xd3, 0xe7]
      step := add_r32_imm32_effect_step 0x101f73 0xc2 0xe7d3fbc8 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f73 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0xe7d3fbc8)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101f79 0x101f7c [.mov (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101f79 0x101f7c (movR32R32Effect 0x101f79 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x101f79)
      code := codeRange 0x101f79 [0x41, 0x89, 0xc7]
      step := mov_r32_r32_rex_effect_step 0x101f79 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f79 3 (by decide +kernel)
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
  have h6 : RunWords 0x101f7c 0x101f7f [.not (.reg 15)] := by
    let ex : InstructionExecution 0x101f7c 0x101f7f (notR32Effect 0x101f7c 3 15) := {
      pre := (fun s ↦ s.RIP = 0x101f7c)
      code := codeRange 0x101f7c [0x41, 0xf7, 0xd7]
      step := not_r32_rex_effect_step 0x101f7c 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1f7c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 15)) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101f7f 0x101f82 [.and (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101f7f 0x101f82 (andR32R32Effect 0x101f7f 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x101f7f)
      code := codeRange 0x101f7f [0x41, 0x21, 0xcf]
      step := and_r32_r32_rex_effect_step 0x101f7f 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f7f 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101f82 0x101f86 [.add (.reg 5) (.location (.stack 4))] := by
    let ex : InstructionExecution 0x101f82 0x101f86 (addR32M32Effect 0x101f82 4 5 (.sib 4 none 0
      (.d8 0x4))) := {
      pre := (LoadPre 0x101f82 (fun s ↦ ((.sib 4 none 0 (.d8 0x4)) : AddrMode).addr s (0x101f82 +
        4)) 4)
      code := codeRange 0x101f82 [0x3, 0x6c, 0x24, 0x4]
      step := add_r32_m32_noRex_effect_step 0x101f82 5 (.sib 4 none 0 (.d8 0x4)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f82 4 (by decide +kernel)
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
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.stack 4))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101f86 0x101f89 [.add (.reg 5) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101f86 0x101f89 (addR32R32Effect 0x101f86 3 5 15) := {
      pre := (fun s ↦ s.RIP = 0x101f86)
      code := codeRange 0x101f86 [0x44, 0x1, 0xfd]
      step := add_r32_r32_rex_effect_step 0x101f86 0x44 0xfd (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f86 3 (by decide +kernel)
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
  have h10 : RunWords 0x101f89 0x101f8c [.rol (.reg 2) 20] := by
    let ex : InstructionExecution 0x101f89 0x101f8c (rolR32Effect 0x101f89 3 2 20) := {
      pre := (fun s ↦ s.RIP = 0x101f89)
      code := codeRange 0x101f89 [0xc1, 0xc2, 0x14]
      step := rol_r32_imm8_effect_step 0x101f89 0xc2 0x14 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f89 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 20) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101f8c 0x101f8e [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101f8c 0x101f8e (addR32R32Effect 0x101f8c 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x101f8c)
      code := codeRange 0x101f8c [0x1, 0xca]
      step := add_r32_r32_effect_step 0x101f8c 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f8c 2 (by decide +kernel)
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
  simpa only [segment24, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment25_runs [Bindings] :
    RunWords 0x101f8e 0x101fb1 segment25 := by
  have h1 : RunWords 0x101f8e 0x101f91 [.mov (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101f8e 0x101f91 (movR32R32Effect 0x101f8e 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x101f8e)
      code := codeRange 0x101f8e [0x41, 0x89, 0xd7]
      step := mov_r32_r32_rex_effect_step 0x101f8e 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f8e 3 (by decide +kernel)
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
  have h2 : RunWords 0x101f91 0x101f94 [.and (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101f91 0x101f94 (andR32R32Effect 0x101f91 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x101f91)
      code := codeRange 0x101f91 [0x41, 0x21, 0xc7]
      step := and_r32_r32_rex_effect_step 0x101f91 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f91 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101f94 0x101f97 [.add (.reg 5) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101f94 0x101f97 (addR32R32Effect 0x101f94 3 5 15) := {
      pre := (fun s ↦ s.RIP = 0x101f94)
      code := codeRange 0x101f94 [0x44, 0x1, 0xfd]
      step := add_r32_r32_rex_effect_step 0x101f94 0x44 0xfd (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f94 3 (by decide +kernel)
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
  have h4 : RunWords 0x101f97 0x101f9d [.add (.reg 5) (.immediate 0x21e1cde6)] := by
    let ex : InstructionExecution 0x101f97 0x101f9d (addR32Imm32Effect 0x101f97 6 5 0x21e1cde6) := {
      pre := (fun s ↦ s.RIP = 0x101f97)
      code := codeRange 0x101f97 [0x81, 0xc5, 0xe6, 0xcd, 0xe1, 0x21]
      step := add_r32_imm32_effect_step 0x101f97 0xc5 0x21e1cde6 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f97 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.immediate 0x21e1cde6)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101f9d 0x101fa0 [.mov (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101f9d 0x101fa0 (movR32R32Effect 0x101f9d 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x101f9d)
      code := codeRange 0x101f9d [0x41, 0x89, 0xcf]
      step := mov_r32_r32_rex_effect_step 0x101f9d 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1f9d 3 (by decide +kernel)
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
  have h6 : RunWords 0x101fa0 0x101fa3 [.not (.reg 15)] := by
    let ex : InstructionExecution 0x101fa0 0x101fa3 (notR32Effect 0x101fa0 3 15) := {
      pre := (fun s ↦ s.RIP = 0x101fa0)
      code := codeRange 0x101fa0 [0x41, 0xf7, 0xd7]
      step := not_r32_rex_effect_step 0x101fa0 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1fa0 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 15)) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101fa3 0x101fa6 [.and (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101fa3 0x101fa6 (andR32R32Effect 0x101fa3 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x101fa3)
      code := codeRange 0x101fa3 [0x41, 0x21, 0xd7]
      step := and_r32_r32_rex_effect_step 0x101fa3 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fa3 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 2))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101fa6 0x101fa9 [.add (.reg 0) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101fa6 0x101fa9 (addR32R32Effect 0x101fa6 3 0 8) := {
      pre := (fun s ↦ s.RIP = 0x101fa6)
      code := codeRange 0x101fa6 [0x44, 0x1, 0xc0]
      step := add_r32_r32_rex_effect_step 0x101fa6 0x44 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fa6 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 8))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101fa9 0x101fac [.add (.reg 0) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101fa9 0x101fac (addR32R32Effect 0x101fa9 3 0 15) := {
      pre := (fun s ↦ s.RIP = 0x101fa9)
      code := codeRange 0x101fa9 [0x44, 0x1, 0xf8]
      step := add_r32_r32_rex_effect_step 0x101fa9 0x44 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fa9 3 (by decide +kernel)
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
  have h10 : RunWords 0x101fac 0x101faf [.rol (.reg 5) 5] := by
    let ex : InstructionExecution 0x101fac 0x101faf (rolR32Effect 0x101fac 3 5 5) := {
      pre := (fun s ↦ s.RIP = 0x101fac)
      code := codeRange 0x101fac [0xc1, 0xc5, 0x5]
      step := rol_r32_imm8_effect_step 0x101fac 0xc5 0x5 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fac 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 5) 5) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101faf 0x101fb1 [.add (.reg 5) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101faf 0x101fb1 (addR32R32Effect 0x101faf 2 5 2) := {
      pre := (fun s ↦ s.RIP = 0x101faf)
      code := codeRange 0x101faf [0x1, 0xd5]
      step := add_r32_r32_effect_step 0x101faf 0xd5 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1faf 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 2))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment25, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment26_runs [Bindings] :
    RunWords 0x101fb1 0x101fd9 segment26 := by
  have h1 : RunWords 0x101fb1 0x101fb4 [.mov (.reg 15) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101fb1 0x101fb4 (movR32R32Effect 0x101fb1 3 15 5) := {
      pre := (fun s ↦ s.RIP = 0x101fb1)
      code := codeRange 0x101fb1 [0x41, 0x89, 0xef]
      step := mov_r32_r32_rex_effect_step 0x101fb1 0x41 0xef (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fb1 3 (by decide +kernel)
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
  have h2 : RunWords 0x101fb4 0x101fb7 [.and (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101fb4 0x101fb7 (andR32R32Effect 0x101fb4 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x101fb4)
      code := codeRange 0x101fb4 [0x41, 0x21, 0xcf]
      step := and_r32_r32_rex_effect_step 0x101fb4 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fb4 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 1))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101fb7 0x101fbb [.lea (.reg 12) (.reg 15) (.reg 0)] := by
    let ex : InstructionExecution 0x101fb7 0x101fbb (Register.leaR32Effect 0x101fb7 4 12 (.sib 15
      (some 0) 0 .none)) := {
      pre := (fun s ↦ s.RIP = 0x101fb7)
      code := codeRange 0x101fb7 [0x45, 0x8d, 0x24, 0x7]
      step := Register.lea_r32_rex_effect_step 0x101fb7 0x45 (by simp [RexNoWPrefix]) 4 (.sib 15
        (some 0) 0 .none) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fb7 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .lea (.reg 12) (.reg 15) (.reg 0)) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x101fbb 0x101fc2 [.add (.reg 12) (.immediate 0xc33707d6)] := by
    let ex : InstructionExecution 0x101fbb 0x101fc2 (addR32Imm32Effect 0x101fbb 7 12 0xc33707d6) :=
      {
      pre := (fun s ↦ s.RIP = 0x101fbb)
      code := codeRange 0x101fbb [0x41, 0x81, 0xc4, 0xd6, 0x7, 0x37, 0xc3]
      step := add_r32_imm32_rex_effect_step 0x101fbb 0x41 0xc4 0xc33707d6 (by simp [RexNoWPrefix])
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fbb 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.immediate 0xc33707d6)) (dst := 12) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101fc2 0x101fc4 [.mov (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101fc2 0x101fc4 (movR32R32Effect 0x101fc2 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x101fc2)
      code := codeRange 0x101fc2 [0x89, 0xd0]
      step := mov_r32_r32_effect_step 0x101fc2 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fc2 2 (by decide +kernel)
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
  have h6 : RunWords 0x101fc4 0x101fc6 [.not (.reg 0)] := by
    let ex : InstructionExecution 0x101fc4 0x101fc6 (notR32Effect 0x101fc4 2 0) := {
      pre := (fun s ↦ s.RIP = 0x101fc4)
      code := codeRange 0x101fc4 [0xf7, 0xd0]
      step := not_r32_effect_step 0x101fc4 0xd0 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fc4 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 0)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101fc6 0x101fc8 [.and (.reg 0) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101fc6 0x101fc8 (andR32R32Effect 0x101fc6 2 0 5) := {
      pre := (fun s ↦ s.RIP = 0x101fc6)
      code := codeRange 0x101fc6 [0x21, 0xe8]
      step := and_r32_r32_effect_step 0x101fc6 0xe8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fc6 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 0) (.location (.reg 5))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101fc8 0x101fcd [.mov (.reg 9) (.location (.stack 72))] := by
    let ex : InstructionExecution 0x101fc8 0x101fcd (movR64M64Effect 0x101fc8 9 (.sib 4 none 0 (.d8
      0x48))) := {
      pre := (LoadPre 0x101fc8 (fun s ↦ ((.sib 4 none 0 (.d8 0x48)) : AddrMode).addr s (0x101fc8 +
        5)) 8)
      code := codeRange 0x101fc8 [0x4c, 0x8b, 0x4c, 0x24, 0x48]
      step := mov_r64_m64_effect_step 0x101fc8 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8
        0x48)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fc8 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 72 8 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 9) (.location (.stack 72))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101fcd 0x101fd0 [.add (.reg 1) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x101fcd 0x101fd0 (addR32R32Effect 0x101fcd 3 1 9) := {
      pre := (fun s ↦ s.RIP = 0x101fcd)
      code := codeRange 0x101fcd [0x44, 0x1, 0xc9]
      step := add_r32_r32_rex_effect_step 0x101fcd 0x44 0xc9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fcd 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 9))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101fd0 0x101fd2 [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101fd0 0x101fd2 (addR32R32Effect 0x101fd0 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x101fd0)
      code := codeRange 0x101fd0 [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x101fd0 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fd0 2 (by decide +kernel)
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
  have h11 : RunWords 0x101fd2 0x101fd6 [.rol (.reg 12) 9] := by
    let ex : InstructionExecution 0x101fd2 0x101fd6 (rolR32Effect 0x101fd2 4 12 9) := {
      pre := (fun s ↦ s.RIP = 0x101fd2)
      code := codeRange 0x101fd2 [0x41, 0xc1, 0xc4, 0x9]
      step := rol_r32_imm8_rex_effect_step 0x101fd2 0x41 0xc4 0x9 (by simp [RexNoWPrefix]) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fd2 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 12) 9) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x101fd6 0x101fd9 [.add (.reg 12) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101fd6 0x101fd9 (addR32R32Effect 0x101fd6 3 12 5) := {
      pre := (fun s ↦ s.RIP = 0x101fd6)
      code := codeRange 0x101fd6 [0x41, 0x1, 0xec]
      step := add_r32_r32_rex_effect_step 0x101fd6 0x41 0xec (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fd6 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 5))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment26, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12)))))))))))

theorem segment27_runs [Bindings] :
    RunWords 0x101fd9 0x101ffd segment27 := by
  have h1 : RunWords 0x101fd9 0x101fdc [.mov (.reg 0) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101fd9 0x101fdc (movR32R32Effect 0x101fd9 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x101fd9)
      code := codeRange 0x101fd9 [0x44, 0x89, 0xe0]
      step := mov_r32_r32_rex_effect_step 0x101fd9 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fd9 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 0) (.location (.reg 12))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x101fdc 0x101fde [.and (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101fdc 0x101fde (andR32R32Effect 0x101fdc 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x101fdc)
      code := codeRange 0x101fdc [0x21, 0xd0]
      step := and_r32_r32_effect_step 0x101fdc 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fdc 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 0) (.location (.reg 2))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101fde 0x101fe0 [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101fde 0x101fe0 (addR32R32Effect 0x101fde 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x101fde)
      code := codeRange 0x101fde [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x101fde 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fde 2 (by decide +kernel)
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
  have h4 : RunWords 0x101fe0 0x101fe6 [.add (.reg 1) (.immediate 0xf4d50d87)] := by
    let ex : InstructionExecution 0x101fe0 0x101fe6 (addR32Imm32Effect 0x101fe0 6 1 0xf4d50d87) := {
      pre := (fun s ↦ s.RIP = 0x101fe0)
      code := codeRange 0x101fe0 [0x81, 0xc1, 0x87, 0xd, 0xd5, 0xf4]
      step := add_r32_imm32_effect_step 0x101fe0 0xc1 0xf4d50d87 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fe0 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0xf4d50d87)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101fe6 0x101fe9 [.rol (.reg 1) 14] := by
    let ex : InstructionExecution 0x101fe6 0x101fe9 (rolR32Effect 0x101fe6 3 1 14) := {
      pre := (fun s ↦ s.RIP = 0x101fe6)
      code := codeRange 0x101fe6 [0xc1, 0xc1, 0xe]
      step := rol_r32_imm8_effect_step 0x101fe6 0xc1 0xe (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fe6 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 14) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101fe9 0x101feb [.mov (.reg 0) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101fe9 0x101feb (movR32R32Effect 0x101fe9 2 0 5) := {
      pre := (fun s ↦ s.RIP = 0x101fe9)
      code := codeRange 0x101fe9 [0x89, 0xe8]
      step := mov_r32_r32_effect_step 0x101fe9 0xe8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fe9 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 0) (.location (.reg 5))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101feb 0x101fed [.not (.reg 0)] := by
    let ex : InstructionExecution 0x101feb 0x101fed (notR32Effect 0x101feb 2 0) := {
      pre := (fun s ↦ s.RIP = 0x101feb)
      code := codeRange 0x101feb [0xf7, 0xd0]
      step := not_r32_effect_step 0x101feb 0xd0 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1feb 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 0)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101fed 0x101ff0 [.and (.reg 0) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101fed 0x101ff0 (andR32R32Effect 0x101fed 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x101fed)
      code := codeRange 0x101fed [0x44, 0x21, 0xe0]
      step := and_r32_r32_rex_effect_step 0x101fed 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fed 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 0) (.location (.reg 12))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101ff0 0x101ff5 [.mov (.reg 14) (.location (.stack 24))] := by
    let ex : InstructionExecution 0x101ff0 0x101ff5 (movR32M32Effect 0x101ff0 14 (.sib 4 none 0 (.d8
      0x18))) := {
      pre := (LoadPre 0x101ff0 (fun s ↦ ((.sib 4 none 0 (.d8 0x18)) : AddrMode).addr s (0x101ff0 +
        5)) 4)
      code := codeRange 0x101ff0 [0x44, 0x8b, 0x74, 0x24, 0x18]
      step := mov_r32_m32_effect_step 0x101ff0 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8
        0x18)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ff0 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 24 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 14) (.location (.stack 24))) (dst := 14) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101ff5 0x101ff8 [.add (.reg 2) (.location (.reg 14))] := by
    let ex : InstructionExecution 0x101ff5 0x101ff8 (addR32R32Effect 0x101ff5 3 2 14) := {
      pre := (fun s ↦ s.RIP = 0x101ff5)
      code := codeRange 0x101ff5 [0x44, 0x1, 0xf2]
      step := add_r32_r32_rex_effect_step 0x101ff5 0x44 0xf2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ff5 3 (by decide +kernel)
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
  have h11 : RunWords 0x101ff8 0x101ffa [.add (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101ff8 0x101ffa (addR32R32Effect 0x101ff8 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x101ff8)
      code := codeRange 0x101ff8 [0x1, 0xc2]
      step := add_r32_r32_effect_step 0x101ff8 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ff8 2 (by decide +kernel)
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
  have h12 : RunWords 0x101ffa 0x101ffd [.add (.reg 1) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101ffa 0x101ffd (addR32R32Effect 0x101ffa 3 1 12) := {
      pre := (fun s ↦ s.RIP = 0x101ffa)
      code := codeRange 0x101ffa [0x44, 0x1, 0xe1]
      step := add_r32_r32_rex_effect_step 0x101ffa 0x44 0xe1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ffa 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 12))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment27, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12)))))))))))

theorem segment28_runs [Bindings] :
    RunWords 0x101ffd 0x10201e segment28 := by
  have h1 : RunWords 0x101ffd 0x101fff [.mov (.reg 0) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101ffd 0x101fff (movR32R32Effect 0x101ffd 2 0 1) := {
      pre := (fun s ↦ s.RIP = 0x101ffd)
      code := codeRange 0x101ffd [0x89, 0xc8]
      step := mov_r32_r32_effect_step 0x101ffd 0xc8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ffd 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 0) (.location (.reg 1))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x101fff 0x102001 [.and (.reg 0) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101fff 0x102001 (andR32R32Effect 0x101fff 2 0 5) := {
      pre := (fun s ↦ s.RIP = 0x101fff)
      code := codeRange 0x101fff [0x21, 0xe8]
      step := and_r32_r32_effect_step 0x101fff 0xe8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1fff 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 0) (.location (.reg 5))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102001 0x102003 [.add (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102001 0x102003 (addR32R32Effect 0x102001 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x102001)
      code := codeRange 0x102001 [0x1, 0xd0]
      step := add_r32_r32_effect_step 0x102001 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2001 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 2))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102003 0x102008 [.add (.reg 0) (.immediate 0x455a14ed)] := by
    let ex : InstructionExecution 0x102003 0x102008 (addR32Imm32Effect 0x102003 5 0 0x455a14ed) := {
      pre := (fun s ↦ s.RIP = 0x102003)
      code := codeRange 0x102003 [0x5, 0xed, 0x14, 0x5a, 0x45]
      step := Register.add_eax_imm32_effect_step 0x102003 0x455a14ed
      present := fun hc ↦ program_text_slice hc 0x2003 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0x455a14ed)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102008 0x10200b [.mov (.reg 2) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x102008 0x10200b (movR32R32Effect 0x102008 3 2 12) := {
      pre := (fun s ↦ s.RIP = 0x102008)
      code := codeRange 0x102008 [0x44, 0x89, 0xe2]
      step := mov_r32_r32_rex_effect_step 0x102008 0x44 0xe2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2008 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 2) (.location (.reg 12))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x10200b 0x10200d [.not (.reg 2)] := by
    let ex : InstructionExecution 0x10200b 0x10200d (notR32Effect 0x10200b 2 2) := {
      pre := (fun s ↦ s.RIP = 0x10200b)
      code := codeRange 0x10200b [0xf7, 0xd2]
      step := not_r32_effect_step 0x10200b 0xd2 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x200b 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 2)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x10200d 0x10200f [.and (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x10200d 0x10200f (andR32R32Effect 0x10200d 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x10200d)
      code := codeRange 0x10200d [0x21, 0xca]
      step := and_r32_r32_effect_step 0x10200d 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x200d 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 2) (.location (.reg 1))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x10200f 0x102014 [.mov (.reg 10) (.location (.stack 20))] := by
    let ex : InstructionExecution 0x10200f 0x102014 (movR32M32Effect 0x10200f 10 (.sib 4 none 0 (.d8
      0x14))) := {
      pre := (LoadPre 0x10200f (fun s ↦ ((.sib 4 none 0 (.d8 0x14)) : AddrMode).addr s (0x10200f +
        5)) 4)
      code := codeRange 0x10200f [0x44, 0x8b, 0x54, 0x24, 0x14]
      step := mov_r32_m32_effect_step 0x10200f 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8
        0x14)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x200f 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 20 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.stack 20))) (dst := 10) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x102014 0x102017 [.add (.reg 5) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x102014 0x102017 (addR32R32Effect 0x102014 3 5 10) := {
      pre := (fun s ↦ s.RIP = 0x102014)
      code := codeRange 0x102014 [0x44, 0x1, 0xd5]
      step := add_r32_r32_rex_effect_step 0x102014 0x44 0xd5 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2014 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 10))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x102017 0x102019 [.add (.reg 5) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102017 0x102019 (addR32R32Effect 0x102017 2 5 2) := {
      pre := (fun s ↦ s.RIP = 0x102017)
      code := codeRange 0x102017 [0x1, 0xd5]
      step := add_r32_r32_effect_step 0x102017 0xd5 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2017 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 2))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x102019 0x10201c [.rol (.reg 0) 20] := by
    let ex : InstructionExecution 0x102019 0x10201c (rolR32Effect 0x102019 3 0 20) := {
      pre := (fun s ↦ s.RIP = 0x102019)
      code := codeRange 0x102019 [0xc1, 0xc0, 0x14]
      step := rol_r32_imm8_effect_step 0x102019 0xc0 0x14 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2019 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 20) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x10201c 0x10201e [.add (.reg 0) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x10201c 0x10201e (addR32R32Effect 0x10201c 2 0 1) := {
      pre := (fun s ↦ s.RIP = 0x10201c)
      code := codeRange 0x10201c [0x1, 0xc8]
      step := add_r32_r32_effect_step 0x10201c 0xc8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x201c 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 1))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment28, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12)))))))))))

theorem segment29_runs [Bindings] :
    RunWords 0x10201e 0x102041 segment29 := by
  have h1 : RunWords 0x10201e 0x102020 [.mov (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x10201e 0x102020 (movR32R32Effect 0x10201e 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x10201e)
      code := codeRange 0x10201e [0x89, 0xc2]
      step := mov_r32_r32_effect_step 0x10201e 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x201e 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 2) (.location (.reg 0))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x102020 0x102023 [.and (.reg 2) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x102020 0x102023 (andR32R32Effect 0x102020 3 2 12) := {
      pre := (fun s ↦ s.RIP = 0x102020)
      code := codeRange 0x102020 [0x44, 0x21, 0xe2]
      step := and_r32_r32_rex_effect_step 0x102020 0x44 0xe2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2020 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 2) (.location (.reg 12))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102023 0x102025 [.add (.reg 5) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102023 0x102025 (addR32R32Effect 0x102023 2 5 2) := {
      pre := (fun s ↦ s.RIP = 0x102023)
      code := codeRange 0x102023 [0x1, 0xd5]
      step := add_r32_r32_effect_step 0x102023 0xd5 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2023 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 2))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102025 0x10202b [.add (.reg 5) (.immediate 0xa9e3e905)] := by
    let ex : InstructionExecution 0x102025 0x10202b (addR32Imm32Effect 0x102025 6 5 0xa9e3e905) := {
      pre := (fun s ↦ s.RIP = 0x102025)
      code := codeRange 0x102025 [0x81, 0xc5, 0x5, 0xe9, 0xe3, 0xa9]
      step := add_r32_imm32_effect_step 0x102025 0xc5 0xa9e3e905 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2025 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.immediate 0xa9e3e905)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x10202b 0x10202d [.mov (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x10202b 0x10202d (movR32R32Effect 0x10202b 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x10202b)
      code := codeRange 0x10202b [0x89, 0xca]
      step := mov_r32_r32_effect_step 0x10202b 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x202b 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 2) (.location (.reg 1))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x10202d 0x10202f [.not (.reg 2)] := by
    let ex : InstructionExecution 0x10202d 0x10202f (notR32Effect 0x10202d 2 2) := {
      pre := (fun s ↦ s.RIP = 0x10202d)
      code := codeRange 0x10202d [0xf7, 0xd2]
      step := not_r32_effect_step 0x10202d 0xd2 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x202d 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 2)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x10202f 0x102031 [.and (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x10202f 0x102031 (andR32R32Effect 0x10202f 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x10202f)
      code := codeRange 0x10202f [0x21, 0xc2]
      step := and_r32_r32_effect_step 0x10202f 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x202f 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 2) (.location (.reg 0))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x102031 0x102036 [.mov (.reg 13) (.location (.stack 112))] := by
    let ex : InstructionExecution 0x102031 0x102036 (movR64M64Effect 0x102031 13 (.sib 4 none 0 (.d8
      0x70))) := {
      pre := (LoadPre 0x102031 (fun s ↦ ((.sib 4 none 0 (.d8 0x70)) : AddrMode).addr s (0x102031 +
        5)) 8)
      code := codeRange 0x102031 [0x4c, 0x8b, 0x6c, 0x24, 0x70]
      step := mov_r64_m64_effect_step 0x102031 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8
        0x70)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2031 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 112 8 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 13) (.location (.stack 112))) (dst := 13) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x102036 0x102039 [.add (.reg 12) (.location (.reg 13))] := by
    let ex : InstructionExecution 0x102036 0x102039 (addR32R32Effect 0x102036 3 12 13) := {
      pre := (fun s ↦ s.RIP = 0x102036)
      code := codeRange 0x102036 [0x45, 0x1, 0xec]
      step := add_r32_r32_rex_effect_step 0x102036 0x45 0xec (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2036 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.location (.reg 13))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x102039 0x10203c [.add (.reg 12) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102039 0x10203c (addR32R32Effect 0x102039 3 12 2) := {
      pre := (fun s ↦ s.RIP = 0x102039)
      code := codeRange 0x102039 [0x41, 0x1, 0xd4]
      step := add_r32_r32_rex_effect_step 0x102039 0x41 0xd4 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2039 3 (by decide +kernel)
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
  have h11 : RunWords 0x10203c 0x10203f [.rol (.reg 5) 5] := by
    let ex : InstructionExecution 0x10203c 0x10203f (rolR32Effect 0x10203c 3 5 5) := {
      pre := (fun s ↦ s.RIP = 0x10203c)
      code := codeRange 0x10203c [0xc1, 0xc5, 0x5]
      step := rol_r32_imm8_effect_step 0x10203c 0xc5 0x5 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x203c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 5) 5) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x10203f 0x102041 [.add (.reg 5) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x10203f 0x102041 (addR32R32Effect 0x10203f 2 5 0) := {
      pre := (fun s ↦ s.RIP = 0x10203f)
      code := codeRange 0x10203f [0x1, 0xc5]
      step := add_r32_r32_effect_step 0x10203f 0xc5 (by decide)
      present := fun hc ↦ program_text_slice hc 0x203f 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 0))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment29, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12)))))))))))

theorem segment30_runs [Bindings] :
    RunWords 0x102041 0x102067 segment30 := by
  have h1 : RunWords 0x102041 0x102043 [.mov (.reg 2) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x102041 0x102043 (movR32R32Effect 0x102041 2 2 5) := {
      pre := (fun s ↦ s.RIP = 0x102041)
      code := codeRange 0x102041 [0x89, 0xea]
      step := mov_r32_r32_effect_step 0x102041 0xea (by decide)
      present := fun hc ↦ program_text_slice hc 0x2041 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 2) (.location (.reg 5))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x102043 0x102045 [.and (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102043 0x102045 (andR32R32Effect 0x102043 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x102043)
      code := codeRange 0x102043 [0x21, 0xca]
      step := and_r32_r32_effect_step 0x102043 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x2043 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 2) (.location (.reg 1))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102045 0x102048 [.add (.reg 2) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x102045 0x102048 (addR32R32Effect 0x102045 3 2 12) := {
      pre := (fun s ↦ s.RIP = 0x102045)
      code := codeRange 0x102045 [0x44, 0x1, 0xe2]
      step := add_r32_r32_rex_effect_step 0x102045 0x44 0xe2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2045 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 12))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102048 0x10204e [.add (.reg 2) (.immediate 0xfcefa3f8)] := by
    let ex : InstructionExecution 0x102048 0x10204e (addR32Imm32Effect 0x102048 6 2 0xfcefa3f8) := {
      pre := (fun s ↦ s.RIP = 0x102048)
      code := codeRange 0x102048 [0x81, 0xc2, 0xf8, 0xa3, 0xef, 0xfc]
      step := add_r32_imm32_effect_step 0x102048 0xc2 0xfcefa3f8 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2048 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0xfcefa3f8)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x10204e 0x102051 [.mov (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x10204e 0x102051 (movR32R32Effect 0x10204e 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x10204e)
      code := codeRange 0x10204e [0x41, 0x89, 0xc7]
      step := mov_r32_r32_rex_effect_step 0x10204e 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x204e 3 (by decide +kernel)
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
  have h6 : RunWords 0x102051 0x102054 [.not (.reg 15)] := by
    let ex : InstructionExecution 0x102051 0x102054 (notR32Effect 0x102051 3 15) := {
      pre := (fun s ↦ s.RIP = 0x102051)
      code := codeRange 0x102051 [0x41, 0xf7, 0xd7]
      step := not_r32_rex_effect_step 0x102051 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x2051 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 15)) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102054 0x102057 [.and (.reg 15) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x102054 0x102057 (andR32R32Effect 0x102054 3 15 5) := {
      pre := (fun s ↦ s.RIP = 0x102054)
      code := codeRange 0x102054 [0x41, 0x21, 0xef]
      step := and_r32_r32_rex_effect_step 0x102054 0x41 0xef (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2054 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 5))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x102057 0x10205c [.mov (.reg 8) (.location (.stack 52))] := by
    let ex : InstructionExecution 0x102057 0x10205c (movR32M32Effect 0x102057 8 (.sib 4 none 0 (.d8
      0x34))) := {
      pre := (LoadPre 0x102057 (fun s ↦ ((.sib 4 none 0 (.d8 0x34)) : AddrMode).addr s (0x102057 +
        5)) 4)
      code := codeRange 0x102057 [0x44, 0x8b, 0x44, 0x24, 0x34]
      step := mov_r32_m32_effect_step 0x102057 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8
        0x34)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2057 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 52 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.stack 52))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x10205c 0x10205f [.add (.reg 1) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x10205c 0x10205f (addR32R32Effect 0x10205c 3 1 8) := {
      pre := (fun s ↦ s.RIP = 0x10205c)
      code := codeRange 0x10205c [0x44, 0x1, 0xc1]
      step := add_r32_r32_rex_effect_step 0x10205c 0x44 0xc1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x205c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 8))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x10205f 0x102062 [.add (.reg 1) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x10205f 0x102062 (addR32R32Effect 0x10205f 3 1 15) := {
      pre := (fun s ↦ s.RIP = 0x10205f)
      code := codeRange 0x10205f [0x44, 0x1, 0xf9]
      step := add_r32_r32_rex_effect_step 0x10205f 0x44 0xf9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x205f 3 (by decide +kernel)
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
  have h11 : RunWords 0x102062 0x102065 [.rol (.reg 2) 9] := by
    let ex : InstructionExecution 0x102062 0x102065 (rolR32Effect 0x102062 3 2 9) := {
      pre := (fun s ↦ s.RIP = 0x102062)
      code := codeRange 0x102062 [0xc1, 0xc2, 0x9]
      step := rol_r32_imm8_effect_step 0x102062 0xc2 0x9 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2062 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 9) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x102065 0x102067 [.add (.reg 2) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x102065 0x102067 (addR32R32Effect 0x102065 2 2 5) := {
      pre := (fun s ↦ s.RIP = 0x102065)
      code := codeRange 0x102065 [0x1, 0xea]
      step := add_r32_r32_effect_step 0x102065 0xea (by decide)
      present := fun hc ↦ program_text_slice hc 0x2065 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 5))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment30, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12)))))))))))

theorem segment31_runs [Bindings] :
    RunWords 0x102067 0x10207b segment31 := by
  have h1 : RunWords 0x102067 0x10206a [.mov (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102067 0x10206a (movR32R32Effect 0x102067 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x102067)
      code := codeRange 0x102067 [0x41, 0x89, 0xd7]
      step := mov_r32_r32_rex_effect_step 0x102067 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2067 3 (by decide +kernel)
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
  have h2 : RunWords 0x10206a 0x10206d [.and (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x10206a 0x10206d (andR32R32Effect 0x10206a 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x10206a)
      code := codeRange 0x10206a [0x41, 0x21, 0xc7]
      step := and_r32_r32_rex_effect_step 0x10206a 0x41 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x206a 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x10206d 0x102070 [.add (.reg 1) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x10206d 0x102070 (addR32R32Effect 0x10206d 3 1 15) := {
      pre := (fun s ↦ s.RIP = 0x10206d)
      code := codeRange 0x10206d [0x44, 0x1, 0xf9]
      step := add_r32_r32_rex_effect_step 0x10206d 0x44 0xf9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x206d 3 (by decide +kernel)
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
  have h4 : RunWords 0x102070 0x102076 [.add (.reg 1) (.immediate 0x676f02d9)] := by
    let ex : InstructionExecution 0x102070 0x102076 (addR32Imm32Effect 0x102070 6 1 0x676f02d9) := {
      pre := (fun s ↦ s.RIP = 0x102070)
      code := codeRange 0x102070 [0x81, 0xc1, 0xd9, 0x2, 0x6f, 0x67]
      step := add_r32_imm32_effect_step 0x102070 0xc1 0x676f02d9 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2070 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0x676f02d9)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102076 0x102079 [.rol (.reg 1) 14] := by
    let ex : InstructionExecution 0x102076 0x102079 (rolR32Effect 0x102076 3 1 14) := {
      pre := (fun s ↦ s.RIP = 0x102076)
      code := codeRange 0x102076 [0xc1, 0xc1, 0xe]
      step := rol_r32_imm8_effect_step 0x102076 0xc1 0xe (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2076 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 14) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102079 0x10207b [.add (.reg 1) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102079 0x10207b (addR32R32Effect 0x102079 2 1 2) := {
      pre := (fun s ↦ s.RIP = 0x102079)
      code := codeRange 0x102079 [0x1, 0xd1]
      step := add_r32_r32_effect_step 0x102079 0xd1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2079 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 2))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment31, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6)))))

theorem segment32_runs [Bindings] :
    RunWords 0x10207b 0x1020a2 segment32 := by
  have h1 : RunWords 0x10207b 0x10207e [.mov (.reg 15) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x10207b 0x10207e (movR32R32Effect 0x10207b 3 15 1) := {
      pre := (fun s ↦ s.RIP = 0x10207b)
      code := codeRange 0x10207b [0x41, 0x89, 0xcf]
      step := mov_r32_r32_rex_effect_step 0x10207b 0x41 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x207b 3 (by decide +kernel)
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
  have h2 : RunWords 0x10207e 0x102081 [.and (.reg 15) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x10207e 0x102081 (andR32R32Effect 0x10207e 3 15 5) := {
      pre := (fun s ↦ s.RIP = 0x10207e)
      code := codeRange 0x10207e [0x41, 0x21, 0xef]
      step := and_r32_r32_rex_effect_step 0x10207e 0x41 0xef (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x207e 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 15) (.location (.reg 5))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102081 0x102085 [.lea (.reg 12) (.reg 3) (.reg 5)] := by
    let ex : InstructionExecution 0x102081 0x102085 (Register.leaR32Effect 0x102081 4 12 (.sib 3
      (some 5) 0 .none)) := {
      pre := (fun s ↦ s.RIP = 0x102081)
      code := codeRange 0x102081 [0x44, 0x8d, 0x24, 0x2b]
      step := Register.lea_r32_rex_effect_step 0x102081 0x44 (by simp [RexNoWPrefix]) 4 (.sib 3
        (some 5) 0 .none) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2081 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .lea (.reg 12) (.reg 3) (.reg 5)) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102085 0x102087 [.not (.reg 5)] := by
    let ex : InstructionExecution 0x102085 0x102087 (notR32Effect 0x102085 2 5) := {
      pre := (fun s ↦ s.RIP = 0x102085)
      code := codeRange 0x102085 [0xf7, 0xd5]
      step := not_r32_effect_step 0x102085 0xd5 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2085 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 5)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102087 0x10208c [.mov (.reg 11) (.location (.stack 44))] := by
    let ex : InstructionExecution 0x102087 0x10208c (movR32M32Effect 0x102087 11 (.sib 4 none 0 (.d8
      0x2c))) := {
      pre := (LoadPre 0x102087 (fun s ↦ ((.sib 4 none 0 (.d8 0x2c)) : AddrMode).addr s (0x102087 +
        5)) 4)
      code := codeRange 0x102087 [0x44, 0x8b, 0x5c, 0x24, 0x2c]
      step := mov_r32_m32_effect_step 0x102087 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8
        0x2c)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2087 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 44 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 11) (.location (.stack 44))) (dst := 11) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x10208c 0x10208f [.add (.reg 0) (.location (.reg 11))] := by
    let ex : InstructionExecution 0x10208c 0x10208f (addR32R32Effect 0x10208c 3 0 11) := {
      pre := (fun s ↦ s.RIP = 0x10208c)
      code := codeRange 0x10208c [0x44, 0x1, 0xd8]
      step := add_r32_r32_rex_effect_step 0x10208c 0x44 0xd8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x208c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 11))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x10208f 0x102091 [.and (.reg 5) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x10208f 0x102091 (andR32R32Effect 0x10208f 2 5 2) := {
      pre := (fun s ↦ s.RIP = 0x10208f)
      code := codeRange 0x10208f [0x21, 0xd5]
      step := and_r32_r32_effect_step 0x10208f 0xd5 (by decide)
      present := fun hc ↦ program_text_slice hc 0x208f 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 5) (.location (.reg 2))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x102091 0x102093 [.add (.reg 0) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x102091 0x102093 (addR32R32Effect 0x102091 2 0 5) := {
      pre := (fun s ↦ s.RIP = 0x102091)
      code := codeRange 0x102091 [0x1, 0xe8]
      step := add_r32_r32_effect_step 0x102091 0xe8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2091 2 (by decide +kernel)
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
  have h9 : RunWords 0x102093 0x102097 [.lea (.reg 5) (.reg 15) (.reg 0)] := by
    let ex : InstructionExecution 0x102093 0x102097 (Register.leaR32Effect 0x102093 4 5 (.sib 15
      (some 0) 0 .none)) := {
      pre := (fun s ↦ s.RIP = 0x102093)
      code := codeRange 0x102093 [0x41, 0x8d, 0x2c, 0x7]
      step := Register.lea_r32_rex_effect_step 0x102093 0x41 (by simp [RexNoWPrefix]) 5 (.sib 15
        (some 0) 0 .none) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2093 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .lea (.reg 5) (.reg 15) (.reg 0)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x102097 0x10209d [.add (.reg 5) (.immediate 0x8d2a4c8a)] := by
    let ex : InstructionExecution 0x102097 0x10209d (addR32Imm32Effect 0x102097 6 5 0x8d2a4c8a) := {
      pre := (fun s ↦ s.RIP = 0x102097)
      code := codeRange 0x102097 [0x81, 0xc5, 0x8a, 0x4c, 0x2a, 0x8d]
      step := add_r32_imm32_effect_step 0x102097 0xc5 0x8d2a4c8a (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2097 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.immediate 0x8d2a4c8a)) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x10209d 0x1020a0 [.rol (.reg 5) 20] := by
    let ex : InstructionExecution 0x10209d 0x1020a0 (rolR32Effect 0x10209d 3 5 20) := {
      pre := (fun s ↦ s.RIP = 0x10209d)
      code := codeRange 0x10209d [0xc1, 0xc5, 0x14]
      step := rol_r32_imm8_effect_step 0x10209d 0xc5 0x14 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x209d 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 5) 20) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x1020a0 0x1020a2 [.add (.reg 5) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1020a0 0x1020a2 (addR32R32Effect 0x1020a0 2 5 1) := {
      pre := (fun s ↦ s.RIP = 0x1020a0)
      code := codeRange 0x1020a0 [0x1, 0xcd]
      step := add_r32_r32_effect_step 0x1020a0 0xcd (by decide)
      present := fun hc ↦ program_text_slice hc 0x20a0 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 5) (.location (.reg 1))) (dst := 5) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment32, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12)))))))))))

end Md5.Proofs.Block.Rounds
