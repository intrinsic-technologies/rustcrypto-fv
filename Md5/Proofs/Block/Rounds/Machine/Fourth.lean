import Md5.Proofs.Block.Rounds.Step
import Md5.Proofs.Block.Rounds.Address
import Md5.Proofs.Block.Rounds.Interface
import Md5.Proofs.Block.Rounds.Register
import Md5.Proofs.Block.Rounds.Load
import Md5.Proofs.Block.Rounds.Store

namespace Md5.Proofs.Block.Rounds
open X86 X86.Machine X86.UserProcess X86Proofs

theorem segment49_runs [Bindings] :
    RunWords 0x102251 0x102274 segment49 := by
  have h1 : RunWords 0x102251 0x102254 [.mov (.reg 15) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102251 0x102254 (movR32R32Effect 0x102251 3 15 2) := {
      pre := (fun s ↦ s.RIP = 0x102251)
      code := codeRange 0x102251 [0x41, 0x89, 0xd7]
      step := mov_r32_r32_rex_effect_step 0x102251 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2251 3 (by decide +kernel)
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
  have h2 : RunWords 0x102254 0x102257 [.not (.reg 15)] := by
    let ex : InstructionExecution 0x102254 0x102257 (notR32Effect 0x102254 3 15) := {
      pre := (fun s ↦ s.RIP = 0x102254)
      code := codeRange 0x102254 [0x41, 0xf7, 0xd7]
      step := not_r32_rex_effect_step 0x102254 0x41 0xd7 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x2254 3 (by decide +kernel)
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
  have h3 : RunWords 0x102257 0x10225a [.or (.reg 15) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102257 0x10225a (Register.orR32R32Effect 0x102257 3 15 0) := {
      pre := (fun s ↦ s.RIP = 0x102257)
      code := codeRange 0x102257 [0x41, 0x9, 0xc7]
      step := Register.or_r32_r32_rex_effect_step 0x102257 0x41 0xc7 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x2257 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 15) (.location (.reg 0))) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x10225a 0x10225d [.xor (.reg 15) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x10225a 0x10225d (xorR32R32Effect 0x10225a 3 15 12) := {
      pre := (fun s ↦ s.RIP = 0x10225a)
      code := codeRange 0x10225a [0x45, 0x31, 0xe7]
      step := xor_r32_r32_rex_effect_step 0x10225a 0x45 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x225a 3 (by decide +kernel)
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
  have h5 : RunWords 0x10225d 0x102260 [.add (.reg 1) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x10225d 0x102260 (addR32R32Effect 0x10225d 3 1 15) := {
      pre := (fun s ↦ s.RIP = 0x10225d)
      code := codeRange 0x10225d [0x44, 0x1, 0xf9]
      step := add_r32_r32_rex_effect_step 0x10225d 0x44 0xf9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x225d 3 (by decide +kernel)
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
  have h6 : RunWords 0x102260 0x102266 [.add (.reg 1) (.immediate 0xf4292244)] := by
    let ex : InstructionExecution 0x102260 0x102266 (addR32Imm32Effect 0x102260 6 1 0xf4292244) := {
      pre := (fun s ↦ s.RIP = 0x102260)
      code := codeRange 0x102260 [0x81, 0xc1, 0x44, 0x22, 0x29, 0xf4]
      step := add_r32_imm32_effect_step 0x102260 0xc1 0xf4292244 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2260 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0xf4292244)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102266 0x102269 [.rol (.reg 1) 6] := by
    let ex : InstructionExecution 0x102266 0x102269 (rolR32Effect 0x102266 3 1 6) := {
      pre := (fun s ↦ s.RIP = 0x102266)
      code := codeRange 0x102266 [0xc1, 0xc1, 0x6]
      step := rol_r32_imm8_effect_step 0x102266 0xc1 0x6 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2266 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 6) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x102269 0x10226c [.add (.reg 2) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x102269 0x10226c (addR32R32Effect 0x102269 3 2 8) := {
      pre := (fun s ↦ s.RIP = 0x102269)
      code := codeRange 0x102269 [0x44, 0x1, 0xc2]
      step := add_r32_r32_rex_effect_step 0x102269 0x44 0xc2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2269 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 8))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x10226c 0x10226f [.mov (.reg 9) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x10226c 0x10226f (movR32R32Effect 0x10226c 3 9 12) := {
      pre := (fun s ↦ s.RIP = 0x10226c)
      code := codeRange 0x10226c [0x45, 0x89, 0xe1]
      step := mov_r32_r32_rex_effect_step 0x10226c 0x45 0xe1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x226c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 9) (.location (.reg 12))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x10226f 0x102272 [.not (.reg 9)] := by
    let ex : InstructionExecution 0x10226f 0x102272 (notR32Effect 0x10226f 3 9) := {
      pre := (fun s ↦ s.RIP = 0x10226f)
      code := codeRange 0x10226f [0x41, 0xf7, 0xd1]
      step := not_r32_rex_effect_step 0x10226f 0x41 0xd1 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x226f 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 9)) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x102272 0x102274 [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102272 0x102274 (addR32R32Effect 0x102272 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x102272)
      code := codeRange 0x102272 [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x102272 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2272 2 (by decide +kernel)
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
  simpa only [segment49, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment50_runs [Bindings] :
    RunWords 0x102274 0x10228b segment50 := by
  have h1 : RunWords 0x102274 0x102277 [.or (.reg 9) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102274 0x102277 (Register.orR32R32Effect 0x102274 3 9 1) := {
      pre := (fun s ↦ s.RIP = 0x102274)
      code := codeRange 0x102274 [0x41, 0x9, 0xc9]
      step := Register.or_r32_r32_rex_effect_step 0x102274 0x41 0xc9 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x2274 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 9) (.location (.reg 1))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x102277 0x10227a [.xor (.reg 9) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102277 0x10227a (xorR32R32Effect 0x102277 3 9 0) := {
      pre := (fun s ↦ s.RIP = 0x102277)
      code := codeRange 0x102277 [0x41, 0x31, 0xc1]
      step := xor_r32_r32_rex_effect_step 0x102277 0x41 0xc1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2277 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 9) (.location (.reg 0))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x10227a 0x10227d [.add (.reg 2) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x10227a 0x10227d (addR32R32Effect 0x10227a 3 2 9) := {
      pre := (fun s ↦ s.RIP = 0x10227a)
      code := codeRange 0x10227a [0x44, 0x1, 0xca]
      step := add_r32_r32_rex_effect_step 0x10227a 0x44 0xca (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x227a 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 9))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x10227d 0x102283 [.add (.reg 2) (.immediate 0x432aff97)] := by
    let ex : InstructionExecution 0x10227d 0x102283 (addR32Imm32Effect 0x10227d 6 2 0x432aff97) := {
      pre := (fun s ↦ s.RIP = 0x10227d)
      code := codeRange 0x10227d [0x81, 0xc2, 0x97, 0xff, 0x2a, 0x43]
      step := add_r32_imm32_effect_step 0x10227d 0xc2 0x432aff97 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x227d 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0x432aff97)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102283 0x102286 [.add (.reg 12) (.location (.reg 3))] := by
    let ex : InstructionExecution 0x102283 0x102286 (addR32R32Effect 0x102283 3 12 3) := {
      pre := (fun s ↦ s.RIP = 0x102283)
      code := codeRange 0x102283 [0x41, 0x1, 0xdc]
      step := add_r32_r32_rex_effect_step 0x102283 0x41 0xdc (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2283 3 (by decide +kernel)
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
  have h6 : RunWords 0x102286 0x102289 [.rol (.reg 2) 10] := by
    let ex : InstructionExecution 0x102286 0x102289 (rolR32Effect 0x102286 3 2 10) := {
      pre := (fun s ↦ s.RIP = 0x102286)
      code := codeRange 0x102286 [0xc1, 0xc2, 0xa]
      step := rol_r32_imm8_effect_step 0x102286 0xc2 0xa (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2286 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 10) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102289 0x10228b [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102289 0x10228b (addR32R32Effect 0x102289 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x102289)
      code := codeRange 0x102289 [0x1, 0xca]
      step := add_r32_r32_effect_step 0x102289 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x2289 2 (by decide +kernel)
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
  simpa only [segment50, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7))))))

theorem segment51_runs [Bindings] :
    RunWords 0x10228b 0x1022a5 segment51 := by
  have h1 : RunWords 0x10228b 0x10228d [.mov (.reg 7) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x10228b 0x10228d (movR32R32Effect 0x10228b 2 7 0) := {
      pre := (fun s ↦ s.RIP = 0x10228b)
      code := codeRange 0x10228b [0x89, 0xc7]
      step := mov_r32_r32_effect_step 0x10228b 0xc7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x228b 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 7) (.location (.reg 0))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x10228d 0x10228f [.not (.reg 7)] := by
    let ex : InstructionExecution 0x10228d 0x10228f (notR32Effect 0x10228d 2 7) := {
      pre := (fun s ↦ s.RIP = 0x10228d)
      code := codeRange 0x10228d [0xf7, 0xd7]
      step := not_r32_effect_step 0x10228d 0xd7 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x228d 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 7)) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x10228f 0x102291 [.or (.reg 7) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x10228f 0x102291 (Register.orR32R32Effect 0x10228f 2 7 2) := {
      pre := (fun s ↦ s.RIP = 0x10228f)
      code := codeRange 0x10228f [0x9, 0xd7]
      step := Register.or_r32_r32_effect_step 0x10228f 0xd7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x228f 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 7) (.location (.reg 2))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102291 0x102293 [.xor (.reg 7) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102291 0x102293 (xorR32R32Effect 0x102291 2 7 1) := {
      pre := (fun s ↦ s.RIP = 0x102291)
      code := codeRange 0x102291 [0x31, 0xcf]
      step := xor_r32_r32_effect_step 0x102291 0xcf (by decide)
      present := fun hc ↦ program_text_slice hc 0x2291 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 7) (.location (.reg 1))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102293 0x102296 [.add (.reg 7) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x102293 0x102296 (addR32R32Effect 0x102293 3 7 12) := {
      pre := (fun s ↦ s.RIP = 0x102293)
      code := codeRange 0x102293 [0x44, 0x1, 0xe7]
      step := add_r32_r32_rex_effect_step 0x102293 0x44 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2293 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.reg 12))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102296 0x10229c [.add (.reg 7) (.immediate 0xab9423a7)] := by
    let ex : InstructionExecution 0x102296 0x10229c (addR32Imm32Effect 0x102296 6 7 0xab9423a7) := {
      pre := (fun s ↦ s.RIP = 0x102296)
      code := codeRange 0x102296 [0x81, 0xc7, 0xa7, 0x23, 0x94, 0xab]
      step := add_r32_imm32_effect_step 0x102296 0xc7 0xab9423a7 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2296 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.immediate 0xab9423a7)) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x10229c 0x1022a0 [.add (.reg 0) (.location (.stack 64))] := by
    let ex : InstructionExecution 0x10229c 0x1022a0 (addR32M32Effect 0x10229c 4 0 (.sib 4 none 0
      (.d8 0x40))) := {
      pre := (LoadPre 0x10229c (fun s ↦ ((.sib 4 none 0 (.d8 0x40)) : AddrMode).addr s (0x10229c +
        4)) 4)
      code := codeRange 0x10229c [0x3, 0x44, 0x24, 0x40]
      step := add_r32_m32_noRex_effect_step 0x10229c 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x229c 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 64 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.stack 64))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1022a0 0x1022a3 [.rol (.reg 7) 15] := by
    let ex : InstructionExecution 0x1022a0 0x1022a3 (rolR32Effect 0x1022a0 3 7 15) := {
      pre := (fun s ↦ s.RIP = 0x1022a0)
      code := codeRange 0x1022a0 [0xc1, 0xc7, 0xf]
      step := rol_r32_imm8_effect_step 0x1022a0 0xc7 0xf (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22a0 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 7) 15) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x1022a3 0x1022a5 [.add (.reg 7) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1022a3 0x1022a5 (addR32R32Effect 0x1022a3 2 7 2) := {
      pre := (fun s ↦ s.RIP = 0x1022a3)
      code := codeRange 0x1022a3 [0x1, 0xd7]
      step := add_r32_r32_effect_step 0x1022a3 0xd7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x22a3 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.reg 2))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment51, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

theorem segment52_runs [Bindings] :
    RunWords 0x1022a5 0x1022c1 segment52 := by
  have h1 : RunWords 0x1022a5 0x1022a8 [.mov (.reg 9) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1022a5 0x1022a8 (movR32R32Effect 0x1022a5 3 9 1) := {
      pre := (fun s ↦ s.RIP = 0x1022a5)
      code := codeRange 0x1022a5 [0x41, 0x89, 0xc9]
      step := mov_r32_r32_rex_effect_step 0x1022a5 0x41 0xc9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22a5 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 9) (.location (.reg 1))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1022a8 0x1022ab [.not (.reg 9)] := by
    let ex : InstructionExecution 0x1022a8 0x1022ab (notR32Effect 0x1022a8 3 9) := {
      pre := (fun s ↦ s.RIP = 0x1022a8)
      code := codeRange 0x1022a8 [0x41, 0xf7, 0xd1]
      step := not_r32_rex_effect_step 0x1022a8 0x41 0xd1 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x22a8 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 9)) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1022ab 0x1022ae [.or (.reg 9) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x1022ab 0x1022ae (Register.orR32R32Effect 0x1022ab 3 9 7) := {
      pre := (fun s ↦ s.RIP = 0x1022ab)
      code := codeRange 0x1022ab [0x41, 0x9, 0xf9]
      step := Register.or_r32_r32_rex_effect_step 0x1022ab 0x41 0xf9 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x22ab 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 9) (.location (.reg 7))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1022ae 0x1022b1 [.xor (.reg 9) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1022ae 0x1022b1 (xorR32R32Effect 0x1022ae 3 9 2) := {
      pre := (fun s ↦ s.RIP = 0x1022ae)
      code := codeRange 0x1022ae [0x41, 0x31, 0xd1]
      step := xor_r32_r32_rex_effect_step 0x1022ae 0x41 0xd1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22ae 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 9) (.location (.reg 2))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1022b1 0x1022b4 [.add (.reg 0) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x1022b1 0x1022b4 (addR32R32Effect 0x1022b1 3 0 9) := {
      pre := (fun s ↦ s.RIP = 0x1022b1)
      code := codeRange 0x1022b1 [0x44, 0x1, 0xc8]
      step := add_r32_r32_rex_effect_step 0x1022b1 0x44 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22b1 3 (by decide +kernel)
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
  have h6 : RunWords 0x1022b4 0x1022b9 [.add (.reg 0) (.immediate 0xfc93a039)] := by
    let ex : InstructionExecution 0x1022b4 0x1022b9 (addR32Imm32Effect 0x1022b4 5 0 0xfc93a039) := {
      pre := (fun s ↦ s.RIP = 0x1022b4)
      code := codeRange 0x1022b4 [0x5, 0x39, 0xa0, 0x93, 0xfc]
      step := Register.add_eax_imm32_effect_step 0x1022b4 0xfc93a039
      present := fun hc ↦ program_text_slice hc 0x22b4 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0xfc93a039)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1022b9 0x1022bc [.add (.reg 1) (.location (.reg 11))] := by
    let ex : InstructionExecution 0x1022b9 0x1022bc (addR32R32Effect 0x1022b9 3 1 11) := {
      pre := (fun s ↦ s.RIP = 0x1022b9)
      code := codeRange 0x1022b9 [0x44, 0x1, 0xd9]
      step := add_r32_r32_rex_effect_step 0x1022b9 0x44 0xd9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22b9 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.reg 11))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1022bc 0x1022bf [.rol (.reg 0) 21] := by
    let ex : InstructionExecution 0x1022bc 0x1022bf (rolR32Effect 0x1022bc 3 0 21) := {
      pre := (fun s ↦ s.RIP = 0x1022bc)
      code := codeRange 0x1022bc [0xc1, 0xc0, 0x15]
      step := rol_r32_imm8_effect_step 0x1022bc 0xc0 0x15 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22bc 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 21) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x1022bf 0x1022c1 [.add (.reg 0) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x1022bf 0x1022c1 (addR32R32Effect 0x1022bf 2 0 7) := {
      pre := (fun s ↦ s.RIP = 0x1022bf)
      code := codeRange 0x1022bf [0x1, 0xf8]
      step := add_r32_r32_effect_step 0x1022bf 0xf8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x22bf 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 7))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment52, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

theorem segment53_runs [Bindings] :
    RunWords 0x1022c1 0x1022e5 segment53 := by
  have h1 : RunWords 0x1022c1 0x1022c4 [.mov (.reg 8) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1022c1 0x1022c4 (movR32R32Effect 0x1022c1 3 8 2) := {
      pre := (fun s ↦ s.RIP = 0x1022c1)
      code := codeRange 0x1022c1 [0x41, 0x89, 0xd0]
      step := mov_r32_r32_rex_effect_step 0x1022c1 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22c1 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.reg 2))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1022c4 0x1022c7 [.not (.reg 8)] := by
    let ex : InstructionExecution 0x1022c4 0x1022c7 (notR32Effect 0x1022c4 3 8) := {
      pre := (fun s ↦ s.RIP = 0x1022c4)
      code := codeRange 0x1022c4 [0x41, 0xf7, 0xd0]
      step := not_r32_rex_effect_step 0x1022c4 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x22c4 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 8)) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1022c7 0x1022ca [.or (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1022c7 0x1022ca (Register.orR32R32Effect 0x1022c7 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x1022c7)
      code := codeRange 0x1022c7 [0x41, 0x9, 0xc0]
      step := Register.or_r32_r32_rex_effect_step 0x1022c7 0x41 0xc0 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x22c7 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 8) (.location (.reg 0))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1022ca 0x1022cd [.xor (.reg 8) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x1022ca 0x1022cd (xorR32R32Effect 0x1022ca 3 8 7) := {
      pre := (fun s ↦ s.RIP = 0x1022ca)
      code := codeRange 0x1022ca [0x41, 0x31, 0xf8]
      step := xor_r32_r32_rex_effect_step 0x1022ca 0x41 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22ca 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 8) (.location (.reg 7))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1022cd 0x1022d0 [.add (.reg 1) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x1022cd 0x1022d0 (addR32R32Effect 0x1022cd 3 1 8) := {
      pre := (fun s ↦ s.RIP = 0x1022cd)
      code := codeRange 0x1022cd [0x44, 0x1, 0xc1]
      step := add_r32_r32_rex_effect_step 0x1022cd 0x44 0xc1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22cd 3 (by decide +kernel)
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
  have h6 : RunWords 0x1022d0 0x1022d6 [.add (.reg 1) (.immediate 0x655b59c3)] := by
    let ex : InstructionExecution 0x1022d0 0x1022d6 (addR32Imm32Effect 0x1022d0 6 1 0x655b59c3) := {
      pre := (fun s ↦ s.RIP = 0x1022d0)
      code := codeRange 0x1022d0 [0x81, 0xc1, 0xc3, 0x59, 0x5b, 0x65]
      step := add_r32_imm32_effect_step 0x1022d0 0xc1 0x655b59c3 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22d0 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0x655b59c3)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1022d6 0x1022d9 [.rol (.reg 1) 6] := by
    let ex : InstructionExecution 0x1022d6 0x1022d9 (rolR32Effect 0x1022d6 3 1 6) := {
      pre := (fun s ↦ s.RIP = 0x1022d6)
      code := codeRange 0x1022d6 [0xc1, 0xc1, 0x6]
      step := rol_r32_imm8_effect_step 0x1022d6 0xc1 0x6 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22d6 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 6) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1022d9 0x1022dd [.add (.reg 2) (.location (.stack 72))] := by
    let ex : InstructionExecution 0x1022d9 0x1022dd (addR32M32Effect 0x1022d9 4 2 (.sib 4 none 0
      (.d8 0x48))) := {
      pre := (LoadPre 0x1022d9 (fun s ↦ ((.sib 4 none 0 (.d8 0x48)) : AddrMode).addr s (0x1022d9 +
        4)) 4)
      code := codeRange 0x1022d9 [0x3, 0x54, 0x24, 0x48]
      step := add_r32_m32_noRex_effect_step 0x1022d9 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22d9 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 72 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.stack 72))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x1022dd 0x1022e0 [.mov (.reg 8) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x1022dd 0x1022e0 (movR32R32Effect 0x1022dd 3 8 7) := {
      pre := (fun s ↦ s.RIP = 0x1022dd)
      code := codeRange 0x1022dd [0x41, 0x89, 0xf8]
      step := mov_r32_r32_rex_effect_step 0x1022dd 0x41 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22dd 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.reg 7))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x1022e0 0x1022e3 [.not (.reg 8)] := by
    let ex : InstructionExecution 0x1022e0 0x1022e3 (notR32Effect 0x1022e0 3 8) := {
      pre := (fun s ↦ s.RIP = 0x1022e0)
      code := codeRange 0x1022e0 [0x41, 0xf7, 0xd0]
      step := not_r32_rex_effect_step 0x1022e0 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x22e0 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 8)) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x1022e3 0x1022e5 [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1022e3 0x1022e5 (addR32R32Effect 0x1022e3 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x1022e3)
      code := codeRange 0x1022e3 [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x1022e3 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x22e3 2 (by decide +kernel)
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
  simpa only [segment53, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment54_runs [Bindings] :
    RunWords 0x1022e5 0x1022fc segment54 := by
  have h1 : RunWords 0x1022e5 0x1022e8 [.or (.reg 8) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1022e5 0x1022e8 (Register.orR32R32Effect 0x1022e5 3 8 1) := {
      pre := (fun s ↦ s.RIP = 0x1022e5)
      code := codeRange 0x1022e5 [0x41, 0x9, 0xc8]
      step := Register.or_r32_r32_rex_effect_step 0x1022e5 0x41 0xc8 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x22e5 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 8) (.location (.reg 1))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1022e8 0x1022eb [.xor (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1022e8 0x1022eb (xorR32R32Effect 0x1022e8 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x1022e8)
      code := codeRange 0x1022e8 [0x41, 0x31, 0xc0]
      step := xor_r32_r32_rex_effect_step 0x1022e8 0x41 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22e8 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 8) (.location (.reg 0))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1022eb 0x1022ee [.add (.reg 2) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x1022eb 0x1022ee (addR32R32Effect 0x1022eb 3 2 8) := {
      pre := (fun s ↦ s.RIP = 0x1022eb)
      code := codeRange 0x1022eb [0x44, 0x1, 0xc2]
      step := add_r32_r32_rex_effect_step 0x1022eb 0x44 0xc2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22eb 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 8))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1022ee 0x1022f4 [.add (.reg 2) (.immediate 0x8f0ccc92)] := by
    let ex : InstructionExecution 0x1022ee 0x1022f4 (addR32Imm32Effect 0x1022ee 6 2 0x8f0ccc92) := {
      pre := (fun s ↦ s.RIP = 0x1022ee)
      code := codeRange 0x1022ee [0x81, 0xc2, 0x92, 0xcc, 0xc, 0x8f]
      step := add_r32_imm32_effect_step 0x1022ee 0xc2 0x8f0ccc92 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22ee 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0x8f0ccc92)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1022f4 0x1022f7 [.add (.reg 7) (.location (.reg 14))] := by
    let ex : InstructionExecution 0x1022f4 0x1022f7 (addR32R32Effect 0x1022f4 3 7 14) := {
      pre := (fun s ↦ s.RIP = 0x1022f4)
      code := codeRange 0x1022f4 [0x44, 0x1, 0xf7]
      step := add_r32_r32_rex_effect_step 0x1022f4 0x44 0xf7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22f4 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.reg 14))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x1022f7 0x1022fa [.rol (.reg 2) 10] := by
    let ex : InstructionExecution 0x1022f7 0x1022fa (rolR32Effect 0x1022f7 3 2 10) := {
      pre := (fun s ↦ s.RIP = 0x1022f7)
      code := codeRange 0x1022f7 [0xc1, 0xc2, 0xa]
      step := rol_r32_imm8_effect_step 0x1022f7 0xc2 0xa (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22f7 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 10) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1022fa 0x1022fc [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1022fa 0x1022fc (addR32R32Effect 0x1022fa 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x1022fa)
      code := codeRange 0x1022fa [0x1, 0xca]
      step := add_r32_r32_effect_step 0x1022fa 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x22fa 2 (by decide +kernel)
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
  simpa only [segment54, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7))))))

theorem segment55_runs [Bindings] :
    RunWords 0x1022fc 0x10231a segment55 := by
  have h1 : RunWords 0x1022fc 0x1022ff [.mov (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1022fc 0x1022ff (movR32R32Effect 0x1022fc 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x1022fc)
      code := codeRange 0x1022fc [0x41, 0x89, 0xc0]
      step := mov_r32_r32_rex_effect_step 0x1022fc 0x41 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x22fc 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.reg 0))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1022ff 0x102302 [.not (.reg 8)] := by
    let ex : InstructionExecution 0x1022ff 0x102302 (notR32Effect 0x1022ff 3 8) := {
      pre := (fun s ↦ s.RIP = 0x1022ff)
      code := codeRange 0x1022ff [0x41, 0xf7, 0xd0]
      step := not_r32_rex_effect_step 0x1022ff 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x22ff 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 8)) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102302 0x102305 [.or (.reg 8) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102302 0x102305 (Register.orR32R32Effect 0x102302 3 8 2) := {
      pre := (fun s ↦ s.RIP = 0x102302)
      code := codeRange 0x102302 [0x41, 0x9, 0xd0]
      step := Register.or_r32_r32_rex_effect_step 0x102302 0x41 0xd0 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x2302 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 8) (.location (.reg 2))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102305 0x102308 [.xor (.reg 8) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102305 0x102308 (xorR32R32Effect 0x102305 3 8 1) := {
      pre := (fun s ↦ s.RIP = 0x102305)
      code := codeRange 0x102305 [0x41, 0x31, 0xc8]
      step := xor_r32_r32_rex_effect_step 0x102305 0x41 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2305 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 8) (.location (.reg 1))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102308 0x10230b [.add (.reg 7) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x102308 0x10230b (addR32R32Effect 0x102308 3 7 8) := {
      pre := (fun s ↦ s.RIP = 0x102308)
      code := codeRange 0x102308 [0x44, 0x1, 0xc7]
      step := add_r32_r32_rex_effect_step 0x102308 0x44 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2308 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.reg 8))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x10230b 0x102311 [.add (.reg 7) (.immediate 0xffeff47d)] := by
    let ex : InstructionExecution 0x10230b 0x102311 (addR32Imm32Effect 0x10230b 6 7 0xffeff47d) := {
      pre := (fun s ↦ s.RIP = 0x10230b)
      code := codeRange 0x10230b [0x81, 0xc7, 0x7d, 0xf4, 0xef, 0xff]
      step := add_r32_imm32_effect_step 0x10230b 0xc7 0xffeff47d (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x230b 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.immediate 0xffeff47d)) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102311 0x102315 [.add (.reg 0) (.location (.stack 80))] := by
    let ex : InstructionExecution 0x102311 0x102315 (addR32M32Effect 0x102311 4 0 (.sib 4 none 0
      (.d8 0x50))) := {
      pre := (LoadPre 0x102311 (fun s ↦ ((.sib 4 none 0 (.d8 0x50)) : AddrMode).addr s (0x102311 +
        4)) 4)
      code := codeRange 0x102311 [0x3, 0x44, 0x24, 0x50]
      step := add_r32_m32_noRex_effect_step 0x102311 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2311 4 (by decide +kernel)
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
  have h8 : RunWords 0x102315 0x102318 [.rol (.reg 7) 15] := by
    let ex : InstructionExecution 0x102315 0x102318 (rolR32Effect 0x102315 3 7 15) := {
      pre := (fun s ↦ s.RIP = 0x102315)
      code := codeRange 0x102315 [0xc1, 0xc7, 0xf]
      step := rol_r32_imm8_effect_step 0x102315 0xc7 0xf (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2315 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 7) 15) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x102318 0x10231a [.add (.reg 7) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102318 0x10231a (addR32R32Effect 0x102318 2 7 2) := {
      pre := (fun s ↦ s.RIP = 0x102318)
      code := codeRange 0x102318 [0x1, 0xd7]
      step := add_r32_r32_effect_step 0x102318 0xd7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2318 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.reg 2))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment55, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))

theorem segment56_runs [Bindings] :
    RunWords 0x10231a 0x102337 segment56 := by
  have h1 : RunWords 0x10231a 0x10231d [.mov (.reg 8) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x10231a 0x10231d (movR32R32Effect 0x10231a 3 8 1) := {
      pre := (fun s ↦ s.RIP = 0x10231a)
      code := codeRange 0x10231a [0x41, 0x89, 0xc8]
      step := mov_r32_r32_rex_effect_step 0x10231a 0x41 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x231a 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.reg 1))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x10231d 0x102320 [.not (.reg 8)] := by
    let ex : InstructionExecution 0x10231d 0x102320 (notR32Effect 0x10231d 3 8) := {
      pre := (fun s ↦ s.RIP = 0x10231d)
      code := codeRange 0x10231d [0x41, 0xf7, 0xd0]
      step := not_r32_rex_effect_step 0x10231d 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x231d 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 8)) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102320 0x102323 [.or (.reg 8) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x102320 0x102323 (Register.orR32R32Effect 0x102320 3 8 7) := {
      pre := (fun s ↦ s.RIP = 0x102320)
      code := codeRange 0x102320 [0x41, 0x9, 0xf8]
      step := Register.or_r32_r32_rex_effect_step 0x102320 0x41 0xf8 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x2320 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 8) (.location (.reg 7))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102323 0x102326 [.xor (.reg 8) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102323 0x102326 (xorR32R32Effect 0x102323 3 8 2) := {
      pre := (fun s ↦ s.RIP = 0x102323)
      code := codeRange 0x102323 [0x41, 0x31, 0xd0]
      step := xor_r32_r32_rex_effect_step 0x102323 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2323 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 8) (.location (.reg 2))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102326 0x102329 [.add (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102326 0x102329 (addR32R32Effect 0x102326 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x102326)
      code := codeRange 0x102326 [0x41, 0x1, 0xc0]
      step := add_r32_r32_rex_effect_step 0x102326 0x41 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2326 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 8) (.location (.reg 0))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102329 0x102330 [.add (.reg 8) (.immediate 0x85845dd1)] := by
    let ex : InstructionExecution 0x102329 0x102330 (addR32Imm32Effect 0x102329 7 8 0x85845dd1) := {
      pre := (fun s ↦ s.RIP = 0x102329)
      code := codeRange 0x102329 [0x41, 0x81, 0xc0, 0xd1, 0x5d, 0x84, 0x85]
      step := add_r32_imm32_rex_effect_step 0x102329 0x41 0xc0 0x85845dd1 (by simp [RexNoWPrefix])
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2329 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 8) (.immediate 0x85845dd1)) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102330 0x102334 [.rol (.reg 8) 21] := by
    let ex : InstructionExecution 0x102330 0x102334 (rolR32Effect 0x102330 4 8 21) := {
      pre := (fun s ↦ s.RIP = 0x102330)
      code := codeRange 0x102330 [0x41, 0xc1, 0xc0, 0x15]
      step := rol_r32_imm8_rex_effect_step 0x102330 0x41 0xc0 0x15 (by simp [RexNoWPrefix]) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2330 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 8) 21) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x102334 0x102337 [.add (.reg 8) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x102334 0x102337 (addR32R32Effect 0x102334 3 8 7) := {
      pre := (fun s ↦ s.RIP = 0x102334)
      code := codeRange 0x102334 [0x41, 0x1, 0xf8]
      step := add_r32_r32_rex_effect_step 0x102334 0x41 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2334 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 8) (.location (.reg 7))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment56, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8)))))))

theorem segment57_runs [Bindings] :
    RunWords 0x102337 0x102356 segment57 := by
  have h1 : RunWords 0x102337 0x10233b [.add (.reg 1) (.location (.stack 24))] := by
    let ex : InstructionExecution 0x102337 0x10233b (addR32M32Effect 0x102337 4 1 (.sib 4 none 0
      (.d8 0x18))) := {
      pre := (LoadPre 0x102337 (fun s ↦ ((.sib 4 none 0 (.d8 0x18)) : AddrMode).addr s (0x102337 +
        4)) 4)
      code := codeRange 0x102337 [0x3, 0x4c, 0x24, 0x18]
      step := add_r32_m32_noRex_effect_step 0x102337 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2337 4 (by decide +kernel)
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
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.stack 24))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x10233b 0x10233d [.mov (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x10233b 0x10233d (movR32R32Effect 0x10233b 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x10233b)
      code := codeRange 0x10233b [0x89, 0xd0]
      step := mov_r32_r32_effect_step 0x10233b 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x233b 2 (by decide +kernel)
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
  have h3 : RunWords 0x10233d 0x10233f [.not (.reg 0)] := by
    let ex : InstructionExecution 0x10233d 0x10233f (notR32Effect 0x10233d 2 0) := {
      pre := (fun s ↦ s.RIP = 0x10233d)
      code := codeRange 0x10233d [0xf7, 0xd0]
      step := not_r32_effect_step 0x10233d 0xd0 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x233d 2 (by decide +kernel)
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
  have h4 : RunWords 0x10233f 0x102342 [.or (.reg 0) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x10233f 0x102342 (Register.orR32R32Effect 0x10233f 3 0 8) := {
      pre := (fun s ↦ s.RIP = 0x10233f)
      code := codeRange 0x10233f [0x44, 0x9, 0xc0]
      step := Register.or_r32_r32_rex_effect_step 0x10233f 0x44 0xc0 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x233f 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 0) (.location (.reg 8))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102342 0x102344 [.xor (.reg 0) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x102342 0x102344 (xorR32R32Effect 0x102342 2 0 7) := {
      pre := (fun s ↦ s.RIP = 0x102342)
      code := codeRange 0x102342 [0x31, 0xf8]
      step := xor_r32_r32_effect_step 0x102342 0xf8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2342 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 0) (.location (.reg 7))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102344 0x102346 [.add (.reg 0) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x102344 0x102346 (addR32R32Effect 0x102344 2 0 1) := {
      pre := (fun s ↦ s.RIP = 0x102344)
      code := codeRange 0x102344 [0x1, 0xc8]
      step := add_r32_r32_effect_step 0x102344 0xc8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2344 2 (by decide +kernel)
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
  have h7 : RunWords 0x102346 0x10234b [.add (.reg 0) (.immediate 0x6fa87e4f)] := by
    let ex : InstructionExecution 0x102346 0x10234b (addR32Imm32Effect 0x102346 5 0 0x6fa87e4f) := {
      pre := (fun s ↦ s.RIP = 0x102346)
      code := codeRange 0x102346 [0x5, 0x4f, 0x7e, 0xa8, 0x6f]
      step := Register.add_eax_imm32_effect_step 0x102346 0x6fa87e4f
      present := fun hc ↦ program_text_slice hc 0x2346 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0x6fa87e4f)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x10234b 0x10234e [.rol (.reg 0) 6] := by
    let ex : InstructionExecution 0x10234b 0x10234e (rolR32Effect 0x10234b 3 0 6) := {
      pre := (fun s ↦ s.RIP = 0x10234b)
      code := codeRange 0x10234b [0xc1, 0xc0, 0x6]
      step := rol_r32_imm8_effect_step 0x10234b 0xc0 0x6 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x234b 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 6) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x10234e 0x102351 [.add (.reg 2) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x10234e 0x102351 (addR32R32Effect 0x10234e 3 2 10) := {
      pre := (fun s ↦ s.RIP = 0x10234e)
      code := codeRange 0x10234e [0x44, 0x1, 0xd2]
      step := add_r32_r32_rex_effect_step 0x10234e 0x44 0xd2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x234e 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 10))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x102351 0x102353 [.mov (.reg 1) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x102351 0x102353 (movR32R32Effect 0x102351 2 1 7) := {
      pre := (fun s ↦ s.RIP = 0x102351)
      code := codeRange 0x102351 [0x89, 0xf9]
      step := mov_r32_r32_effect_step 0x102351 0xf9 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2351 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 1) (.location (.reg 7))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x102353 0x102356 [.add (.reg 0) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x102353 0x102356 (addR32R32Effect 0x102353 3 0 8) := {
      pre := (fun s ↦ s.RIP = 0x102353)
      code := codeRange 0x102353 [0x44, 0x1, 0xc0]
      step := add_r32_r32_rex_effect_step 0x102353 0x44 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2353 3 (by decide +kernel)
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
  simpa only [segment57, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment58_runs [Bindings] :
    RunWords 0x102356 0x10236c segment58 := by
  have h1 : RunWords 0x102356 0x102358 [.not (.reg 1)] := by
    let ex : InstructionExecution 0x102356 0x102358 (notR32Effect 0x102356 2 1) := {
      pre := (fun s ↦ s.RIP = 0x102356)
      code := codeRange 0x102356 [0xf7, 0xd1]
      step := not_r32_effect_step 0x102356 0xd1 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2356 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 1)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x102358 0x10235a [.or (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102358 0x10235a (Register.orR32R32Effect 0x102358 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x102358)
      code := codeRange 0x102358 [0x9, 0xc1]
      step := Register.or_r32_r32_effect_step 0x102358 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2358 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 1) (.location (.reg 0))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x10235a 0x10235d [.xor (.reg 1) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x10235a 0x10235d (xorR32R32Effect 0x10235a 3 1 8) := {
      pre := (fun s ↦ s.RIP = 0x10235a)
      code := codeRange 0x10235a [0x44, 0x31, 0xc1]
      step := xor_r32_r32_rex_effect_step 0x10235a 0x44 0xc1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x235a 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 1) (.location (.reg 8))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x10235d 0x10235f [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x10235d 0x10235f (addR32R32Effect 0x10235d 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x10235d)
      code := codeRange 0x10235d [0x1, 0xca]
      step := add_r32_r32_effect_step 0x10235d 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x235d 2 (by decide +kernel)
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
  have h5 : RunWords 0x10235f 0x102365 [.add (.reg 2) (.immediate 0xfe2ce6e0)] := by
    let ex : InstructionExecution 0x10235f 0x102365 (addR32Imm32Effect 0x10235f 6 2 0xfe2ce6e0) := {
      pre := (fun s ↦ s.RIP = 0x10235f)
      code := codeRange 0x10235f [0x81, 0xc2, 0xe0, 0xe6, 0x2c, 0xfe]
      step := add_r32_imm32_effect_step 0x10235f 0xc2 0xfe2ce6e0 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x235f 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0xfe2ce6e0)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102365 0x102368 [.rol (.reg 2) 10] := by
    let ex : InstructionExecution 0x102365 0x102368 (rolR32Effect 0x102365 3 2 10) := {
      pre := (fun s ↦ s.RIP = 0x102365)
      code := codeRange 0x102365 [0xc1, 0xc2, 0xa]
      step := rol_r32_imm8_effect_step 0x102365 0xc2 0xa (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2365 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 10) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102368 0x10236a [.add (.reg 7) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x102368 0x10236a (addR32R32Effect 0x102368 2 7 5) := {
      pre := (fun s ↦ s.RIP = 0x102368)
      code := codeRange 0x102368 [0x1, 0xef]
      step := add_r32_r32_effect_step 0x102368 0xef (by decide)
      present := fun hc ↦ program_text_slice hc 0x2368 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.reg 5))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x10236a 0x10236c [.add (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x10236a 0x10236c (addR32R32Effect 0x10236a 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x10236a)
      code := codeRange 0x10236a [0x1, 0xc2]
      step := add_r32_r32_effect_step 0x10236a 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x236a 2 (by decide +kernel)
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
  simpa only [segment58, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8)))))))

theorem segment59_runs [Bindings] :
    RunWords 0x10236c 0x102387 segment59 := by
  have h1 : RunWords 0x10236c 0x10236f [.mov (.reg 1) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x10236c 0x10236f (movR32R32Effect 0x10236c 3 1 8) := {
      pre := (fun s ↦ s.RIP = 0x10236c)
      code := codeRange 0x10236c [0x44, 0x89, 0xc1]
      step := mov_r32_r32_rex_effect_step 0x10236c 0x44 0xc1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x236c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 1) (.location (.reg 8))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x10236f 0x102371 [.not (.reg 1)] := by
    let ex : InstructionExecution 0x10236f 0x102371 (notR32Effect 0x10236f 2 1) := {
      pre := (fun s ↦ s.RIP = 0x10236f)
      code := codeRange 0x10236f [0xf7, 0xd1]
      step := not_r32_effect_step 0x10236f 0xd1 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x236f 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 1)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102371 0x102373 [.or (.reg 1) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102371 0x102373 (Register.orR32R32Effect 0x102371 2 1 2) := {
      pre := (fun s ↦ s.RIP = 0x102371)
      code := codeRange 0x102371 [0x9, 0xd1]
      step := Register.or_r32_r32_effect_step 0x102371 0xd1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2371 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 1) (.location (.reg 2))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102373 0x102375 [.xor (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x102373 0x102375 (xorR32R32Effect 0x102373 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x102373)
      code := codeRange 0x102373 [0x31, 0xc1]
      step := xor_r32_r32_effect_step 0x102373 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2373 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 1) (.location (.reg 0))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102375 0x102379 [.lea (.reg 9) (.reg 1) (.reg 7)] := by
    let ex : InstructionExecution 0x102375 0x102379 (Register.leaR32Effect 0x102375 4 9 (.sib 1
      (some 7) 0 .none)) := {
      pre := (fun s ↦ s.RIP = 0x102375)
      code := codeRange 0x102375 [0x44, 0x8d, 0xc, 0x39]
      step := Register.lea_r32_rex_effect_step 0x102375 0x44 (by simp [RexNoWPrefix]) 1 (.sib 1
        (some 7) 0 .none) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2375 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .lea (.reg 9) (.reg 1) (.reg 7)) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x102379 0x102380 [.add (.reg 9) (.immediate 0xa3014314)] := by
    let ex : InstructionExecution 0x102379 0x102380 (addR32Imm32Effect 0x102379 7 9 0xa3014314) := {
      pre := (fun s ↦ s.RIP = 0x102379)
      code := codeRange 0x102379 [0x41, 0x81, 0xc1, 0x14, 0x43, 0x1, 0xa3]
      step := add_r32_imm32_rex_effect_step 0x102379 0x41 0xc1 0xa3014314 (by simp [RexNoWPrefix])
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2379 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 9) (.immediate 0xa3014314)) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102380 0x102384 [.rol (.reg 9) 15] := by
    let ex : InstructionExecution 0x102380 0x102384 (rolR32Effect 0x102380 4 9 15) := {
      pre := (fun s ↦ s.RIP = 0x102380)
      code := codeRange 0x102380 [0x41, 0xc1, 0xc1, 0xf]
      step := rol_r32_imm8_rex_effect_step 0x102380 0x41 0xc1 0xf (by simp [RexNoWPrefix]) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2380 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 9) 15) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x102384 0x102387 [.add (.reg 9) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102384 0x102387 (addR32R32Effect 0x102384 3 9 2) := {
      pre := (fun s ↦ s.RIP = 0x102384)
      code := codeRange 0x102384 [0x41, 0x1, 0xd1]
      step := add_r32_r32_rex_effect_step 0x102384 0x41 0xd1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2384 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 9) (.location (.reg 2))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment59, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8)))))))

theorem segment60_runs [Bindings] :
    RunWords 0x102387 0x1023ab segment60 := by
  have h1 : RunWords 0x102387 0x10238c [.add (.reg 8) (.location (.stack 20))] := by
    let ex : InstructionExecution 0x102387 0x10238c (addR32M32Effect 0x102387 5 8 (.sib 4 none 0
      (.d8 0x14))) := {
      pre := (LoadPre 0x102387 (fun s ↦ ((.sib 4 none 0 (.d8 0x14)) : AddrMode).addr s (0x102387 +
        5)) 4)
      code := codeRange 0x102387 [0x44, 0x3, 0x44, 0x24, 0x14]
      step := add_r32_m32_effect_step 0x102387 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8
        0x14)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2387 5 (by decide +kernel)
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
    apply ex.run_reg (instruction := .add (.reg 8) (.location (.stack 20))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x10238c 0x10238e [.mov (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x10238c 0x10238e (movR32R32Effect 0x10238c 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x10238c)
      code := codeRange 0x10238c [0x89, 0xc1]
      step := mov_r32_r32_effect_step 0x10238c 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x238c 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 1) (.location (.reg 0))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x10238e 0x102390 [.not (.reg 1)] := by
    let ex : InstructionExecution 0x10238e 0x102390 (notR32Effect 0x10238e 2 1) := {
      pre := (fun s ↦ s.RIP = 0x10238e)
      code := codeRange 0x10238e [0xf7, 0xd1]
      step := not_r32_effect_step 0x10238e 0xd1 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x238e 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 1)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102390 0x102393 [.or (.reg 1) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x102390 0x102393 (Register.orR32R32Effect 0x102390 3 1 9) := {
      pre := (fun s ↦ s.RIP = 0x102390)
      code := codeRange 0x102390 [0x44, 0x9, 0xc9]
      step := Register.or_r32_r32_rex_effect_step 0x102390 0x44 0xc9 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x2390 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 1) (.location (.reg 9))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x102393 0x102395 [.xor (.reg 1) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102393 0x102395 (xorR32R32Effect 0x102393 2 1 2) := {
      pre := (fun s ↦ s.RIP = 0x102393)
      code := codeRange 0x102393 [0x31, 0xd1]
      step := xor_r32_r32_effect_step 0x102393 0xd1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x2393 2 (by decide +kernel)
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
  have h6 : RunWords 0x102395 0x102399 [.lea (.reg 7) (.reg 1) (.reg 8)] := by
    let ex : InstructionExecution 0x102395 0x102399 (Register.leaR32Effect 0x102395 4 7 (.sib 1
      (some 8) 0 .none)) := {
      pre := (fun s ↦ s.RIP = 0x102395)
      code := codeRange 0x102395 [0x42, 0x8d, 0x3c, 0x1]
      step := Register.lea_r32_rex_effect_step 0x102395 0x42 (by simp [RexNoWPrefix]) 7 (.sib 1
        (some 8) 0 .none) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2395 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .lea (.reg 7) (.reg 1) (.reg 8)) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102399 0x10239f [.add (.reg 7) (.immediate 0x4e0811a1)] := by
    let ex : InstructionExecution 0x102399 0x10239f (addR32Imm32Effect 0x102399 6 7 0x4e0811a1) := {
      pre := (fun s ↦ s.RIP = 0x102399)
      code := codeRange 0x102399 [0x81, 0xc7, 0xa1, 0x11, 0x8, 0x4e]
      step := add_r32_imm32_effect_step 0x102399 0xc7 0x4e0811a1 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2399 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.immediate 0x4e0811a1)) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x10239f 0x1023a2 [.rol (.reg 7) 21] := by
    let ex : InstructionExecution 0x10239f 0x1023a2 (rolR32Effect 0x10239f 3 7 21) := {
      pre := (fun s ↦ s.RIP = 0x10239f)
      code := codeRange 0x10239f [0xc1, 0xc7, 0x15]
      step := rol_r32_imm8_effect_step 0x10239f 0xc7 0x15 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x239f 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 7) 21) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x1023a2 0x1023a6 [.add (.reg 0) (.location (.stack 28))] := by
    let ex : InstructionExecution 0x1023a2 0x1023a6 (addR32M32Effect 0x1023a2 4 0 (.sib 4 none 0
      (.d8 0x1c))) := {
      pre := (LoadPre 0x1023a2 (fun s ↦ ((.sib 4 none 0 (.d8 0x1c)) : AddrMode).addr s (0x1023a2 +
        4)) 4)
      code := codeRange 0x1023a2 [0x3, 0x44, 0x24, 0x1c]
      step := add_r32_m32_noRex_effect_step 0x1023a2 0 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23a2 4 (by decide +kernel)
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
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.stack 28))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x1023a6 0x1023a8 [.mov (.reg 1) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1023a6 0x1023a8 (movR32R32Effect 0x1023a6 2 1 2) := {
      pre := (fun s ↦ s.RIP = 0x1023a6)
      code := codeRange 0x1023a6 [0x89, 0xd1]
      step := mov_r32_r32_effect_step 0x1023a6 0xd1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x23a6 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 1) (.location (.reg 2))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x1023a8 0x1023ab [.add (.reg 7) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x1023a8 0x1023ab (addR32R32Effect 0x1023a8 3 7 9) := {
      pre := (fun s ↦ s.RIP = 0x1023a8)
      code := codeRange 0x1023a8 [0x44, 0x1, 0xcf]
      step := add_r32_r32_rex_effect_step 0x1023a8 0x44 0xcf (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23a8 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.reg 9))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment60, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment61_runs [Bindings] :
    RunWords 0x1023ab 0x1023c3 segment61 := by
  have h1 : RunWords 0x1023ab 0x1023ad [.not (.reg 1)] := by
    let ex : InstructionExecution 0x1023ab 0x1023ad (notR32Effect 0x1023ab 2 1) := {
      pre := (fun s ↦ s.RIP = 0x1023ab)
      code := codeRange 0x1023ab [0xf7, 0xd1]
      step := not_r32_effect_step 0x1023ab 0xd1 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23ab 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 1)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1023ad 0x1023af [.or (.reg 1) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x1023ad 0x1023af (Register.orR32R32Effect 0x1023ad 2 1 7) := {
      pre := (fun s ↦ s.RIP = 0x1023ad)
      code := codeRange 0x1023ad [0x9, 0xf9]
      step := Register.or_r32_r32_effect_step 0x1023ad 0xf9 (by decide)
      present := fun hc ↦ program_text_slice hc 0x23ad 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 1) (.location (.reg 7))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1023af 0x1023b2 [.xor (.reg 1) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x1023af 0x1023b2 (xorR32R32Effect 0x1023af 3 1 9) := {
      pre := (fun s ↦ s.RIP = 0x1023af)
      code := codeRange 0x1023af [0x44, 0x31, 0xc9]
      step := xor_r32_r32_rex_effect_step 0x1023af 0x44 0xc9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23af 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 1) (.location (.reg 9))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1023b2 0x1023b4 [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1023b2 0x1023b4 (addR32R32Effect 0x1023b2 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x1023b2)
      code := codeRange 0x1023b2 [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x1023b2 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x23b2 2 (by decide +kernel)
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
  have h5 : RunWords 0x1023b4 0x1023ba [.add (.reg 1) (.immediate 0xf7537e82)] := by
    let ex : InstructionExecution 0x1023b4 0x1023ba (addR32Imm32Effect 0x1023b4 6 1 0xf7537e82) := {
      pre := (fun s ↦ s.RIP = 0x1023b4)
      code := codeRange 0x1023b4 [0x81, 0xc1, 0x82, 0x7e, 0x53, 0xf7]
      step := add_r32_imm32_effect_step 0x1023b4 0xc1 0xf7537e82 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23b4 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0xf7537e82)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x1023ba 0x1023bd [.rol (.reg 1) 6] := by
    let ex : InstructionExecution 0x1023ba 0x1023bd (rolR32Effect 0x1023ba 3 1 6) := {
      pre := (fun s ↦ s.RIP = 0x1023ba)
      code := codeRange 0x1023ba [0xc1, 0xc1, 0x6]
      step := rol_r32_imm8_effect_step 0x1023ba 0xc1 0x6 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23ba 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 6) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1023bd 0x1023c1 [.add (.reg 2) (.location (.stack 32))] := by
    let ex : InstructionExecution 0x1023bd 0x1023c1 (addR32M32Effect 0x1023bd 4 2 (.sib 4 none 0
      (.d8 0x20))) := {
      pre := (LoadPre 0x1023bd (fun s ↦ ((.sib 4 none 0 (.d8 0x20)) : AddrMode).addr s (0x1023bd +
        4)) 4)
      code := codeRange 0x1023bd [0x3, 0x54, 0x24, 0x20]
      step := add_r32_m32_noRex_effect_step 0x1023bd 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23bd 4 (by decide +kernel)
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
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.stack 32))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1023c1 0x1023c3 [.add (.reg 1) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x1023c1 0x1023c3 (addR32R32Effect 0x1023c1 2 1 7) := {
      pre := (fun s ↦ s.RIP = 0x1023c1)
      code := codeRange 0x1023c1 [0x1, 0xf9]
      step := add_r32_r32_effect_step 0x1023c1 0xf9 (by decide)
      present := fun hc ↦ program_text_slice hc 0x23c1 2 (by decide +kernel)
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
  simpa only [segment61, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8)))))))

theorem segment62_runs [Bindings] :
    RunWords 0x1023c3 0x1023d8 segment62 := by
  have h1 : RunWords 0x1023c3 0x1023c6 [.mov (.reg 0) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x1023c3 0x1023c6 (movR32R32Effect 0x1023c3 3 0 9) := {
      pre := (fun s ↦ s.RIP = 0x1023c3)
      code := codeRange 0x1023c3 [0x44, 0x89, 0xc8]
      step := mov_r32_r32_rex_effect_step 0x1023c3 0x44 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23c3 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 0) (.location (.reg 9))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1023c6 0x1023c8 [.not (.reg 0)] := by
    let ex : InstructionExecution 0x1023c6 0x1023c8 (notR32Effect 0x1023c6 2 0) := {
      pre := (fun s ↦ s.RIP = 0x1023c6)
      code := codeRange 0x1023c6 [0xf7, 0xd0]
      step := not_r32_effect_step 0x1023c6 0xd0 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23c6 2 (by decide +kernel)
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
  have h3 : RunWords 0x1023c8 0x1023ca [.or (.reg 0) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1023c8 0x1023ca (Register.orR32R32Effect 0x1023c8 2 0 1) := {
      pre := (fun s ↦ s.RIP = 0x1023c8)
      code := codeRange 0x1023c8 [0x9, 0xc8]
      step := Register.or_r32_r32_effect_step 0x1023c8 0xc8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x23c8 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 0) (.location (.reg 1))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x1023ca 0x1023cc [.xor (.reg 0) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x1023ca 0x1023cc (xorR32R32Effect 0x1023ca 2 0 7) := {
      pre := (fun s ↦ s.RIP = 0x1023ca)
      code := codeRange 0x1023ca [0x31, 0xf8]
      step := xor_r32_r32_effect_step 0x1023ca 0xf8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x23ca 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 0) (.location (.reg 7))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1023cc 0x1023ce [.add (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1023cc 0x1023ce (addR32R32Effect 0x1023cc 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x1023cc)
      code := codeRange 0x1023cc [0x1, 0xd0]
      step := add_r32_r32_effect_step 0x1023cc 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x23cc 2 (by decide +kernel)
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
  have h6 : RunWords 0x1023ce 0x1023d3 [.add (.reg 0) (.immediate 0xbd3af235)] := by
    let ex : InstructionExecution 0x1023ce 0x1023d3 (addR32Imm32Effect 0x1023ce 5 0 0xbd3af235) := {
      pre := (fun s ↦ s.RIP = 0x1023ce)
      code := codeRange 0x1023ce [0x5, 0x35, 0xf2, 0x3a, 0xbd]
      step := Register.add_eax_imm32_effect_step 0x1023ce 0xbd3af235
      present := fun hc ↦ program_text_slice hc 0x23ce 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0xbd3af235)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1023d3 0x1023d6 [.rol (.reg 0) 10] := by
    let ex : InstructionExecution 0x1023d3 0x1023d6 (rolR32Effect 0x1023d3 3 0 10) := {
      pre := (fun s ↦ s.RIP = 0x1023d3)
      code := codeRange 0x1023d3 [0xc1, 0xc0, 0xa]
      step := rol_r32_imm8_effect_step 0x1023d3 0xc0 0xa (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23d3 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 10) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1023d6 0x1023d8 [.add (.reg 0) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1023d6 0x1023d8 (addR32R32Effect 0x1023d6 2 0 1) := {
      pre := (fun s ↦ s.RIP = 0x1023d6)
      code := codeRange 0x1023d6 [0x1, 0xc8]
      step := add_r32_r32_effect_step 0x1023d6 0xc8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x23d6 2 (by decide +kernel)
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
  simpa only [segment62, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8)))))))

theorem segment63_runs [Bindings] :
    RunWords 0x1023d8 0x1023fb segment63 := by
  have h1 : RunWords 0x1023d8 0x1023db [.add (.reg 9) (.location (.reg 13))] := by
    let ex : InstructionExecution 0x1023d8 0x1023db (addR32R32Effect 0x1023d8 3 9 13) := {
      pre := (fun s ↦ s.RIP = 0x1023d8)
      code := codeRange 0x1023d8 [0x45, 0x1, 0xe9]
      step := add_r32_r32_rex_effect_step 0x1023d8 0x45 0xe9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23d8 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 9) (.location (.reg 13))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1023db 0x1023dd [.mov (.reg 2) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x1023db 0x1023dd (movR32R32Effect 0x1023db 2 2 7) := {
      pre := (fun s ↦ s.RIP = 0x1023db)
      code := codeRange 0x1023db [0x89, 0xfa]
      step := mov_r32_r32_effect_step 0x1023db 0xfa (by decide)
      present := fun hc ↦ program_text_slice hc 0x23db 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 2) (.location (.reg 7))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x1023dd 0x1023df [.not (.reg 2)] := by
    let ex : InstructionExecution 0x1023dd 0x1023df (notR32Effect 0x1023dd 2 2) := {
      pre := (fun s ↦ s.RIP = 0x1023dd)
      code := codeRange 0x1023dd [0xf7, 0xd2]
      step := not_r32_effect_step 0x1023dd 0xd2 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23dd 2 (by decide +kernel)
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
  have h4 : RunWords 0x1023df 0x1023e1 [.or (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1023df 0x1023e1 (Register.orR32R32Effect 0x1023df 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x1023df)
      code := codeRange 0x1023df [0x9, 0xc2]
      step := Register.or_r32_r32_effect_step 0x1023df 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x23df 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 2) (.location (.reg 0))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x1023e1 0x1023e3 [.xor (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1023e1 0x1023e3 (xorR32R32Effect 0x1023e1 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x1023e1)
      code := codeRange 0x1023e1 [0x31, 0xca]
      step := xor_r32_r32_effect_step 0x1023e1 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x23e1 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 2) (.location (.reg 1))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x1023e3 0x1023e6 [.add (.reg 2) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x1023e3 0x1023e6 (addR32R32Effect 0x1023e3 3 2 9) := {
      pre := (fun s ↦ s.RIP = 0x1023e3)
      code := codeRange 0x1023e3 [0x44, 0x1, 0xca]
      step := add_r32_r32_rex_effect_step 0x1023e3 0x44 0xca (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23e3 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 9))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x1023e6 0x1023ec [.add (.reg 2) (.immediate 0x2ad7d2bb)] := by
    let ex : InstructionExecution 0x1023e6 0x1023ec (addR32Imm32Effect 0x1023e6 6 2 0x2ad7d2bb) := {
      pre := (fun s ↦ s.RIP = 0x1023e6)
      code := codeRange 0x1023e6 [0x81, 0xc2, 0xbb, 0xd2, 0xd7, 0x2a]
      step := add_r32_imm32_effect_step 0x1023e6 0xc2 0x2ad7d2bb (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23e6 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0x2ad7d2bb)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x1023ec 0x1023ef [.rol (.reg 2) 15] := by
    let ex : InstructionExecution 0x1023ec 0x1023ef (rolR32Effect 0x1023ec 3 2 15) := {
      pre := (fun s ↦ s.RIP = 0x1023ec)
      code := codeRange 0x1023ec [0xc1, 0xc2, 0xf]
      step := rol_r32_imm8_effect_step 0x1023ec 0xc2 0xf (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23ec 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 15) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x1023ef 0x1023f3 [.add (.reg 7) (.location (.stack 4))] := by
    let ex : InstructionExecution 0x1023ef 0x1023f3 (addR32M32Effect 0x1023ef 4 7 (.sib 4 none 0
      (.d8 0x4))) := {
      pre := (LoadPre 0x1023ef (fun s ↦ ((.sib 4 none 0 (.d8 0x4)) : AddrMode).addr s (0x1023ef +
        4)) 4)
      code := codeRange 0x1023ef [0x3, 0x7c, 0x24, 0x4]
      step := add_r32_m32_noRex_effect_step 0x1023ef 7 (.sib 4 none 0 (.d8 0x4)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23ef 4 (by decide +kernel)
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
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.stack 4))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x1023f3 0x1023f6 [.mov (.reg 8) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x1023f3 0x1023f6 (movR32R32Effect 0x1023f3 3 8 1) := {
      pre := (fun s ↦ s.RIP = 0x1023f3)
      code := codeRange 0x1023f3 [0x41, 0x89, 0xc8]
      step := mov_r32_r32_rex_effect_step 0x1023f3 0x41 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23f3 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.reg 1))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x1023f6 0x1023f9 [.not (.reg 8)] := by
    let ex : InstructionExecution 0x1023f6 0x1023f9 (notR32Effect 0x1023f6 3 8) := {
      pre := (fun s ↦ s.RIP = 0x1023f6)
      code := codeRange 0x1023f6 [0x41, 0xf7, 0xd0]
      step := not_r32_rex_effect_step 0x1023f6 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x23f6 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 8)) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x1023f9 0x1023fb [.add (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1023f9 0x1023fb (addR32R32Effect 0x1023f9 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x1023f9)
      code := codeRange 0x1023f9 [0x1, 0xc2]
      step := add_r32_r32_effect_step 0x1023f9 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x23f9 2 (by decide +kernel)
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
  simpa only [segment63, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12)))))))))))

theorem segment64_runs [Bindings] :
    RunWords 0x1023fb 0x102427 segment64 := by
  have h1 : RunWords 0x1023fb 0x1023fe [.or (.reg 8) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x1023fb 0x1023fe (Register.orR32R32Effect 0x1023fb 3 8 2) := {
      pre := (fun s ↦ s.RIP = 0x1023fb)
      code := codeRange 0x1023fb [0x41, 0x9, 0xd0]
      step := Register.or_r32_r32_rex_effect_step 0x1023fb 0x41 0xd0 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x23fb 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 8) (.location (.reg 2))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x1023fe 0x102401 [.xor (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x1023fe 0x102401 (xorR32R32Effect 0x1023fe 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x1023fe)
      code := codeRange 0x1023fe [0x41, 0x31, 0xc0]
      step := xor_r32_r32_rex_effect_step 0x1023fe 0x41 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x23fe 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 8) (.location (.reg 0))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x102401 0x102404 [.add (.reg 7) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x102401 0x102404 (addR32R32Effect 0x102401 3 7 8) := {
      pre := (fun s ↦ s.RIP = 0x102401)
      code := codeRange 0x102401 [0x44, 0x1, 0xc7]
      step := add_r32_r32_rex_effect_step 0x102401 0x44 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2401 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.reg 8))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x102404 0x10240a [.add (.reg 7) (.immediate 0xeb86d391)] := by
    let ex : InstructionExecution 0x102404 0x10240a (addR32Imm32Effect 0x102404 6 7 0xeb86d391) := {
      pre := (fun s ↦ s.RIP = 0x102404)
      code := codeRange 0x102404 [0x81, 0xc7, 0x91, 0xd3, 0x86, 0xeb]
      step := add_r32_imm32_effect_step 0x102404 0xc7 0xeb86d391 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2404 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.immediate 0xeb86d391)) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x10240a 0x10240f [.mov (.reg 8) (.location (.stack 8))] := by
    let ex : InstructionExecution 0x10240a 0x10240f (movR64M64Effect 0x10240a 8 (.sib 4 none 0 (.d8
      0x8))) := {
      pre := (LoadPre 0x10240a (fun s ↦ ((.sib 4 none 0 (.d8 0x8)) : AddrMode).addr s (0x10240a +
        5)) 8)
      code := codeRange 0x10240a [0x4c, 0x8b, 0x44, 0x24, 0x8]
      step := mov_r64_m64_effect_step 0x10240a 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8
        0x8)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x240a 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 8 8 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.stack 8))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x10240f 0x102413 [.add (.reg 1) (.location (.stack 60))] := by
    let ex : InstructionExecution 0x10240f 0x102413 (addR32M32Effect 0x10240f 4 1 (.sib 4 none 0
      (.d8 0x3c))) := {
      pre := (LoadPre 0x10240f (fun s ↦ ((.sib 4 none 0 (.d8 0x3c)) : AddrMode).addr s (0x10240f +
        4)) 4)
      code := codeRange 0x10240f [0x3, 0x4c, 0x24, 0x3c]
      step := add_r32_m32_noRex_effect_step 0x10240f 1 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x240f 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 60 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.location (.stack 60))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x102413 0x102416 [.rol (.reg 7) 21] := by
    let ex : InstructionExecution 0x102413 0x102416 (rolR32Effect 0x102413 3 7 21) := {
      pre := (fun s ↦ s.RIP = 0x102413)
      code := codeRange 0x102413 [0xc1, 0xc7, 0x15]
      step := rol_r32_imm8_effect_step 0x102413 0xc7 0x15 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2413 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 7) 21) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x102416 0x102419 [.add (.reg 8) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x102416 0x102419 (addR32R32Effect 0x102416 3 8 2) := {
      pre := (fun s ↦ s.RIP = 0x102416)
      code := codeRange 0x102416 [0x41, 0x1, 0xd0]
      step := add_r32_r32_rex_effect_step 0x102416 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2416 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 8) (.location (.reg 2))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x102419 0x10241c [.add (.reg 8) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x102419 0x10241c (addR32R32Effect 0x102419 3 8 7) := {
      pre := (fun s ↦ s.RIP = 0x102419)
      code := codeRange 0x102419 [0x41, 0x1, 0xf8]
      step := add_r32_r32_rex_effect_step 0x102419 0x41 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2419 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 8) (.location (.reg 7))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x10241c 0x102420 [.add (.reg 2) (.location (.stack 120))] := by
    let ex : InstructionExecution 0x10241c 0x102420 (addR32M32Effect 0x10241c 4 2 (.sib 4 none 0
      (.d8 0x78))) := {
      pre := (LoadPre 0x10241c (fun s ↦ ((.sib 4 none 0 (.d8 0x78)) : AddrMode).addr s (0x10241c +
        4)) 4)
      code := codeRange 0x10241c [0x3, 0x54, 0x24, 0x78]
      step := add_r32_m32_noRex_effect_step 0x10241c 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x241c 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 120 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.stack 120))) (dst := 2) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x102420 0x102427 [.add (.reg 0) (.location (.stack 128))] := by
    let ex : InstructionExecution 0x102420 0x102427 (addR32M32Effect 0x102420 7 0 (.sib 4 none 0
      (.d32 0x80))) := {
      pre := (LoadPre 0x102420 (fun s ↦ ((.sib 4 none 0 (.d32 0x80)) : AddrMode).addr s (0x102420 +
        7)) 4)
      code := codeRange 0x102420 [0x3, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0]
      step := add_r32_m32_noRex_effect_step 0x102420 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x2420 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 128 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.stack 128))) (dst := 0) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment64, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

end Md5.Proofs.Block.Rounds
