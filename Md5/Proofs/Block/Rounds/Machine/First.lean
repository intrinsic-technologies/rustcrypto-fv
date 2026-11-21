import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.Block.Rounds.Step
import Md5.Proofs.Block.Rounds.Address
import Md5.Proofs.Block.Rounds.Interface
import Md5.Proofs.Block.Rounds.Register
import Md5.Proofs.Block.Rounds.Load
import Md5.Proofs.Block.Rounds.Store

namespace Md5.Proofs.Block.Rounds
open X86 X86.Machine X86.UserProcess X86Proofs

theorem segment1_runs [Bindings] :
    RunWords 0x101be0 0x101c1d segment1 := by
  have h1 : RunWords 0x101be0 0x101be5 [.mov (.stack 8) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101be0 0x101be5 (movM64R64Effect 0x101be0 8 (.sib 4 none 0 (.d8
      0x8))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101be0 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x8)) :
        AddrMode).addr s (0x101be0 + 5)) 8)
      code := codeRange 0x101be0 [0x4c, 0x89, 0x44, 0x24, 0x8]
      step := Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step 0x101be0 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0
        (.d8 0x8)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1be0 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 8) (length := 8) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1be0 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack64 (instruction := .mov (.stack 8) (.location (.reg 8))) (dst := 8)
      (value := fun s ↦ (Operand.reg 8 : Operand 64).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h2 : RunWords 0x101be5 0x101be7 [.mov (.reg 7) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101be5 0x101be7 (movR32R32Effect 0x101be5 2 7 2) := {
      pre := (fun s ↦ s.RIP = 0x101be5)
      code := codeRange 0x101be5 [0x89, 0xd7]
      step := mov_r32_r32_effect_step 0x101be5 0xd7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1be5 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 7) (.location (.reg 2))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101be7 0x101be9 [.mov (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101be7 0x101be9 (movR32R32Effect 0x101be7 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x101be7)
      code := codeRange 0x101be7 [0x89, 0xc2]
      step := mov_r32_r32_effect_step 0x101be7 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1be7 2 (by decide +kernel)
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
  have h4 : RunWords 0x101be9 0x101bec [.mov (.reg 9) (.location (.input 0))] := by
    let ex : InstructionExecution 0x101be9 0x101bec (movR32M32Effect 0x101be9 9 (.base 6 .none)) :=
      {
      pre := (LoadPre 0x101be9 (fun s ↦ ((.base 6 .none) : AddrMode).addr s (0x101be9 + 3)) 4)
      code := codeRange 0x101be9 [0x44, 0x8b, 0xe]
      step := mov_r32_m32_effect_step 0x101be9 0x44 (by simp [RexNoWPrefix]) 1 (.base 6 .none) (by
        decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1be9 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        simpa only [BitVec.add_zero] using hd.readable_input 0 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 9) (.location (.input 0))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101bec 0x101bf1 [.mov (.stack 88) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x101bec 0x101bf1 (movM64R64Effect 0x101bec 9 (.sib 4 none 0 (.d8
      0x58))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101bec 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x58)) :
        AddrMode).addr s (0x101bec + 5)) 8)
      code := codeRange 0x101bec [0x4c, 0x89, 0x4c, 0x24, 0x58]
      step := Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step 0x101bec 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0
        (.d8 0x58)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1bec 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 88) (length := 8) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1bec 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack64 (instruction := .mov (.stack 88) (.location (.reg 9))) (dst := 88)
      (value := fun s ↦ (Operand.reg 9 : Operand 64).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h6 : RunWords 0x101bf1 0x101bf3 [.mov (.reg 0) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101bf1 0x101bf3 (movR32R32Effect 0x101bf1 2 0 7) := {
      pre := (fun s ↦ s.RIP = 0x101bf1)
      code := codeRange 0x101bf1 [0x89, 0xf8]
      step := mov_r32_r32_effect_step 0x101bf1 0xf8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1bf1 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 0) (.location (.reg 7))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101bf3 0x101bf5 [.xor (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101bf3 0x101bf5 (xorR32R32Effect 0x101bf3 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x101bf3)
      code := codeRange 0x101bf3 [0x31, 0xd0]
      step := xor_r32_r32_effect_step 0x101bf3 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1bf3 2 (by decide +kernel)
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
  have h8 : RunWords 0x101bf5 0x101bf9 [.mov (.stack 60) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101bf5 0x101bf9 (Store.movM32R32NoRexEffect 0x101bf5 1 (.sib 4
      none 0 (.d8 0x3c))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101bf5 4 (fun s ↦ ((.sib 4 none 0 (.d8 0x3c)) :
        AddrMode).addr s (0x101bf5 + 4)) 4)
      code := codeRange 0x101bf5 [0x89, 0x4c, 0x24, 0x3c]
      step := Store.mov_m32_r32_noRex_effect_step 0x101bf5 1 (.sib 4 none 0 (.d8 0x3c)) (by decide)
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1bf5 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 60) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1bf5 4 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 60) (.location (.reg 1))) (dst := 60)
      (value := fun s ↦ (Operand.reg 1 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h9 : RunWords 0x101bf9 0x101bfc [.and (.reg 0) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101bf9 0x101bfc (andR32R32Effect 0x101bf9 3 0 8) := {
      pre := (fun s ↦ s.RIP = 0x101bf9)
      code := codeRange 0x101bf9 [0x44, 0x21, 0xc0]
      step := and_r32_r32_rex_effect_step 0x101bf9 0x44 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1bf9 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 0) (.location (.reg 8))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101bfc 0x101bfe [.xor (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101bfc 0x101bfe (xorR32R32Effect 0x101bfc 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x101bfc)
      code := codeRange 0x101bfc [0x31, 0xd0]
      step := xor_r32_r32_effect_step 0x101bfc 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1bfc 2 (by decide +kernel)
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
  have h11 : RunWords 0x101bfe 0x101c01 [.mov (.reg 8) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101bfe 0x101c01 (movR64R64Effect 0x101bfe 8 2) := {
      pre := (fun s ↦ s.RIP = 0x101bfe)
      code := codeRange 0x101bfe [0x49, 0x89, 0xd0]
      step := mov_r64_r64_effect_step 0x101bfe 0x49 0xd0 (by simp [RexWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1bfe 3 (by decide +kernel)
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
  have h12 : RunWords 0x101c01 0x101c09 [.mov (.stack 128) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101c01 0x101c09 (movM64R64Effect 0x101c01 2 (.sib 4 none 0 (.d32
      0x80))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101c01 8 (fun s ↦ ((.sib 4 none 0 (.d32 0x80)) :
        AddrMode).addr s (0x101c01 + 8)) 8)
      code := codeRange 0x101c01 [0x48, 0x89, 0x94, 0x24, 0x80, 0x0, 0x0, 0x0]
      step := Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step 0x101c01 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0
        (.d32 0x80)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c01 8 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 128) (length := 8) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1c01 8 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack64 (instruction := .mov (.stack 128) (.location (.reg 2))) (dst := 128)
      (value := fun s ↦ (Operand.reg 2 : Operand 64).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h13 : RunWords 0x101c09 0x101c0b [.add (.reg 0) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101c09 0x101c0b (addR32R32Effect 0x101c09 2 0 1) := {
      pre := (fun s ↦ s.RIP = 0x101c09)
      code := codeRange 0x101c09 [0x1, 0xc8]
      step := add_r32_r32_effect_step 0x101c09 0xc8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c09 2 (by decide +kernel)
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
  have h14 : RunWords 0x101c0b 0x101c0e [.mov (.reg 3) (.location (.input 1))] := by
    let ex : InstructionExecution 0x101c0b 0x101c0e (movR32M32NoRexEffect 0x101c0b 3 (.base 6 (.d8
      0x4))) := {
      pre := (LoadPre 0x101c0b (fun s ↦ ((.base 6 (.d8 0x4)) : AddrMode).addr s (0x101c0b + 3)) 4)
      code := codeRange 0x101c0b [0x8b, 0x5e, 0x4]
      step := mov_r32_m32_noRex_effect_step 0x101c0b 3 (.base 6 (.d8 0x4)) (by decide) (by decide)
        (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c0b 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 4 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 3) (.location (.input 1))) (dst := 3) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h15 : RunWords 0x101c0e 0x101c11 [.add (.reg 0) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x101c0e 0x101c11 (addR32R32Effect 0x101c0e 3 0 9) := {
      pre := (fun s ↦ s.RIP = 0x101c0e)
      code := codeRange 0x101c0e [0x44, 0x1, 0xc8]
      step := add_r32_r32_rex_effect_step 0x101c0e 0x44 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c0e 3 (by decide +kernel)
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
  have h16 : RunWords 0x101c11 0x101c16 [.add (.reg 0) (.immediate 0xd76aa478)] := by
    let ex : InstructionExecution 0x101c11 0x101c16 (addR32Imm32Effect 0x101c11 5 0 0xd76aa478) := {
      pre := (fun s ↦ s.RIP = 0x101c11)
      code := codeRange 0x101c11 [0x5, 0x78, 0xa4, 0x6a, 0xd7]
      step := Register.add_eax_imm32_effect_step 0x101c11 0xd76aa478
      present := fun hc ↦ program_text_slice hc 0x1c11 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0xd76aa478)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h17 : RunWords 0x101c16 0x101c19 [.rol (.reg 0) 7] := by
    let ex : InstructionExecution 0x101c16 0x101c19 (rolR32Effect 0x101c16 3 0 7) := {
      pre := (fun s ↦ s.RIP = 0x101c16)
      code := codeRange 0x101c16 [0xc1, 0xc0, 0x7]
      step := rol_r32_imm8_effect_step 0x101c16 0xc0 0x7 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c16 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 7) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h18 : RunWords 0x101c19 0x101c1d [.add (.reg 0) (.location (.stack 8))] := by
    let ex : InstructionExecution 0x101c19 0x101c1d (addR32M32Effect 0x101c19 4 0 (.sib 4 none 0
      (.d8 0x8))) := {
      pre := (LoadPre 0x101c19 (fun s ↦ ((.sib 4 none 0 (.d8 0x8)) : AddrMode).addr s (0x101c19 +
        4)) 4)
      code := codeRange 0x101c19 [0x3, 0x44, 0x24, 0x8]
      step := add_r32_m32_noRex_effect_step 0x101c19 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c19 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 8 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.stack 8))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment1, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (h14.seq (h15.seq
    (h16.seq (h17.seq (h18)))))))))))))))))

theorem segment2_runs [Bindings] :
    RunWords 0x101c1d 0x101c51 segment2 := by
  have h1 : RunWords 0x101c1d 0x101c1f [.mov (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101c1d 0x101c1f (movR32R32Effect 0x101c1d 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x101c1d)
      code := codeRange 0x101c1d [0x89, 0xc1]
      step := mov_r32_r32_effect_step 0x101c1d 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c1d 2 (by decide +kernel)
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
  have h2 : RunWords 0x101c1f 0x101c21 [.mov (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101c1f 0x101c21 (movR32R32Effect 0x101c1f 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x101c1f)
      code := codeRange 0x101c1f [0x89, 0xc2]
      step := mov_r32_r32_effect_step 0x101c1f 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c1f 2 (by decide +kernel)
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
  have h3 : RunWords 0x101c21 0x101c23 [.not (.reg 2)] := by
    let ex : InstructionExecution 0x101c21 0x101c23 (notR32Effect 0x101c21 2 2) := {
      pre := (fun s ↦ s.RIP = 0x101c21)
      code := codeRange 0x101c21 [0xf7, 0xd2]
      step := not_r32_effect_step 0x101c21 0xd2 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c21 2 (by decide +kernel)
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
  have h4 : RunWords 0x101c23 0x101c27 [.and (.reg 1) (.location (.stack 8))] := by
    let ex : InstructionExecution 0x101c23 0x101c27 (andR32M32Effect 0x101c23 4 1 (.sib 4 none 0
      (.d8 0x8))) := {
      pre := (LoadPre 0x101c23 (fun s ↦ ((.sib 4 none 0 (.d8 0x8)) : AddrMode).addr s (0x101c23 +
        4)) 4)
      code := codeRange 0x101c23 [0x23, 0x4c, 0x24, 0x8]
      step := and_r32_m32_noRex_effect_step 0x101c23 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c23 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 8 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 1) (.location (.stack 8))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101c27 0x101c29 [.and (.reg 2) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101c27 0x101c29 (andR32R32Effect 0x101c27 2 2 7) := {
      pre := (fun s ↦ s.RIP = 0x101c27)
      code := codeRange 0x101c27 [0x21, 0xfa]
      step := and_r32_r32_effect_step 0x101c27 0xfa (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c27 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 2) (.location (.reg 7))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101c29 0x101c2c [.mov (.reg 9) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101c29 0x101c2c (movR64R64Effect 0x101c29 9 7) := {
      pre := (fun s ↦ s.RIP = 0x101c29)
      code := codeRange 0x101c29 [0x49, 0x89, 0xf9]
      step := mov_r64_r64_effect_step 0x101c29 0x49 0xf9 (by simp [RexWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c29 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 9) (.location (.reg 7))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101c2c 0x101c31 [.mov (.stack 120) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101c2c 0x101c31 (movM64R64Effect 0x101c2c 7 (.sib 4 none 0 (.d8
      0x78))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101c2c 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x78)) :
        AddrMode).addr s (0x101c2c + 5)) 8)
      code := codeRange 0x101c2c [0x48, 0x89, 0x7c, 0x24, 0x78]
      step := Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step 0x101c2c 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0
        (.d8 0x78)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c2c 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 120) (length := 8) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1c2c 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack64 (instruction := .mov (.stack 120) (.location (.reg 7))) (dst := 120)
      (value := fun s ↦ (Operand.reg 7 : Operand 64).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h8 : RunWords 0x101c31 0x101c36 [.mov (.stack 80) (.location (.reg 3))] := by
    let ex : InstructionExecution 0x101c31 0x101c36 (movM64R64Effect 0x101c31 3 (.sib 4 none 0 (.d8
      0x50))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101c31 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x50)) :
        AddrMode).addr s (0x101c31 + 5)) 8)
      code := codeRange 0x101c31 [0x48, 0x89, 0x5c, 0x24, 0x50]
      step := Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step 0x101c31 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0
        (.d8 0x50)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c31 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 80) (length := 8) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1c31 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack64 (instruction := .mov (.stack 80) (.location (.reg 3))) (dst := 80)
      (value := fun s ↦ (Operand.reg 3 : Operand 64).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h9 : RunWords 0x101c36 0x101c39 [.add (.reg 2) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101c36 0x101c39 (addR32R32Effect 0x101c36 3 2 8) := {
      pre := (fun s ↦ s.RIP = 0x101c36)
      code := codeRange 0x101c36 [0x44, 0x1, 0xc2]
      step := add_r32_r32_rex_effect_step 0x101c36 0x44 0xc2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c36 3 (by decide +kernel)
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
  have h10 : RunWords 0x101c39 0x101c3b [.add (.reg 2) (.location (.reg 3))] := by
    let ex : InstructionExecution 0x101c39 0x101c3b (addR32R32Effect 0x101c39 2 2 3) := {
      pre := (fun s ↦ s.RIP = 0x101c39)
      code := codeRange 0x101c39 [0x1, 0xda]
      step := add_r32_r32_effect_step 0x101c39 0xda (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c39 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.location (.reg 3))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101c3b 0x101c3f [.mov (.reg 8) (.location (.input 2))] := by
    let ex : InstructionExecution 0x101c3b 0x101c3f (movR32M32Effect 0x101c3b 8 (.base 6 (.d8 0x8)))
      := {
      pre := (LoadPre 0x101c3b (fun s ↦ ((.base 6 (.d8 0x8)) : AddrMode).addr s (0x101c3b + 4)) 4)
      code := codeRange 0x101c3b [0x44, 0x8b, 0x46, 0x8]
      step := mov_r32_m32_effect_step 0x101c3b 0x44 (by simp [RexNoWPrefix]) 0 (.base 6 (.d8 0x8))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c3b 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 8 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.input 2))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x101c3f 0x101c44 [.mov (.stack 112) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101c3f 0x101c44 (movM64R64Effect 0x101c3f 8 (.sib 4 none 0 (.d8
      0x70))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101c3f 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x70)) :
        AddrMode).addr s (0x101c3f + 5)) 8)
      code := codeRange 0x101c3f [0x4c, 0x89, 0x44, 0x24, 0x70]
      step := Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step 0x101c3f 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0
        (.d8 0x70)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c3f 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 112) (length := 8) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1c3f 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack64 (instruction := .mov (.stack 112) (.location (.reg 8))) (dst := 112)
      (value := fun s ↦ (Operand.reg 8 : Operand 64).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h13 : RunWords 0x101c44 0x101c46 [.add (.reg 1) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101c44 0x101c46 (addR32R32Effect 0x101c44 2 1 2) := {
      pre := (fun s ↦ s.RIP = 0x101c44)
      code := codeRange 0x101c44 [0x1, 0xd1]
      step := add_r32_r32_effect_step 0x101c44 0xd1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c44 2 (by decide +kernel)
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
  have h14 : RunWords 0x101c46 0x101c4c [.add (.reg 1) (.immediate 0xe8c7b756)] := by
    let ex : InstructionExecution 0x101c46 0x101c4c (addR32Imm32Effect 0x101c46 6 1 0xe8c7b756) := {
      pre := (fun s ↦ s.RIP = 0x101c46)
      code := codeRange 0x101c46 [0x81, 0xc1, 0x56, 0xb7, 0xc7, 0xe8]
      step := add_r32_imm32_effect_step 0x101c46 0xc1 0xe8c7b756 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c46 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0xe8c7b756)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h15 : RunWords 0x101c4c 0x101c4f [.rol (.reg 1) 12] := by
    let ex : InstructionExecution 0x101c4c 0x101c4f (rolR32Effect 0x101c4c 3 1 12) := {
      pre := (fun s ↦ s.RIP = 0x101c4c)
      code := codeRange 0x101c4c [0xc1, 0xc1, 0xc]
      step := rol_r32_imm8_effect_step 0x101c4c 0xc1 0xc (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c4c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 12) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h16 : RunWords 0x101c4f 0x101c51 [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101c4f 0x101c51 (addR32R32Effect 0x101c4f 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x101c4f)
      code := codeRange 0x101c4f [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x101c4f 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c4f 2 (by decide +kernel)
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
  simpa only [segment2, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (h14.seq (h15.seq
    (h16)))))))))))))))

theorem segment3_runs [Bindings] :
    RunWords 0x101c51 0x101c79 segment3 := by
  have h1 : RunWords 0x101c51 0x101c53 [.mov (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101c51 0x101c53 (movR32R32Effect 0x101c51 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x101c51)
      code := codeRange 0x101c51 [0x89, 0xca]
      step := mov_r32_r32_effect_step 0x101c51 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c51 2 (by decide +kernel)
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
  have h2 : RunWords 0x101c53 0x101c55 [.mov (.reg 7) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101c53 0x101c55 (movR32R32Effect 0x101c53 2 7 1) := {
      pre := (fun s ↦ s.RIP = 0x101c53)
      code := codeRange 0x101c53 [0x89, 0xcf]
      step := mov_r32_r32_effect_step 0x101c53 0xcf (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c53 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 7) (.location (.reg 1))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101c55 0x101c57 [.not (.reg 7)] := by
    let ex : InstructionExecution 0x101c55 0x101c57 (notR32Effect 0x101c55 2 7) := {
      pre := (fun s ↦ s.RIP = 0x101c55)
      code := codeRange 0x101c55 [0xf7, 0xd7]
      step := not_r32_effect_step 0x101c55 0xd7 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c55 2 (by decide +kernel)
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
  have h4 : RunWords 0x101c57 0x101c59 [.and (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101c57 0x101c59 (andR32R32Effect 0x101c57 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x101c57)
      code := codeRange 0x101c57 [0x21, 0xc2]
      step := and_r32_r32_effect_step 0x101c57 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c57 2 (by decide +kernel)
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
  have h5 : RunWords 0x101c59 0x101c5d [.and (.reg 7) (.location (.stack 8))] := by
    let ex : InstructionExecution 0x101c59 0x101c5d (andR32M32Effect 0x101c59 4 7 (.sib 4 none 0
      (.d8 0x8))) := {
      pre := (LoadPre 0x101c59 (fun s ↦ ((.sib 4 none 0 (.d8 0x8)) : AddrMode).addr s (0x101c59 +
        4)) 4)
      code := codeRange 0x101c59 [0x23, 0x7c, 0x24, 0x8]
      step := and_r32_m32_noRex_effect_step 0x101c59 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c59 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_stack 8 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 7) (.location (.stack 8))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101c5d 0x101c60 [.add (.reg 8) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x101c5d 0x101c60 (addR32R32Effect 0x101c5d 3 8 9) := {
      pre := (fun s ↦ s.RIP = 0x101c5d)
      code := codeRange 0x101c5d [0x45, 0x1, 0xc8]
      step := add_r32_r32_rex_effect_step 0x101c5d 0x45 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c5d 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 8) (.location (.reg 9))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101c60 0x101c63 [.add (.reg 7) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101c60 0x101c63 (addR32R32Effect 0x101c60 3 7 8) := {
      pre := (fun s ↦ s.RIP = 0x101c60)
      code := codeRange 0x101c60 [0x44, 0x1, 0xc7]
      step := add_r32_r32_rex_effect_step 0x101c60 0x44 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c60 3 (by decide +kernel)
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
  have h8 : RunWords 0x101c63 0x101c67 [.mov (.reg 10) (.location (.input 3))] := by
    let ex : InstructionExecution 0x101c63 0x101c67 (movR32M32Effect 0x101c63 10 (.base 6 (.d8
      0xc))) := {
      pre := (LoadPre 0x101c63 (fun s ↦ ((.base 6 (.d8 0xc)) : AddrMode).addr s (0x101c63 + 4)) 4)
      code := codeRange 0x101c63 [0x44, 0x8b, 0x56, 0xc]
      step := mov_r32_m32_effect_step 0x101c63 0x44 (by simp [RexNoWPrefix]) 2 (.base 6 (.d8 0xc))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c63 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 12 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.input 3))) (dst := 10) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101c67 0x101c6c [.mov (.stack 72) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101c67 0x101c6c (movM64R64Effect 0x101c67 10 (.sib 4 none 0 (.d8
      0x48))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101c67 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x48)) :
        AddrMode).addr s (0x101c67 + 5)) 8)
      code := codeRange 0x101c67 [0x4c, 0x89, 0x54, 0x24, 0x48]
      step := Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step 0x101c67 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0
        (.d8 0x48)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c67 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 72) (length := 8) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1c67 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack64 (instruction := .mov (.stack 72) (.location (.reg 10))) (dst := 72)
      (value := fun s ↦ (Operand.reg 10 : Operand 64).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h10 : RunWords 0x101c6c 0x101c6e [.add (.reg 2) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101c6c 0x101c6e (addR32R32Effect 0x101c6c 2 2 7) := {
      pre := (fun s ↦ s.RIP = 0x101c6c)
      code := codeRange 0x101c6c [0x1, 0xfa]
      step := add_r32_r32_effect_step 0x101c6c 0xfa (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c6c 2 (by decide +kernel)
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
  have h11 : RunWords 0x101c6e 0x101c74 [.add (.reg 2) (.immediate 0x242070db)] := by
    let ex : InstructionExecution 0x101c6e 0x101c74 (addR32Imm32Effect 0x101c6e 6 2 0x242070db) := {
      pre := (fun s ↦ s.RIP = 0x101c6e)
      code := codeRange 0x101c6e [0x81, 0xc2, 0xdb, 0x70, 0x20, 0x24]
      step := add_r32_imm32_effect_step 0x101c6e 0xc2 0x242070db (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c6e 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0x242070db)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x101c74 0x101c77 [.rol (.reg 2) 17] := by
    let ex : InstructionExecution 0x101c74 0x101c77 (rolR32Effect 0x101c74 3 2 17) := {
      pre := (fun s ↦ s.RIP = 0x101c74)
      code := codeRange 0x101c74 [0xc1, 0xc2, 0x11]
      step := rol_r32_imm8_effect_step 0x101c74 0xc2 0x11 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c74 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 17) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h13 : RunWords 0x101c77 0x101c79 [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101c77 0x101c79 (addR32R32Effect 0x101c77 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x101c77)
      code := codeRange 0x101c77 [0x1, 0xca]
      step := add_r32_r32_effect_step 0x101c77 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c77 2 (by decide +kernel)
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
  simpa only [segment3, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13))))))))))))

theorem segment4_runs [Bindings] :
    RunWords 0x101c79 0x101ca8 segment4 := by
  have h1 : RunWords 0x101c79 0x101c7b [.mov (.reg 7) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101c79 0x101c7b (movR32R32Effect 0x101c79 2 7 2) := {
      pre := (fun s ↦ s.RIP = 0x101c79)
      code := codeRange 0x101c79 [0x89, 0xd7]
      step := mov_r32_r32_effect_step 0x101c79 0xd7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c79 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 7) (.location (.reg 2))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x101c7b 0x101c7e [.mov (.reg 8) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101c7b 0x101c7e (movR32R32Effect 0x101c7b 3 8 2) := {
      pre := (fun s ↦ s.RIP = 0x101c7b)
      code := codeRange 0x101c7b [0x41, 0x89, 0xd0]
      step := mov_r32_r32_rex_effect_step 0x101c7b 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c7b 3 (by decide +kernel)
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
  have h3 : RunWords 0x101c7e 0x101c81 [.not (.reg 8)] := by
    let ex : InstructionExecution 0x101c7e 0x101c81 (notR32Effect 0x101c7e 3 8) := {
      pre := (fun s ↦ s.RIP = 0x101c7e)
      code := codeRange 0x101c7e [0x41, 0xf7, 0xd0]
      step := not_r32_rex_effect_step 0x101c7e 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1c7e 3 (by decide +kernel)
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
  have h4 : RunWords 0x101c81 0x101c83 [.and (.reg 7) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101c81 0x101c83 (andR32R32Effect 0x101c81 2 7 1) := {
      pre := (fun s ↦ s.RIP = 0x101c81)
      code := codeRange 0x101c81 [0x21, 0xcf]
      step := and_r32_r32_effect_step 0x101c81 0xcf (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c81 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 7) (.location (.reg 1))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101c83 0x101c86 [.and (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101c83 0x101c86 (andR32R32Effect 0x101c83 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x101c83)
      code := codeRange 0x101c83 [0x41, 0x21, 0xc0]
      step := and_r32_r32_rex_effect_step 0x101c83 0x41 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c83 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 8) (.location (.reg 0))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101c86 0x101c8b [.mov (.reg 9) (.location (.stack 8))] := by
    let ex : InstructionExecution 0x101c86 0x101c8b (movR64M64Effect 0x101c86 9 (.sib 4 none 0 (.d8
      0x8))) := {
      pre := (LoadPre 0x101c86 (fun s ↦ ((.sib 4 none 0 (.d8 0x8)) : AddrMode).addr s (0x101c86 +
        5)) 8)
      code := codeRange 0x101c86 [0x4c, 0x8b, 0x4c, 0x24, 0x8]
      step := mov_r64_m64_effect_step 0x101c86 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8
        0x8)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c86 5 (by decide +kernel)
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
    apply ex.run_reg (instruction := .mov (.reg 9) (.location (.stack 8))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101c8b 0x101c8e [.add (.reg 9) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101c8b 0x101c8e (addR32R32Effect 0x101c8b 3 9 10) := {
      pre := (fun s ↦ s.RIP = 0x101c8b)
      code := codeRange 0x101c8b [0x45, 0x1, 0xd1]
      step := add_r32_r32_rex_effect_step 0x101c8b 0x45 0xd1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c8b 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 9) (.location (.reg 10))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101c8e 0x101c91 [.add (.reg 8) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x101c8e 0x101c91 (addR32R32Effect 0x101c8e 3 8 9) := {
      pre := (fun s ↦ s.RIP = 0x101c8e)
      code := codeRange 0x101c8e [0x45, 0x1, 0xc8]
      step := add_r32_r32_rex_effect_step 0x101c8e 0x45 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c8e 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 8) (.location (.reg 9))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101c91 0x101c95 [.mov (.reg 10) (.location (.input 4))] := by
    let ex : InstructionExecution 0x101c91 0x101c95 (movR32M32Effect 0x101c91 10 (.base 6 (.d8
      0x10))) := {
      pre := (LoadPre 0x101c91 (fun s ↦ ((.base 6 (.d8 0x10)) : AddrMode).addr s (0x101c91 + 4)) 4)
      code := codeRange 0x101c91 [0x44, 0x8b, 0x56, 0x10]
      step := mov_r32_m32_effect_step 0x101c91 0x44 (by simp [RexNoWPrefix]) 2 (.base 6 (.d8 0x10))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c91 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 16 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.input 4))) (dst := 10) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101c95 0x101c9a [.mov (.stack 28) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101c95 0x101c9a (movM32R32Effect 0x101c95 10 (.sib 4 none 0 (.d8
      0x1c))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101c95 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x1c)) :
        AddrMode).addr s (0x101c95 + 5)) 4)
      code := codeRange 0x101c95 [0x44, 0x89, 0x54, 0x24, 0x1c]
      step := Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x101c95 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4
        none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c95 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 28) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1c95 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 28) (.location (.reg 10))) (dst := 28)
      (value := fun s ↦ (Operand.reg 10 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h11 : RunWords 0x101c9a 0x101c9d [.add (.reg 7) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101c9a 0x101c9d (addR32R32Effect 0x101c9a 3 7 8) := {
      pre := (fun s ↦ s.RIP = 0x101c9a)
      code := codeRange 0x101c9a [0x44, 0x1, 0xc7]
      step := add_r32_r32_rex_effect_step 0x101c9a 0x44 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c9a 3 (by decide +kernel)
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
  have h12 : RunWords 0x101c9d 0x101ca3 [.add (.reg 7) (.immediate 0xc1bdceee)] := by
    let ex : InstructionExecution 0x101c9d 0x101ca3 (addR32Imm32Effect 0x101c9d 6 7 0xc1bdceee) := {
      pre := (fun s ↦ s.RIP = 0x101c9d)
      code := codeRange 0x101c9d [0x81, 0xc7, 0xee, 0xce, 0xbd, 0xc1]
      step := add_r32_imm32_effect_step 0x101c9d 0xc7 0xc1bdceee (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1c9d 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.immediate 0xc1bdceee)) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h13 : RunWords 0x101ca3 0x101ca6 [.rol (.reg 7) 22] := by
    let ex : InstructionExecution 0x101ca3 0x101ca6 (rolR32Effect 0x101ca3 3 7 22) := {
      pre := (fun s ↦ s.RIP = 0x101ca3)
      code := codeRange 0x101ca3 [0xc1, 0xc7, 0x16]
      step := rol_r32_imm8_effect_step 0x101ca3 0xc7 0x16 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ca3 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 7) 22) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h14 : RunWords 0x101ca6 0x101ca8 [.add (.reg 7) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101ca6 0x101ca8 (addR32R32Effect 0x101ca6 2 7 2) := {
      pre := (fun s ↦ s.RIP = 0x101ca6)
      code := codeRange 0x101ca6 [0x1, 0xd7]
      step := add_r32_r32_effect_step 0x101ca6 0xd7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ca6 2 (by decide +kernel)
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
  simpa only [segment4, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (h14)))))))))))))

theorem segment5_runs [Bindings] :
    RunWords 0x101ca8 0x101cd3 segment5 := by
  have h1 : RunWords 0x101ca8 0x101cab [.mov (.reg 8) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101ca8 0x101cab (movR32R32Effect 0x101ca8 3 8 7) := {
      pre := (fun s ↦ s.RIP = 0x101ca8)
      code := codeRange 0x101ca8 [0x41, 0x89, 0xf8]
      step := mov_r32_r32_rex_effect_step 0x101ca8 0x41 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ca8 3 (by decide +kernel)
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
  have h2 : RunWords 0x101cab 0x101cae [.mov (.reg 9) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101cab 0x101cae (movR32R32Effect 0x101cab 3 9 7) := {
      pre := (fun s ↦ s.RIP = 0x101cab)
      code := codeRange 0x101cab [0x41, 0x89, 0xf9]
      step := mov_r32_r32_rex_effect_step 0x101cab 0x41 0xf9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cab 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 9) (.location (.reg 7))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101cae 0x101cb1 [.not (.reg 9)] := by
    let ex : InstructionExecution 0x101cae 0x101cb1 (notR32Effect 0x101cae 3 9) := {
      pre := (fun s ↦ s.RIP = 0x101cae)
      code := codeRange 0x101cae [0x41, 0xf7, 0xd1]
      step := not_r32_rex_effect_step 0x101cae 0x41 0xd1 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1cae 3 (by decide +kernel)
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
  have h4 : RunWords 0x101cb1 0x101cb4 [.and (.reg 8) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101cb1 0x101cb4 (andR32R32Effect 0x101cb1 3 8 2) := {
      pre := (fun s ↦ s.RIP = 0x101cb1)
      code := codeRange 0x101cb1 [0x41, 0x21, 0xd0]
      step := and_r32_r32_rex_effect_step 0x101cb1 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cb1 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 8) (.location (.reg 2))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101cb4 0x101cb7 [.and (.reg 9) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101cb4 0x101cb7 (andR32R32Effect 0x101cb4 3 9 1) := {
      pre := (fun s ↦ s.RIP = 0x101cb4)
      code := codeRange 0x101cb4 [0x41, 0x21, 0xc9]
      step := and_r32_r32_rex_effect_step 0x101cb4 0x41 0xc9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cb4 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 9) (.location (.reg 1))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101cb7 0x101cba [.add (.reg 0) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101cb7 0x101cba (addR32R32Effect 0x101cb7 3 0 10) := {
      pre := (fun s ↦ s.RIP = 0x101cb7)
      code := codeRange 0x101cb7 [0x44, 0x1, 0xd0]
      step := add_r32_r32_rex_effect_step 0x101cb7 0x44 0xd0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cb7 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 10))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101cba 0x101cbd [.add (.reg 0) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x101cba 0x101cbd (addR32R32Effect 0x101cba 3 0 9) := {
      pre := (fun s ↦ s.RIP = 0x101cba)
      code := codeRange 0x101cba [0x44, 0x1, 0xc8]
      step := add_r32_r32_rex_effect_step 0x101cba 0x44 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cba 3 (by decide +kernel)
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
  have h8 : RunWords 0x101cbd 0x101cc1 [.mov (.reg 10) (.location (.input 5))] := by
    let ex : InstructionExecution 0x101cbd 0x101cc1 (movR32M32Effect 0x101cbd 10 (.base 6 (.d8
      0x14))) := {
      pre := (LoadPre 0x101cbd (fun s ↦ ((.base 6 (.d8 0x14)) : AddrMode).addr s (0x101cbd + 4)) 4)
      code := codeRange 0x101cbd [0x44, 0x8b, 0x56, 0x14]
      step := mov_r32_m32_effect_step 0x101cbd 0x44 (by simp [RexNoWPrefix]) 2 (.base 6 (.d8 0x14))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cbd 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 20 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.input 5))) (dst := 10) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101cc1 0x101cc6 [.mov (.stack 64) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101cc1 0x101cc6 (movM64R64Effect 0x101cc1 10 (.sib 4 none 0 (.d8
      0x40))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101cc1 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x40)) :
        AddrMode).addr s (0x101cc1 + 5)) 8)
      code := codeRange 0x101cc1 [0x4c, 0x89, 0x54, 0x24, 0x40]
      step := Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step 0x101cc1 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0
        (.d8 0x40)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cc1 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 64) (length := 8) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1cc1 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack64 (instruction := .mov (.stack 64) (.location (.reg 10))) (dst := 64)
      (value := fun s ↦ (Operand.reg 10 : Operand 64).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h10 : RunWords 0x101cc6 0x101cc9 [.add (.reg 0) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101cc6 0x101cc9 (addR32R32Effect 0x101cc6 3 0 8) := {
      pre := (fun s ↦ s.RIP = 0x101cc6)
      code := codeRange 0x101cc6 [0x44, 0x1, 0xc0]
      step := add_r32_r32_rex_effect_step 0x101cc6 0x44 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cc6 3 (by decide +kernel)
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
  have h11 : RunWords 0x101cc9 0x101cce [.add (.reg 0) (.immediate 0xf57c0faf)] := by
    let ex : InstructionExecution 0x101cc9 0x101cce (addR32Imm32Effect 0x101cc9 5 0 0xf57c0faf) := {
      pre := (fun s ↦ s.RIP = 0x101cc9)
      code := codeRange 0x101cc9 [0x5, 0xaf, 0xf, 0x7c, 0xf5]
      step := Register.add_eax_imm32_effect_step 0x101cc9 0xf57c0faf
      present := fun hc ↦ program_text_slice hc 0x1cc9 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0xf57c0faf)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x101cce 0x101cd1 [.rol (.reg 0) 7] := by
    let ex : InstructionExecution 0x101cce 0x101cd1 (rolR32Effect 0x101cce 3 0 7) := {
      pre := (fun s ↦ s.RIP = 0x101cce)
      code := codeRange 0x101cce [0xc1, 0xc0, 0x7]
      step := rol_r32_imm8_effect_step 0x101cce 0xc0 0x7 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cce 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 7) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h13 : RunWords 0x101cd1 0x101cd3 [.add (.reg 0) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101cd1 0x101cd3 (addR32R32Effect 0x101cd1 2 0 7) := {
      pre := (fun s ↦ s.RIP = 0x101cd1)
      code := codeRange 0x101cd1 [0x1, 0xf8]
      step := add_r32_r32_effect_step 0x101cd1 0xf8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cd1 2 (by decide +kernel)
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
  simpa only [segment5, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13))))))))))))

theorem segment6_runs [Bindings] :
    RunWords 0x101cd3 0x101cfd segment6 := by
  have h1 : RunWords 0x101cd3 0x101cd6 [.mov (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101cd3 0x101cd6 (movR32R32Effect 0x101cd3 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x101cd3)
      code := codeRange 0x101cd3 [0x41, 0x89, 0xc0]
      step := mov_r32_r32_rex_effect_step 0x101cd3 0x41 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cd3 3 (by decide +kernel)
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
  have h2 : RunWords 0x101cd6 0x101cd9 [.mov (.reg 9) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101cd6 0x101cd9 (movR32R32Effect 0x101cd6 3 9 0) := {
      pre := (fun s ↦ s.RIP = 0x101cd6)
      code := codeRange 0x101cd6 [0x41, 0x89, 0xc1]
      step := mov_r32_r32_rex_effect_step 0x101cd6 0x41 0xc1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cd6 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 9) (.location (.reg 0))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101cd9 0x101cdc [.not (.reg 9)] := by
    let ex : InstructionExecution 0x101cd9 0x101cdc (notR32Effect 0x101cd9 3 9) := {
      pre := (fun s ↦ s.RIP = 0x101cd9)
      code := codeRange 0x101cd9 [0x41, 0xf7, 0xd1]
      step := not_r32_rex_effect_step 0x101cd9 0x41 0xd1 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1cd9 3 (by decide +kernel)
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
  have h4 : RunWords 0x101cdc 0x101cdf [.and (.reg 8) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101cdc 0x101cdf (andR32R32Effect 0x101cdc 3 8 7) := {
      pre := (fun s ↦ s.RIP = 0x101cdc)
      code := codeRange 0x101cdc [0x41, 0x21, 0xf8]
      step := and_r32_r32_rex_effect_step 0x101cdc 0x41 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cdc 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 8) (.location (.reg 7))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101cdf 0x101ce2 [.and (.reg 9) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101cdf 0x101ce2 (andR32R32Effect 0x101cdf 3 9 2) := {
      pre := (fun s ↦ s.RIP = 0x101cdf)
      code := codeRange 0x101cdf [0x41, 0x21, 0xd1]
      step := and_r32_r32_rex_effect_step 0x101cdf 0x41 0xd1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cdf 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 9) (.location (.reg 2))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101ce2 0x101ce5 [.add (.reg 1) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101ce2 0x101ce5 (addR32R32Effect 0x101ce2 3 1 10) := {
      pre := (fun s ↦ s.RIP = 0x101ce2)
      code := codeRange 0x101ce2 [0x44, 0x1, 0xd1]
      step := add_r32_r32_rex_effect_step 0x101ce2 0x44 0xd1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ce2 3 (by decide +kernel)
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
  have h7 : RunWords 0x101ce5 0x101ce8 [.add (.reg 1) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x101ce5 0x101ce8 (addR32R32Effect 0x101ce5 3 1 9) := {
      pre := (fun s ↦ s.RIP = 0x101ce5)
      code := codeRange 0x101ce5 [0x44, 0x1, 0xc9]
      step := add_r32_r32_rex_effect_step 0x101ce5 0x44 0xc9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ce5 3 (by decide +kernel)
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
  have h8 : RunWords 0x101ce8 0x101cec [.mov (.reg 9) (.location (.input 6))] := by
    let ex : InstructionExecution 0x101ce8 0x101cec (movR32M32Effect 0x101ce8 9 (.base 6 (.d8
      0x18))) := {
      pre := (LoadPre 0x101ce8 (fun s ↦ ((.base 6 (.d8 0x18)) : AddrMode).addr s (0x101ce8 + 4)) 4)
      code := codeRange 0x101ce8 [0x44, 0x8b, 0x4e, 0x18]
      step := mov_r32_m32_effect_step 0x101ce8 0x44 (by simp [RexNoWPrefix]) 1 (.base 6 (.d8 0x18))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1ce8 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 24 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 9) (.location (.input 6))) (dst := 9) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101cec 0x101cef [.add (.reg 8) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101cec 0x101cef (addR32R32Effect 0x101cec 3 8 1) := {
      pre := (fun s ↦ s.RIP = 0x101cec)
      code := codeRange 0x101cec [0x41, 0x1, 0xc8]
      step := add_r32_r32_rex_effect_step 0x101cec 0x41 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cec 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 8) (.location (.reg 1))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101cef 0x101cf6 [.add (.reg 8) (.immediate 0x4787c62a)] := by
    let ex : InstructionExecution 0x101cef 0x101cf6 (addR32Imm32Effect 0x101cef 7 8 0x4787c62a) := {
      pre := (fun s ↦ s.RIP = 0x101cef)
      code := codeRange 0x101cef [0x41, 0x81, 0xc0, 0x2a, 0xc6, 0x87, 0x47]
      step := add_r32_imm32_rex_effect_step 0x101cef 0x41 0xc0 0x4787c62a (by simp [RexNoWPrefix])
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cef 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 8) (.immediate 0x4787c62a)) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101cf6 0x101cfa [.rol (.reg 8) 12] := by
    let ex : InstructionExecution 0x101cf6 0x101cfa (rolR32Effect 0x101cf6 4 8 12) := {
      pre := (fun s ↦ s.RIP = 0x101cf6)
      code := codeRange 0x101cf6 [0x41, 0xc1, 0xc0, 0xc]
      step := rol_r32_imm8_rex_effect_step 0x101cf6 0x41 0xc0 0xc (by simp [RexNoWPrefix]) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cf6 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 8) 12) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h12 : RunWords 0x101cfa 0x101cfd [.add (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101cfa 0x101cfd (addR32R32Effect 0x101cfa 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x101cfa)
      code := codeRange 0x101cfa [0x41, 0x1, 0xc0]
      step := add_r32_r32_rex_effect_step 0x101cfa 0x41 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cfa 3 (by decide +kernel)
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
  simpa only [segment6, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12)))))))))))

theorem segment7_runs [Bindings] :
    RunWords 0x101cfd 0x101d1c segment7 := by
  have h1 : RunWords 0x101cfd 0x101cff [.mov (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101cfd 0x101cff (movR32R32Effect 0x101cfd 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x101cfd)
      code := codeRange 0x101cfd [0x89, 0xc1]
      step := mov_r32_r32_effect_step 0x101cfd 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cfd 2 (by decide +kernel)
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
  have h2 : RunWords 0x101cff 0x101d01 [.xor (.reg 1) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101cff 0x101d01 (xorR32R32Effect 0x101cff 2 1 7) := {
      pre := (fun s ↦ s.RIP = 0x101cff)
      code := codeRange 0x101cff [0x31, 0xf9]
      step := xor_r32_r32_effect_step 0x101cff 0xf9 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1cff 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 1) (.location (.reg 7))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101d01 0x101d04 [.and (.reg 1) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101d01 0x101d04 (andR32R32Effect 0x101d01 3 1 8) := {
      pre := (fun s ↦ s.RIP = 0x101d01)
      code := codeRange 0x101d01 [0x44, 0x21, 0xc1]
      step := and_r32_r32_rex_effect_step 0x101d01 0x44 0xc1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d01 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 1) (.location (.reg 8))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x101d04 0x101d06 [.xor (.reg 1) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101d04 0x101d06 (xorR32R32Effect 0x101d04 2 1 7) := {
      pre := (fun s ↦ s.RIP = 0x101d04)
      code := codeRange 0x101d04 [0x31, 0xf9]
      step := xor_r32_r32_effect_step 0x101d04 0xf9 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d04 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 1) (.location (.reg 7))) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101d06 0x101d09 [.add (.reg 2) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x101d06 0x101d09 (addR32R32Effect 0x101d06 3 2 9) := {
      pre := (fun s ↦ s.RIP = 0x101d06)
      code := codeRange 0x101d06 [0x44, 0x1, 0xca]
      step := add_r32_r32_rex_effect_step 0x101d06 0x44 0xca (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d06 3 (by decide +kernel)
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
  have h6 : RunWords 0x101d09 0x101d0e [.mov (.stack 56) (.location (.reg 9))] := by
    let ex : InstructionExecution 0x101d09 0x101d0e (movM32R32Effect 0x101d09 9 (.sib 4 none 0 (.d8
      0x38))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101d09 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x38)) :
        AddrMode).addr s (0x101d09 + 5)) 4)
      code := codeRange 0x101d09 [0x44, 0x89, 0x4c, 0x24, 0x38]
      step := Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x101d09 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4
        none 0 (.d8 0x38)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d09 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 56) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1d09 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 56) (.location (.reg 9))) (dst := 56)
      (value := fun s ↦ (Operand.reg 9 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h7 : RunWords 0x101d0e 0x101d10 [.add (.reg 1) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101d0e 0x101d10 (addR32R32Effect 0x101d0e 2 1 2) := {
      pre := (fun s ↦ s.RIP = 0x101d0e)
      code := codeRange 0x101d0e [0x1, 0xd1]
      step := add_r32_r32_effect_step 0x101d0e 0xd1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d0e 2 (by decide +kernel)
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
  have h8 : RunWords 0x101d10 0x101d16 [.add (.reg 1) (.immediate 0xa8304613)] := by
    let ex : InstructionExecution 0x101d10 0x101d16 (addR32Imm32Effect 0x101d10 6 1 0xa8304613) := {
      pre := (fun s ↦ s.RIP = 0x101d10)
      code := codeRange 0x101d10 [0x81, 0xc1, 0x13, 0x46, 0x30, 0xa8]
      step := add_r32_imm32_effect_step 0x101d10 0xc1 0xa8304613 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d10 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0xa8304613)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101d16 0x101d19 [.rol (.reg 1) 17] := by
    let ex : InstructionExecution 0x101d16 0x101d19 (rolR32Effect 0x101d16 3 1 17) := {
      pre := (fun s ↦ s.RIP = 0x101d16)
      code := codeRange 0x101d16 [0xc1, 0xc1, 0x11]
      step := rol_r32_imm8_effect_step 0x101d16 0xc1 0x11 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d16 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 17) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101d19 0x101d1c [.add (.reg 1) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101d19 0x101d1c (addR32R32Effect 0x101d19 3 1 8) := {
      pre := (fun s ↦ s.RIP = 0x101d19)
      code := codeRange 0x101d19 [0x44, 0x1, 0xc1]
      step := add_r32_r32_rex_effect_step 0x101d19 0x44 0xc1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d19 3 (by decide +kernel)
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
  simpa only [segment7, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10)))))))))

theorem segment8_runs [Bindings] :
    RunWords 0x101d1c 0x101d3e segment8 := by
  have h1 : RunWords 0x101d1c 0x101d1f [.mov (.reg 2) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101d1c 0x101d1f (movR32R32Effect 0x101d1c 3 2 8) := {
      pre := (fun s ↦ s.RIP = 0x101d1c)
      code := codeRange 0x101d1c [0x44, 0x89, 0xc2]
      step := mov_r32_r32_rex_effect_step 0x101d1c 0x44 0xc2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d1c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 2) (.location (.reg 8))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x101d1f 0x101d21 [.xor (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101d1f 0x101d21 (xorR32R32Effect 0x101d1f 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x101d1f)
      code := codeRange 0x101d1f [0x31, 0xc2]
      step := xor_r32_r32_effect_step 0x101d1f 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d1f 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 2) (.location (.reg 0))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101d21 0x101d23 [.and (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101d21 0x101d23 (andR32R32Effect 0x101d21 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x101d21)
      code := codeRange 0x101d21 [0x21, 0xca]
      step := and_r32_r32_effect_step 0x101d21 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d21 2 (by decide +kernel)
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
  have h4 : RunWords 0x101d23 0x101d25 [.xor (.reg 2) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101d23 0x101d25 (xorR32R32Effect 0x101d23 2 2 0) := {
      pre := (fun s ↦ s.RIP = 0x101d23)
      code := codeRange 0x101d23 [0x31, 0xc2]
      step := xor_r32_r32_effect_step 0x101d23 0xc2 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d23 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 2) (.location (.reg 0))) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101d25 0x101d29 [.mov (.reg 10) (.location (.input 7))] := by
    let ex : InstructionExecution 0x101d25 0x101d29 (movR32M32Effect 0x101d25 10 (.base 6 (.d8
      0x1c))) := {
      pre := (LoadPre 0x101d25 (fun s ↦ ((.base 6 (.d8 0x1c)) : AddrMode).addr s (0x101d25 + 4)) 4)
      code := codeRange 0x101d25 [0x44, 0x8b, 0x56, 0x1c]
      step := mov_r32_m32_effect_step 0x101d25 0x44 (by simp [RexNoWPrefix]) 2 (.base 6 (.d8 0x1c))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d25 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 28 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.input 7))) (dst := 10) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101d29 0x101d2e [.mov (.stack 52) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101d29 0x101d2e (movM32R32Effect 0x101d29 10 (.sib 4 none 0 (.d8
      0x34))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101d29 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x34)) :
        AddrMode).addr s (0x101d29 + 5)) 4)
      code := codeRange 0x101d29 [0x44, 0x89, 0x54, 0x24, 0x34]
      step := Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x101d29 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4
        none 0 (.d8 0x34)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d29 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 52) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1d29 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 52) (.location (.reg 10))) (dst := 52)
      (value := fun s ↦ (Operand.reg 10 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h7 : RunWords 0x101d2e 0x101d31 [.add (.reg 7) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101d2e 0x101d31 (addR32R32Effect 0x101d2e 3 7 10) := {
      pre := (fun s ↦ s.RIP = 0x101d2e)
      code := codeRange 0x101d2e [0x44, 0x1, 0xd7]
      step := add_r32_r32_rex_effect_step 0x101d2e 0x44 0xd7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d2e 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.reg 10))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101d31 0x101d33 [.add (.reg 2) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101d31 0x101d33 (addR32R32Effect 0x101d31 2 2 7) := {
      pre := (fun s ↦ s.RIP = 0x101d31)
      code := codeRange 0x101d31 [0x1, 0xfa]
      step := add_r32_r32_effect_step 0x101d31 0xfa (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d31 2 (by decide +kernel)
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
  have h9 : RunWords 0x101d33 0x101d39 [.add (.reg 2) (.immediate 0xfd469501)] := by
    let ex : InstructionExecution 0x101d33 0x101d39 (addR32Imm32Effect 0x101d33 6 2 0xfd469501) := {
      pre := (fun s ↦ s.RIP = 0x101d33)
      code := codeRange 0x101d33 [0x81, 0xc2, 0x1, 0x95, 0x46, 0xfd]
      step := add_r32_imm32_effect_step 0x101d33 0xc2 0xfd469501 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d33 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0xfd469501)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101d39 0x101d3c [.rol (.reg 2) 22] := by
    let ex : InstructionExecution 0x101d39 0x101d3c (rolR32Effect 0x101d39 3 2 22) := {
      pre := (fun s ↦ s.RIP = 0x101d39)
      code := codeRange 0x101d39 [0xc1, 0xc2, 0x16]
      step := rol_r32_imm8_effect_step 0x101d39 0xc2 0x16 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d39 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 22) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101d3c 0x101d3e [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101d3c 0x101d3e (addR32R32Effect 0x101d3c 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x101d3c)
      code := codeRange 0x101d3c [0x1, 0xca]
      step := add_r32_r32_effect_step 0x101d3c 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d3c 2 (by decide +kernel)
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
  simpa only [segment8, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment9_runs [Bindings] :
    RunWords 0x101d3e 0x101d60 segment9 := by
  have h1 : RunWords 0x101d3e 0x101d40 [.mov (.reg 7) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101d3e 0x101d40 (movR32R32Effect 0x101d3e 2 7 1) := {
      pre := (fun s ↦ s.RIP = 0x101d3e)
      code := codeRange 0x101d3e [0x89, 0xcf]
      step := mov_r32_r32_effect_step 0x101d3e 0xcf (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d3e 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 7) (.location (.reg 1))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x101d40 0x101d43 [.xor (.reg 7) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101d40 0x101d43 (xorR32R32Effect 0x101d40 3 7 8) := {
      pre := (fun s ↦ s.RIP = 0x101d40)
      code := codeRange 0x101d40 [0x44, 0x31, 0xc7]
      step := xor_r32_r32_rex_effect_step 0x101d40 0x44 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d40 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 7) (.location (.reg 8))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101d43 0x101d45 [.and (.reg 7) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101d43 0x101d45 (andR32R32Effect 0x101d43 2 7 2) := {
      pre := (fun s ↦ s.RIP = 0x101d43)
      code := codeRange 0x101d43 [0x21, 0xd7]
      step := and_r32_r32_effect_step 0x101d43 0xd7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d43 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 7) (.location (.reg 2))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x101d45 0x101d48 [.xor (.reg 7) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101d45 0x101d48 (xorR32R32Effect 0x101d45 3 7 8) := {
      pre := (fun s ↦ s.RIP = 0x101d45)
      code := codeRange 0x101d45 [0x44, 0x31, 0xc7]
      step := xor_r32_r32_rex_effect_step 0x101d45 0x44 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d45 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 7) (.location (.reg 8))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101d48 0x101d4c [.mov (.reg 10) (.location (.input 8))] := by
    let ex : InstructionExecution 0x101d48 0x101d4c (movR32M32Effect 0x101d48 10 (.base 6 (.d8
      0x20))) := {
      pre := (LoadPre 0x101d48 (fun s ↦ ((.base 6 (.d8 0x20)) : AddrMode).addr s (0x101d48 + 4)) 4)
      code := codeRange 0x101d48 [0x44, 0x8b, 0x56, 0x20]
      step := mov_r32_m32_effect_step 0x101d48 0x44 (by simp [RexNoWPrefix]) 2 (.base 6 (.d8 0x20))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d48 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 32 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.input 8))) (dst := 10) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101d4c 0x101d51 [.mov (.stack 24) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101d4c 0x101d51 (movM32R32Effect 0x101d4c 10 (.sib 4 none 0 (.d8
      0x18))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101d4c 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x18)) :
        AddrMode).addr s (0x101d4c + 5)) 4)
      code := codeRange 0x101d4c [0x44, 0x89, 0x54, 0x24, 0x18]
      step := Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x101d4c 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4
        none 0 (.d8 0x18)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d4c 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 24) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1d4c 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 24) (.location (.reg 10))) (dst := 24)
      (value := fun s ↦ (Operand.reg 10 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h7 : RunWords 0x101d51 0x101d54 [.add (.reg 0) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101d51 0x101d54 (addR32R32Effect 0x101d51 3 0 10) := {
      pre := (fun s ↦ s.RIP = 0x101d51)
      code := codeRange 0x101d51 [0x44, 0x1, 0xd0]
      step := add_r32_r32_rex_effect_step 0x101d51 0x44 0xd0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d51 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.location (.reg 10))) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101d54 0x101d56 [.add (.reg 0) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101d54 0x101d56 (addR32R32Effect 0x101d54 2 0 7) := {
      pre := (fun s ↦ s.RIP = 0x101d54)
      code := codeRange 0x101d54 [0x1, 0xf8]
      step := add_r32_r32_effect_step 0x101d54 0xf8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d54 2 (by decide +kernel)
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
  have h9 : RunWords 0x101d56 0x101d5b [.add (.reg 0) (.immediate 0x698098d8)] := by
    let ex : InstructionExecution 0x101d56 0x101d5b (addR32Imm32Effect 0x101d56 5 0 0x698098d8) := {
      pre := (fun s ↦ s.RIP = 0x101d56)
      code := codeRange 0x101d56 [0x5, 0xd8, 0x98, 0x80, 0x69]
      step := Register.add_eax_imm32_effect_step 0x101d56 0x698098d8
      present := fun hc ↦ program_text_slice hc 0x1d56 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0x698098d8)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101d5b 0x101d5e [.rol (.reg 0) 7] := by
    let ex : InstructionExecution 0x101d5b 0x101d5e (rolR32Effect 0x101d5b 3 0 7) := {
      pre := (fun s ↦ s.RIP = 0x101d5b)
      code := codeRange 0x101d5b [0xc1, 0xc0, 0x7]
      step := rol_r32_imm8_effect_step 0x101d5b 0xc0 0x7 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d5b 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 7) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101d5e 0x101d60 [.add (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101d5e 0x101d60 (addR32R32Effect 0x101d5e 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x101d5e)
      code := codeRange 0x101d5e [0x1, 0xd0]
      step := add_r32_r32_effect_step 0x101d5e 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d5e 2 (by decide +kernel)
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
  simpa only [segment9, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment10_runs [Bindings] :
    RunWords 0x101d60 0x101d82 segment10 := by
  have h1 : RunWords 0x101d60 0x101d62 [.mov (.reg 7) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101d60 0x101d62 (movR32R32Effect 0x101d60 2 7 2) := {
      pre := (fun s ↦ s.RIP = 0x101d60)
      code := codeRange 0x101d60 [0x89, 0xd7]
      step := mov_r32_r32_effect_step 0x101d60 0xd7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d60 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 7) (.location (.reg 2))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x101d62 0x101d64 [.xor (.reg 7) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101d62 0x101d64 (xorR32R32Effect 0x101d62 2 7 1) := {
      pre := (fun s ↦ s.RIP = 0x101d62)
      code := codeRange 0x101d62 [0x31, 0xcf]
      step := xor_r32_r32_effect_step 0x101d62 0xcf (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d62 2 (by decide +kernel)
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
  have h3 : RunWords 0x101d64 0x101d66 [.and (.reg 7) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101d64 0x101d66 (andR32R32Effect 0x101d64 2 7 0) := {
      pre := (fun s ↦ s.RIP = 0x101d64)
      code := codeRange 0x101d64 [0x21, 0xc7]
      step := and_r32_r32_effect_step 0x101d64 0xc7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d64 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 7) (.location (.reg 0))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x101d66 0x101d68 [.xor (.reg 7) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101d66 0x101d68 (xorR32R32Effect 0x101d66 2 7 1) := {
      pre := (fun s ↦ s.RIP = 0x101d66)
      code := codeRange 0x101d66 [0x31, 0xcf]
      step := xor_r32_r32_effect_step 0x101d66 0xcf (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d66 2 (by decide +kernel)
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
  have h5 : RunWords 0x101d68 0x101d6c [.mov (.reg 10) (.location (.input 9))] := by
    let ex : InstructionExecution 0x101d68 0x101d6c (movR32M32Effect 0x101d68 10 (.base 6 (.d8
      0x24))) := {
      pre := (LoadPre 0x101d68 (fun s ↦ ((.base 6 (.d8 0x24)) : AddrMode).addr s (0x101d68 + 4)) 4)
      code := codeRange 0x101d68 [0x44, 0x8b, 0x56, 0x24]
      step := mov_r32_m32_effect_step 0x101d68 0x44 (by simp [RexNoWPrefix]) 2 (.base 6 (.d8 0x24))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d68 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 36 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.input 9))) (dst := 10) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101d6c 0x101d71 [.mov (.stack 4) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101d6c 0x101d71 (movM32R32Effect 0x101d6c 10 (.sib 4 none 0 (.d8
      0x4))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101d6c 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x4)) :
        AddrMode).addr s (0x101d6c + 5)) 4)
      code := codeRange 0x101d6c [0x44, 0x89, 0x54, 0x24, 0x4]
      step := Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x101d6c 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4
        none 0 (.d8 0x4)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d6c 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 4) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1d6c 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 4) (.location (.reg 10))) (dst := 4)
      (value := fun s ↦ (Operand.reg 10 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h7 : RunWords 0x101d71 0x101d74 [.add (.reg 8) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101d71 0x101d74 (addR32R32Effect 0x101d71 3 8 10) := {
      pre := (fun s ↦ s.RIP = 0x101d71)
      code := codeRange 0x101d71 [0x45, 0x1, 0xd0]
      step := add_r32_r32_rex_effect_step 0x101d71 0x45 0xd0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d71 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 8) (.location (.reg 10))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101d74 0x101d77 [.add (.reg 7) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101d74 0x101d77 (addR32R32Effect 0x101d74 3 7 8) := {
      pre := (fun s ↦ s.RIP = 0x101d74)
      code := codeRange 0x101d74 [0x44, 0x1, 0xc7]
      step := add_r32_r32_rex_effect_step 0x101d74 0x44 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d74 3 (by decide +kernel)
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
  have h9 : RunWords 0x101d77 0x101d7d [.add (.reg 7) (.immediate 0x8b44f7af)] := by
    let ex : InstructionExecution 0x101d77 0x101d7d (addR32Imm32Effect 0x101d77 6 7 0x8b44f7af) := {
      pre := (fun s ↦ s.RIP = 0x101d77)
      code := codeRange 0x101d77 [0x81, 0xc7, 0xaf, 0xf7, 0x44, 0x8b]
      step := add_r32_imm32_effect_step 0x101d77 0xc7 0x8b44f7af (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d77 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.immediate 0x8b44f7af)) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101d7d 0x101d80 [.rol (.reg 7) 12] := by
    let ex : InstructionExecution 0x101d7d 0x101d80 (rolR32Effect 0x101d7d 3 7 12) := {
      pre := (fun s ↦ s.RIP = 0x101d7d)
      code := codeRange 0x101d7d [0xc1, 0xc7, 0xc]
      step := rol_r32_imm8_effect_step 0x101d7d 0xc7 0xc (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d7d 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 7) 12) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101d80 0x101d82 [.add (.reg 7) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101d80 0x101d82 (addR32R32Effect 0x101d80 2 7 0) := {
      pre := (fun s ↦ s.RIP = 0x101d80)
      code := codeRange 0x101d80 [0x1, 0xc7]
      step := add_r32_r32_effect_step 0x101d80 0xc7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d80 2 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 7) (.location (.reg 0))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  simpa only [segment10, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment11_runs [Bindings] :
    RunWords 0x101d82 0x101da8 segment11 := by
  have h1 : RunWords 0x101d82 0x101d85 [.mov (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101d82 0x101d85 (movR32R32Effect 0x101d82 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x101d82)
      code := codeRange 0x101d82 [0x41, 0x89, 0xc0]
      step := mov_r32_r32_rex_effect_step 0x101d82 0x41 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d82 3 (by decide +kernel)
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
  have h2 : RunWords 0x101d85 0x101d88 [.xor (.reg 8) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101d85 0x101d88 (xorR32R32Effect 0x101d85 3 8 2) := {
      pre := (fun s ↦ s.RIP = 0x101d85)
      code := codeRange 0x101d85 [0x41, 0x31, 0xd0]
      step := xor_r32_r32_rex_effect_step 0x101d85 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d85 3 (by decide +kernel)
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
  have h3 : RunWords 0x101d88 0x101d8b [.and (.reg 8) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101d88 0x101d8b (andR32R32Effect 0x101d88 3 8 7) := {
      pre := (fun s ↦ s.RIP = 0x101d88)
      code := codeRange 0x101d88 [0x41, 0x21, 0xf8]
      step := and_r32_r32_rex_effect_step 0x101d88 0x41 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d88 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 8) (.location (.reg 7))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x101d8b 0x101d8e [.xor (.reg 8) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101d8b 0x101d8e (xorR32R32Effect 0x101d8b 3 8 2) := {
      pre := (fun s ↦ s.RIP = 0x101d8b)
      code := codeRange 0x101d8b [0x41, 0x31, 0xd0]
      step := xor_r32_r32_rex_effect_step 0x101d8b 0x41 0xd0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d8b 3 (by decide +kernel)
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
  have h5 : RunWords 0x101d8e 0x101d92 [.mov (.reg 11) (.location (.input 10))] := by
    let ex : InstructionExecution 0x101d8e 0x101d92 (movR32M32Effect 0x101d8e 11 (.base 6 (.d8
      0x28))) := {
      pre := (LoadPre 0x101d8e (fun s ↦ ((.base 6 (.d8 0x28)) : AddrMode).addr s (0x101d8e + 4)) 4)
      code := codeRange 0x101d8e [0x44, 0x8b, 0x5e, 0x28]
      step := mov_r32_m32_effect_step 0x101d8e 0x44 (by simp [RexNoWPrefix]) 3 (.base 6 (.d8 0x28))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d8e 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 40 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 11) (.location (.input 10))) (dst := 11) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101d92 0x101d95 [.add (.reg 1) (.location (.reg 11))] := by
    let ex : InstructionExecution 0x101d92 0x101d95 (addR32R32Effect 0x101d92 3 1 11) := {
      pre := (fun s ↦ s.RIP = 0x101d92)
      code := codeRange 0x101d92 [0x44, 0x1, 0xd9]
      step := add_r32_r32_rex_effect_step 0x101d92 0x44 0xd9 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d92 3 (by decide +kernel)
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
  have h7 : RunWords 0x101d95 0x101d9a [.mov (.stack 40) (.location (.reg 11))] := by
    let ex : InstructionExecution 0x101d95 0x101d9a (movM32R32Effect 0x101d95 11 (.sib 4 none 0 (.d8
      0x28))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101d95 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x28)) :
        AddrMode).addr s (0x101d95 + 5)) 4)
      code := codeRange 0x101d95 [0x44, 0x89, 0x5c, 0x24, 0x28]
      step := Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x101d95 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4
        none 0 (.d8 0x28)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d95 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 40) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1d95 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 40) (.location (.reg 11))) (dst := 40)
      (value := fun s ↦ (Operand.reg 11 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h8 : RunWords 0x101d9a 0x101d9d [.add (.reg 1) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101d9a 0x101d9d (addR32R32Effect 0x101d9a 3 1 8) := {
      pre := (fun s ↦ s.RIP = 0x101d9a)
      code := codeRange 0x101d9a [0x44, 0x1, 0xc1]
      step := add_r32_r32_rex_effect_step 0x101d9a 0x44 0xc1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d9a 3 (by decide +kernel)
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
  have h9 : RunWords 0x101d9d 0x101da3 [.add (.reg 1) (.immediate 0xffff5bb1)] := by
    let ex : InstructionExecution 0x101d9d 0x101da3 (addR32Imm32Effect 0x101d9d 6 1 0xffff5bb1) := {
      pre := (fun s ↦ s.RIP = 0x101d9d)
      code := codeRange 0x101d9d [0x81, 0xc1, 0xb1, 0x5b, 0xff, 0xff]
      step := add_r32_imm32_effect_step 0x101d9d 0xc1 0xffff5bb1 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1d9d 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0xffff5bb1)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101da3 0x101da6 [.rol (.reg 1) 17] := by
    let ex : InstructionExecution 0x101da3 0x101da6 (rolR32Effect 0x101da3 3 1 17) := {
      pre := (fun s ↦ s.RIP = 0x101da3)
      code := codeRange 0x101da3 [0xc1, 0xc1, 0x11]
      step := rol_r32_imm8_effect_step 0x101da3 0xc1 0x11 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1da3 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 17) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101da6 0x101da8 [.add (.reg 1) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101da6 0x101da8 (addR32R32Effect 0x101da6 2 1 7) := {
      pre := (fun s ↦ s.RIP = 0x101da6)
      code := codeRange 0x101da6 [0x1, 0xf9]
      step := add_r32_r32_effect_step 0x101da6 0xf9 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1da6 2 (by decide +kernel)
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
  simpa only [segment11, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment12_runs [Bindings] :
    RunWords 0x101da8 0x101dce segment12 := by
  have h1 : RunWords 0x101da8 0x101dab [.mov (.reg 8) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101da8 0x101dab (movR32R32Effect 0x101da8 3 8 7) := {
      pre := (fun s ↦ s.RIP = 0x101da8)
      code := codeRange 0x101da8 [0x41, 0x89, 0xf8]
      step := mov_r32_r32_rex_effect_step 0x101da8 0x41 0xf8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1da8 3 (by decide +kernel)
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
  have h2 : RunWords 0x101dab 0x101dae [.xor (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101dab 0x101dae (xorR32R32Effect 0x101dab 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x101dab)
      code := codeRange 0x101dab [0x41, 0x31, 0xc0]
      step := xor_r32_r32_rex_effect_step 0x101dab 0x41 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dab 3 (by decide +kernel)
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
  have h3 : RunWords 0x101dae 0x101db1 [.and (.reg 8) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101dae 0x101db1 (andR32R32Effect 0x101dae 3 8 1) := {
      pre := (fun s ↦ s.RIP = 0x101dae)
      code := codeRange 0x101dae [0x41, 0x21, 0xc8]
      step := and_r32_r32_rex_effect_step 0x101dae 0x41 0xc8 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dae 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 8) (.location (.reg 1))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x101db1 0x101db4 [.xor (.reg 8) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101db1 0x101db4 (xorR32R32Effect 0x101db1 3 8 0) := {
      pre := (fun s ↦ s.RIP = 0x101db1)
      code := codeRange 0x101db1 [0x41, 0x31, 0xc0]
      step := xor_r32_r32_rex_effect_step 0x101db1 0x41 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1db1 3 (by decide +kernel)
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
  have h5 : RunWords 0x101db4 0x101db8 [.mov (.reg 14) (.location (.input 11))] := by
    let ex : InstructionExecution 0x101db4 0x101db8 (movR32M32Effect 0x101db4 14 (.base 6 (.d8
      0x2c))) := {
      pre := (LoadPre 0x101db4 (fun s ↦ ((.base 6 (.d8 0x2c)) : AddrMode).addr s (0x101db4 + 4)) 4)
      code := codeRange 0x101db4 [0x44, 0x8b, 0x76, 0x2c]
      step := mov_r32_m32_effect_step 0x101db4 0x44 (by simp [RexNoWPrefix]) 6 (.base 6 (.d8 0x2c))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1db4 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 44 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 14) (.location (.input 11))) (dst := 14) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101db8 0x101dbb [.add (.reg 2) (.location (.reg 14))] := by
    let ex : InstructionExecution 0x101db8 0x101dbb (addR32R32Effect 0x101db8 3 2 14) := {
      pre := (fun s ↦ s.RIP = 0x101db8)
      code := codeRange 0x101db8 [0x44, 0x1, 0xf2]
      step := add_r32_r32_rex_effect_step 0x101db8 0x44 0xf2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1db8 3 (by decide +kernel)
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
  have h7 : RunWords 0x101dbb 0x101dc0 [.mov (.stack 32) (.location (.reg 14))] := by
    let ex : InstructionExecution 0x101dbb 0x101dc0 (movM32R32Effect 0x101dbb 14 (.sib 4 none 0 (.d8
      0x20))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101dbb 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x20)) :
        AddrMode).addr s (0x101dbb + 5)) 4)
      code := codeRange 0x101dbb [0x44, 0x89, 0x74, 0x24, 0x20]
      step := Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x101dbb 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4
        none 0 (.d8 0x20)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dbb 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 32) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1dbb 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 32) (.location (.reg 14))) (dst := 32)
      (value := fun s ↦ (Operand.reg 14 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h8 : RunWords 0x101dc0 0x101dc3 [.add (.reg 2) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101dc0 0x101dc3 (addR32R32Effect 0x101dc0 3 2 8) := {
      pre := (fun s ↦ s.RIP = 0x101dc0)
      code := codeRange 0x101dc0 [0x44, 0x1, 0xc2]
      step := add_r32_r32_rex_effect_step 0x101dc0 0x44 0xc2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dc0 3 (by decide +kernel)
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
  have h9 : RunWords 0x101dc3 0x101dc9 [.add (.reg 2) (.immediate 0x895cd7be)] := by
    let ex : InstructionExecution 0x101dc3 0x101dc9 (addR32Imm32Effect 0x101dc3 6 2 0x895cd7be) := {
      pre := (fun s ↦ s.RIP = 0x101dc3)
      code := codeRange 0x101dc3 [0x81, 0xc2, 0xbe, 0xd7, 0x5c, 0x89]
      step := add_r32_imm32_effect_step 0x101dc3 0xc2 0x895cd7be (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dc3 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0x895cd7be)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101dc9 0x101dcc [.rol (.reg 2) 22] := by
    let ex : InstructionExecution 0x101dc9 0x101dcc (rolR32Effect 0x101dc9 3 2 22) := {
      pre := (fun s ↦ s.RIP = 0x101dc9)
      code := codeRange 0x101dc9 [0xc1, 0xc2, 0x16]
      step := rol_r32_imm8_effect_step 0x101dc9 0xc2 0x16 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dc9 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 22) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101dcc 0x101dce [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101dcc 0x101dce (addR32R32Effect 0x101dcc 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x101dcc)
      code := codeRange 0x101dcc [0x1, 0xca]
      step := add_r32_r32_effect_step 0x101dcc 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dcc 2 (by decide +kernel)
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
  simpa only [segment12, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment13_runs [Bindings] :
    RunWords 0x101dce 0x101df8 segment13 := by
  have h1 : RunWords 0x101dce 0x101dd1 [.mov (.reg 10) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101dce 0x101dd1 (movR32R32Effect 0x101dce 3 10 1) := {
      pre := (fun s ↦ s.RIP = 0x101dce)
      code := codeRange 0x101dce [0x41, 0x89, 0xca]
      step := mov_r32_r32_rex_effect_step 0x101dce 0x41 0xca (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dce 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.reg 1))) (dst := 10) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x101dd1 0x101dd4 [.xor (.reg 10) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101dd1 0x101dd4 (xorR32R32Effect 0x101dd1 3 10 7) := {
      pre := (fun s ↦ s.RIP = 0x101dd1)
      code := codeRange 0x101dd1 [0x41, 0x31, 0xfa]
      step := xor_r32_r32_rex_effect_step 0x101dd1 0x41 0xfa (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dd1 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 10) (.location (.reg 7))) (dst := 10) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101dd4 0x101dd7 [.and (.reg 10) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101dd4 0x101dd7 (andR32R32Effect 0x101dd4 3 10 2) := {
      pre := (fun s ↦ s.RIP = 0x101dd4)
      code := codeRange 0x101dd4 [0x41, 0x21, 0xd2]
      step := and_r32_r32_rex_effect_step 0x101dd4 0x41 0xd2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dd4 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 10) (.location (.reg 2))) (dst := 10) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x101dd7 0x101dda [.xor (.reg 10) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101dd7 0x101dda (xorR32R32Effect 0x101dd7 3 10 7) := {
      pre := (fun s ↦ s.RIP = 0x101dd7)
      code := codeRange 0x101dd7 [0x41, 0x31, 0xfa]
      step := xor_r32_r32_rex_effect_step 0x101dd7 0x41 0xfa (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dd7 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .xor (.reg 10) (.location (.reg 7))) (dst := 10) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101dda 0x101dde [.mov (.reg 8) (.location (.input 12))] := by
    let ex : InstructionExecution 0x101dda 0x101dde (movR32M32Effect 0x101dda 8 (.base 6 (.d8
      0x30))) := {
      pre := (LoadPre 0x101dda (fun s ↦ ((.base 6 (.d8 0x30)) : AddrMode).addr s (0x101dda + 4)) 4)
      code := codeRange 0x101dda [0x44, 0x8b, 0x46, 0x30]
      step := mov_r32_m32_effect_step 0x101dda 0x44 (by simp [RexNoWPrefix]) 0 (.base 6 (.d8 0x30))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dda 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 48 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.input 12))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101dde 0x101de3 [.mov (.stack 44) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101dde 0x101de3 (movM32R32Effect 0x101dde 8 (.sib 4 none 0 (.d8
      0x2c))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101dde 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x2c)) :
        AddrMode).addr s (0x101dde + 5)) 4)
      code := codeRange 0x101dde [0x44, 0x89, 0x44, 0x24, 0x2c]
      step := Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x101dde 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4
        none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dde 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 44) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1dde 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 44) (.location (.reg 8))) (dst := 44)
      (value := fun s ↦ (Operand.reg 8 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h7 : RunWords 0x101de3 0x101de6 [.add (.reg 0) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101de3 0x101de6 (addR32R32Effect 0x101de3 3 0 8) := {
      pre := (fun s ↦ s.RIP = 0x101de3)
      code := codeRange 0x101de3 [0x44, 0x1, 0xc0]
      step := add_r32_r32_rex_effect_step 0x101de3 0x44 0xc0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1de3 3 (by decide +kernel)
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
  have h8 : RunWords 0x101de6 0x101dea [.lea (.reg 12) (.reg 10) (.reg 0)] := by
    let ex : InstructionExecution 0x101de6 0x101dea (Register.leaR32Effect 0x101de6 4 12 (.sib 10
      (some 0) 0 .none)) := {
      pre := (fun s ↦ s.RIP = 0x101de6)
      code := codeRange 0x101de6 [0x45, 0x8d, 0x24, 0x2]
      step := Register.lea_r32_rex_effect_step 0x101de6 0x45 (by simp [RexNoWPrefix]) 4 (.sib 10
        (some 0) 0 .none) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1de6 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .lea (.reg 12) (.reg 10) (.reg 0)) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101dea 0x101df1 [.add (.reg 12) (.immediate 0x6b901122)] := by
    let ex : InstructionExecution 0x101dea 0x101df1 (addR32Imm32Effect 0x101dea 7 12 0x6b901122) :=
      {
      pre := (fun s ↦ s.RIP = 0x101dea)
      code := codeRange 0x101dea [0x41, 0x81, 0xc4, 0x22, 0x11, 0x90, 0x6b]
      step := add_r32_imm32_rex_effect_step 0x101dea 0x41 0xc4 0x6b901122 (by simp [RexNoWPrefix])
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dea 7 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 12) (.immediate 0x6b901122)) (dst := 12) (fun _ ↦
      rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101df1 0x101df5 [.rol (.reg 12) 7] := by
    let ex : InstructionExecution 0x101df1 0x101df5 (rolR32Effect 0x101df1 4 12 7) := {
      pre := (fun s ↦ s.RIP = 0x101df1)
      code := codeRange 0x101df1 [0x41, 0xc1, 0xc4, 0x7]
      step := rol_r32_imm8_rex_effect_step 0x101df1 0x41 0xc4 0x7 (by simp [RexNoWPrefix]) (by
        decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1df1 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 12) 7) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101df5 0x101df8 [.add (.reg 12) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101df5 0x101df8 (addR32R32Effect 0x101df5 3 12 2) := {
      pre := (fun s ↦ s.RIP = 0x101df5)
      code := codeRange 0x101df5 [0x41, 0x1, 0xd4]
      step := add_r32_r32_rex_effect_step 0x101df5 0x41 0xd4 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1df5 3 (by decide +kernel)
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
  simpa only [segment13, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment14_runs [Bindings] :
    RunWords 0x101df8 0x101e1a segment14 := by
  have h1 : RunWords 0x101df8 0x101dfa [.mov (.reg 0) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101df8 0x101dfa (movR32R32Effect 0x101df8 2 0 2) := {
      pre := (fun s ↦ s.RIP = 0x101df8)
      code := codeRange 0x101df8 [0x89, 0xd0]
      step := mov_r32_r32_effect_step 0x101df8 0xd0 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1df8 2 (by decide +kernel)
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
  have h2 : RunWords 0x101dfa 0x101dfc [.xor (.reg 0) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101dfa 0x101dfc (xorR32R32Effect 0x101dfa 2 0 1) := {
      pre := (fun s ↦ s.RIP = 0x101dfa)
      code := codeRange 0x101dfa [0x31, 0xc8]
      step := xor_r32_r32_effect_step 0x101dfa 0xc8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dfa 2 (by decide +kernel)
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
  have h3 : RunWords 0x101dfc 0x101dff [.and (.reg 0) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101dfc 0x101dff (andR32R32Effect 0x101dfc 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x101dfc)
      code := codeRange 0x101dfc [0x44, 0x21, 0xe0]
      step := and_r32_r32_rex_effect_step 0x101dfc 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dfc 3 (by decide +kernel)
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
  have h4 : RunWords 0x101dff 0x101e01 [.xor (.reg 0) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101dff 0x101e01 (xorR32R32Effect 0x101dff 2 0 1) := {
      pre := (fun s ↦ s.RIP = 0x101dff)
      code := codeRange 0x101dff [0x31, 0xc8]
      step := xor_r32_r32_effect_step 0x101dff 0xc8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1dff 2 (by decide +kernel)
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
  have h5 : RunWords 0x101e01 0x101e05 [.mov (.reg 8) (.location (.input 13))] := by
    let ex : InstructionExecution 0x101e01 0x101e05 (movR32M32Effect 0x101e01 8 (.base 6 (.d8
      0x34))) := {
      pre := (LoadPre 0x101e01 (fun s ↦ ((.base 6 (.d8 0x34)) : AddrMode).addr s (0x101e01 + 4)) 4)
      code := codeRange 0x101e01 [0x44, 0x8b, 0x46, 0x34]
      step := mov_r32_m32_effect_step 0x101e01 0x44 (by simp [RexNoWPrefix]) 0 (.base 6 (.d8 0x34))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e01 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 52 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.input 13))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101e05 0x101e0a [.mov (.stack 20) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101e05 0x101e0a (movM32R32Effect 0x101e05 8 (.sib 4 none 0 (.d8
      0x14))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101e05 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x14)) :
        AddrMode).addr s (0x101e05 + 5)) 4)
      code := codeRange 0x101e05 [0x44, 0x89, 0x44, 0x24, 0x14]
      step := Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x101e05 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4
        none 0 (.d8 0x14)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e05 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 20) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1e05 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 20) (.location (.reg 8))) (dst := 20)
      (value := fun s ↦ (Operand.reg 8 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h7 : RunWords 0x101e0a 0x101e0d [.add (.reg 7) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101e0a 0x101e0d (addR32R32Effect 0x101e0a 3 7 8) := {
      pre := (fun s ↦ s.RIP = 0x101e0a)
      code := codeRange 0x101e0a [0x44, 0x1, 0xc7]
      step := add_r32_r32_rex_effect_step 0x101e0a 0x44 0xc7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e0a 3 (by decide +kernel)
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
  have h8 : RunWords 0x101e0d 0x101e0f [.add (.reg 0) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101e0d 0x101e0f (addR32R32Effect 0x101e0d 2 0 7) := {
      pre := (fun s ↦ s.RIP = 0x101e0d)
      code := codeRange 0x101e0d [0x1, 0xf8]
      step := add_r32_r32_effect_step 0x101e0d 0xf8 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e0d 2 (by decide +kernel)
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
  have h9 : RunWords 0x101e0f 0x101e14 [.add (.reg 0) (.immediate 0xfd987193)] := by
    let ex : InstructionExecution 0x101e0f 0x101e14 (addR32Imm32Effect 0x101e0f 5 0 0xfd987193) := {
      pre := (fun s ↦ s.RIP = 0x101e0f)
      code := codeRange 0x101e0f [0x5, 0x93, 0x71, 0x98, 0xfd]
      step := Register.add_eax_imm32_effect_step 0x101e0f 0xfd987193
      present := fun hc ↦ program_text_slice hc 0x1e0f 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 0) (.immediate 0xfd987193)) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h10 : RunWords 0x101e14 0x101e17 [.rol (.reg 0) 12] := by
    let ex : InstructionExecution 0x101e14 0x101e17 (rolR32Effect 0x101e14 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x101e14)
      code := codeRange 0x101e14 [0xc1, 0xc0, 0xc]
      step := rol_r32_imm8_effect_step 0x101e14 0xc0 0xc (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e14 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 0) 12) (dst := 0) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h11 : RunWords 0x101e17 0x101e1a [.add (.reg 0) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101e17 0x101e1a (addR32R32Effect 0x101e17 3 0 12) := {
      pre := (fun s ↦ s.RIP = 0x101e17)
      code := codeRange 0x101e17 [0x44, 0x1, 0xe0]
      step := add_r32_r32_rex_effect_step 0x101e17 0x44 0xe0 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e17 3 (by decide +kernel)
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
  simpa only [segment14, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11))))))))))

theorem segment15_runs [Bindings] :
    RunWords 0x101e1a 0x101e46 segment15 := by
  have h1 : RunWords 0x101e1a 0x101e1c [.mov (.reg 7) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101e1a 0x101e1c (movR32R32Effect 0x101e1a 2 7 0) := {
      pre := (fun s ↦ s.RIP = 0x101e1a)
      code := codeRange 0x101e1a [0x89, 0xc7]
      step := mov_r32_r32_effect_step 0x101e1a 0xc7 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e1a 2 (by decide +kernel)
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
  have h2 : RunWords 0x101e1c 0x101e1f [.and (.reg 7) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101e1c 0x101e1f (andR32R32Effect 0x101e1c 3 7 12) := {
      pre := (fun s ↦ s.RIP = 0x101e1c)
      code := codeRange 0x101e1c [0x44, 0x21, 0xe7]
      step := and_r32_r32_rex_effect_step 0x101e1c 0x44 0xe7 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e1c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 7) (.location (.reg 12))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101e1f 0x101e21 [.mov (.reg 5) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101e1f 0x101e21 (movR32R32Effect 0x101e1f 2 5 0) := {
      pre := (fun s ↦ s.RIP = 0x101e1f)
      code := codeRange 0x101e1f [0x89, 0xc5]
      step := mov_r32_r32_effect_step 0x101e1f 0xc5 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e1f 2 (by decide +kernel)
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
  have h4 : RunWords 0x101e21 0x101e23 [.not (.reg 5)] := by
    let ex : InstructionExecution 0x101e21 0x101e23 (notR32Effect 0x101e21 2 5) := {
      pre := (fun s ↦ s.RIP = 0x101e21)
      code := codeRange 0x101e21 [0xf7, 0xd5]
      step := not_r32_effect_step 0x101e21 0xd5 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e21 2 (by decide +kernel)
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
  have h5 : RunWords 0x101e23 0x101e26 [.mov (.reg 10) (.location (.reg 2))] := by
    let ex : InstructionExecution 0x101e23 0x101e26 (movR32R32Effect 0x101e23 3 10 2) := {
      pre := (fun s ↦ s.RIP = 0x101e23)
      code := codeRange 0x101e23 [0x41, 0x89, 0xd2]
      step := mov_r32_r32_rex_effect_step 0x101e23 0x41 0xd2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e23 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.reg 2))) (dst := 10) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101e26 0x101e29 [.and (.reg 10) (.location (.reg 5))] := by
    let ex : InstructionExecution 0x101e26 0x101e29 (andR32R32Effect 0x101e26 3 10 5) := {
      pre := (fun s ↦ s.RIP = 0x101e26)
      code := codeRange 0x101e26 [0x41, 0x21, 0xea]
      step := and_r32_r32_rex_effect_step 0x101e26 0x41 0xea (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e26 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 10) (.location (.reg 5))) (dst := 10) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101e29 0x101e2c [.or (.reg 10) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101e29 0x101e2c (Register.orR32R32Effect 0x101e29 3 10 7) := {
      pre := (fun s ↦ s.RIP = 0x101e29)
      code := codeRange 0x101e29 [0x41, 0x9, 0xfa]
      step := Register.or_r32_r32_rex_effect_step 0x101e29 0x41 0xfa (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1e29 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 10) (.location (.reg 7))) (dst := 10) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101e2c 0x101e30 [.mov (.reg 8) (.location (.input 14))] := by
    let ex : InstructionExecution 0x101e2c 0x101e30 (movR32M32Effect 0x101e2c 8 (.base 6 (.d8
      0x38))) := {
      pre := (LoadPre 0x101e2c (fun s ↦ ((.base 6 (.d8 0x38)) : AddrMode).addr s (0x101e2c + 4)) 4)
      code := codeRange 0x101e2c [0x44, 0x8b, 0x46, 0x38]
      step := mov_r32_m32_effect_step 0x101e2c 0x44 (by simp [RexNoWPrefix]) 0 (.base 6 (.d8 0x38))
        (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e2c 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 56 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 8) (.location (.input 14))) (dst := 8) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101e30 0x101e33 [.add (.reg 1) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101e30 0x101e33 (addR32R32Effect 0x101e30 3 1 8) := {
      pre := (fun s ↦ s.RIP = 0x101e30)
      code := codeRange 0x101e30 [0x44, 0x1, 0xc1]
      step := add_r32_r32_rex_effect_step 0x101e30 0x44 0xc1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e30 3 (by decide +kernel)
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
  have h10 : RunWords 0x101e33 0x101e38 [.mov (.stack 36) (.location (.reg 8))] := by
    let ex : InstructionExecution 0x101e33 0x101e38 (movM32R32Effect 0x101e33 8 (.sib 4 none 0 (.d8
      0x24))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101e33 5 (fun s ↦ ((.sib 4 none 0 (.d8 0x24)) :
        AddrMode).addr s (0x101e33 + 5)) 4)
      code := codeRange 0x101e33 [0x44, 0x89, 0x44, 0x24, 0x24]
      step := Md5.Proofs.Buffered.Stores.mov_m32_r32_effect_step 0x101e33 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4
        none 0 (.d8 0x24)) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e33 5 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 36) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1e33 5 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 36) (.location (.reg 8))) (dst := 36)
      (value := fun s ↦ (Operand.reg 8 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h11 : RunWords 0x101e38 0x101e3b [.add (.reg 1) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101e38 0x101e3b (addR32R32Effect 0x101e38 3 1 10) := {
      pre := (fun s ↦ s.RIP = 0x101e38)
      code := codeRange 0x101e38 [0x44, 0x1, 0xd1]
      step := add_r32_r32_rex_effect_step 0x101e38 0x44 0xd1 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e38 3 (by decide +kernel)
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
  have h12 : RunWords 0x101e3b 0x101e41 [.add (.reg 1) (.immediate 0xa679438e)] := by
    let ex : InstructionExecution 0x101e3b 0x101e41 (addR32Imm32Effect 0x101e3b 6 1 0xa679438e) := {
      pre := (fun s ↦ s.RIP = 0x101e3b)
      code := codeRange 0x101e3b [0x81, 0xc1, 0x8e, 0x43, 0x79, 0xa6]
      step := add_r32_imm32_effect_step 0x101e3b 0xc1 0xa679438e (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e3b 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 1) (.immediate 0xa679438e)) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h13 : RunWords 0x101e41 0x101e44 [.rol (.reg 1) 17] := by
    let ex : InstructionExecution 0x101e41 0x101e44 (rolR32Effect 0x101e41 3 1 17) := {
      pre := (fun s ↦ s.RIP = 0x101e41)
      code := codeRange 0x101e41 [0xc1, 0xc1, 0x11]
      step := rol_r32_imm8_effect_step 0x101e41 0xc1 0x11 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e41 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 1) 17) (dst := 1) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h14 : RunWords 0x101e44 0x101e46 [.add (.reg 1) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101e44 0x101e46 (addR32R32Effect 0x101e44 2 1 0) := {
      pre := (fun s ↦ s.RIP = 0x101e44)
      code := codeRange 0x101e44 [0x1, 0xc1]
      step := add_r32_r32_effect_step 0x101e44 0xc1 (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e44 2 (by decide +kernel)
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
  simpa only [segment15, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (h14)))))))))))))

theorem segment16_runs [Bindings] :
    RunWords 0x101e46 0x101e78 segment16 := by
  have h1 : RunWords 0x101e46 0x101e49 [.mov (.reg 10) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101e46 0x101e49 (movR32R32Effect 0x101e46 3 10 1) := {
      pre := (fun s ↦ s.RIP = 0x101e46)
      code := codeRange 0x101e46 [0x41, 0x89, 0xca]
      step := mov_r32_r32_rex_effect_step 0x101e46 0x41 0xca (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e46 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 10) (.location (.reg 1))) (dst := 10) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h2 : RunWords 0x101e49 0x101e4c [.and (.reg 10) (.location (.reg 0))] := by
    let ex : InstructionExecution 0x101e49 0x101e4c (andR32R32Effect 0x101e49 3 10 0) := {
      pre := (fun s ↦ s.RIP = 0x101e49)
      code := codeRange 0x101e49 [0x41, 0x21, 0xc2]
      step := and_r32_r32_rex_effect_step 0x101e49 0x41 0xc2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e49 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 10) (.location (.reg 0))) (dst := 10) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h3 : RunWords 0x101e4c 0x101e4f [.mov (.reg 13) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101e4c 0x101e4f (movR32R32Effect 0x101e4c 3 13 1) := {
      pre := (fun s ↦ s.RIP = 0x101e4c)
      code := codeRange 0x101e4c [0x41, 0x89, 0xcd]
      step := mov_r32_r32_rex_effect_step 0x101e4c 0x41 0xcd (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e4c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 13) (.location (.reg 1))) (dst := 13) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h4 : RunWords 0x101e4f 0x101e52 [.not (.reg 13)] := by
    let ex : InstructionExecution 0x101e4f 0x101e52 (notR32Effect 0x101e4f 3 13) := {
      pre := (fun s ↦ s.RIP = 0x101e4f)
      code := codeRange 0x101e4f [0x41, 0xf7, 0xd5]
      step := not_r32_rex_effect_step 0x101e4f 0x41 0xd5 (by simp [RexNoWPrefix]) (by decide) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1e4f 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .not (.reg 13)) (dst := 13) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h5 : RunWords 0x101e52 0x101e56 [.lea (.reg 15) (.reg 3) (.reg 12)] := by
    let ex : InstructionExecution 0x101e52 0x101e56 (Register.leaR32Effect 0x101e52 4 15 (.sib 3
      (some 12) 0 .none)) := {
      pre := (fun s ↦ s.RIP = 0x101e52)
      code := codeRange 0x101e52 [0x46, 0x8d, 0x3c, 0x23]
      step := Register.lea_r32_rex_effect_step 0x101e52 0x46 (by simp [RexNoWPrefix]) 7 (.sib 3
        (some 12) 0 .none) (by decide) (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e52 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .lea (.reg 15) (.reg 3) (.reg 12)) (dst := 15) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h6 : RunWords 0x101e56 0x101e59 [.and (.reg 12) (.location (.reg 13))] := by
    let ex : InstructionExecution 0x101e56 0x101e59 (andR32R32Effect 0x101e56 3 12 13) := {
      pre := (fun s ↦ s.RIP = 0x101e56)
      code := codeRange 0x101e56 [0x45, 0x21, 0xec]
      step := and_r32_r32_rex_effect_step 0x101e56 0x45 0xec (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e56 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .and (.reg 12) (.location (.reg 13))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h7 : RunWords 0x101e59 0x101e5c [.or (.reg 12) (.location (.reg 10))] := by
    let ex : InstructionExecution 0x101e59 0x101e5c (Register.orR32R32Effect 0x101e59 3 12 10) := {
      pre := (fun s ↦ s.RIP = 0x101e59)
      code := codeRange 0x101e59 [0x45, 0x9, 0xd4]
      step := Register.or_r32_r32_rex_effect_step 0x101e59 0x45 0xd4 (by simp [RexNoWPrefix]) (by
        decide)
      present := fun hc ↦ program_text_slice hc 0x1e59 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .or (.reg 12) (.location (.reg 10))) (dst := 12) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h8 : RunWords 0x101e5c 0x101e5f [.mov (.reg 7) (.location (.input 15))] := by
    let ex : InstructionExecution 0x101e5c 0x101e5f (movR32M32NoRexEffect 0x101e5c 7 (.base 6 (.d8
      0x3c))) := {
      pre := (LoadPre 0x101e5c (fun s ↦ ((.base 6 (.d8 0x3c)) : AddrMode).addr s (0x101e5c + 3)) 4)
      code := codeRange 0x101e5c [0x8b, 0x7e, 0x3c]
      step := mov_r32_m32_noRex_effect_step 0x101e5c 7 (.base 6 (.d8 0x3c)) (by decide) (by decide)
        (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e5c 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        refine ⟨hRip, ?_⟩
        have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
        have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
        x86_norm [hs, hi]
        exact hd.readable_input 60 4 (by decide)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .mov (.reg 7) (.location (.input 15))) (dst := 7) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h9 : RunWords 0x101e5f 0x101e61 [.add (.reg 2) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101e5f 0x101e61 (addR32R32Effect 0x101e5f 2 2 7) := {
      pre := (fun s ↦ s.RIP = 0x101e5f)
      code := codeRange 0x101e5f [0x1, 0xfa]
      step := add_r32_r32_effect_step 0x101e5f 0xfa (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e5f 2 (by decide +kernel)
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
  have h10 : RunWords 0x101e61 0x101e65 [.mov (.stack 48) (.location (.reg 7))] := by
    let ex : InstructionExecution 0x101e61 0x101e65 (Store.movM32R32NoRexEffect 0x101e61 7 (.sib 4
      none 0 (.d8 0x30))) := {
      pre := (Md5.Proofs.Memory.StorePre 0x101e61 4 (fun s ↦ ((.sib 4 none 0 (.d8 0x30)) :
        AddrMode).addr s (0x101e61 + 4)) 4)
      code := codeRange 0x101e61 [0x89, 0x7c, 0x24, 0x30]
      step := Store.mov_m32_r32_noRex_effect_step 0x101e61 7 (.sib 4 none 0 (.d8 0x30)) (by decide)
        (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e61 4 (by decide +kernel)
      enabled := by
        intro s stack input buffer words hd hRip
        apply hd.store_stack (offset := 48) (length := 4) hRip ?_ (by decide) ?_
        · have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
          x86_norm [hs]
        · exact program_text_range 0x1e61 4 (by decide +kernel)
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    refine ex.run_stack32 (instruction := .mov (.stack 48) (.location (.reg 7))) (dst := 48)
      (value := fun s ↦ (Operand.reg 7 : Operand 32).read s)
      ?_ (by decide) (by decide) (by decide) ?_
    · intro s stack input buffer words hd
      have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
      x86_norm [hs]
    · intro s stack input buffer words _
      md5_word_model
      all_goals rfl
  have h11 : RunWords 0x101e65 0x101e68 [.add (.reg 2) (.location (.reg 12))] := by
    let ex : InstructionExecution 0x101e65 0x101e68 (addR32R32Effect 0x101e65 3 2 12) := {
      pre := (fun s ↦ s.RIP = 0x101e65)
      code := codeRange 0x101e65 [0x44, 0x1, 0xe2]
      step := add_r32_r32_rex_effect_step 0x101e65 0x44 0xe2 (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e65 3 (by decide +kernel)
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
  have h12 : RunWords 0x101e68 0x101e6e [.add (.reg 2) (.immediate 0x49b40821)] := by
    let ex : InstructionExecution 0x101e68 0x101e6e (addR32Imm32Effect 0x101e68 6 2 0x49b40821) := {
      pre := (fun s ↦ s.RIP = 0x101e68)
      code := codeRange 0x101e68 [0x81, 0xc2, 0x21, 0x8, 0xb4, 0x49]
      step := add_r32_imm32_effect_step 0x101e68 0xc2 0x49b40821 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e68 6 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .add (.reg 2) (.immediate 0x49b40821)) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h13 : RunWords 0x101e6e 0x101e70 [.and (.reg 5) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101e6e 0x101e70 (andR32R32Effect 0x101e6e 2 5 1) := {
      pre := (fun s ↦ s.RIP = 0x101e6e)
      code := codeRange 0x101e6e [0x21, 0xcd]
      step := and_r32_r32_effect_step 0x101e6e 0xcd (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e6e 2 (by decide +kernel)
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
  have h14 : RunWords 0x101e70 0x101e73 [.add (.reg 5) (.location (.reg 15))] := by
    let ex : InstructionExecution 0x101e70 0x101e73 (addR32R32Effect 0x101e70 3 5 15) := {
      pre := (fun s ↦ s.RIP = 0x101e70)
      code := codeRange 0x101e70 [0x44, 0x1, 0xfd]
      step := add_r32_r32_rex_effect_step 0x101e70 0x44 0xfd (by simp [RexNoWPrefix]) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e70 3 (by decide +kernel)
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
  have h15 : RunWords 0x101e73 0x101e76 [.rol (.reg 2) 22] := by
    let ex : InstructionExecution 0x101e73 0x101e76 (rolR32Effect 0x101e73 3 2 22) := {
      pre := (fun s ↦ s.RIP = 0x101e73)
      code := codeRange 0x101e73 [0xc1, 0xc2, 0x16]
      step := rol_r32_imm8_effect_step 0x101e73 0xc2 0x16 (by decide) (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e73 3 (by decide +kernel)
      enabled := by
        intro s stack input buffer words _ hRip
        exact hRip
      next := fun _ ↦ rfl
      low := by decide
      high := by decide }
    apply ex.run_reg (instruction := .rol (.reg 2) 22) (dst := 2) (fun _ ↦ rfl)
      (by decide) (by decide) (by decide) (by decide)
    intro s stack input buffer words hd
    have hs : (Operand.reg (BitVec.ofNat 5 4) : Operand 64).read s = stack := hd.stackPointer
    have hi : (Operand.reg (BitVec.ofNat 5 6) : Operand 64).read s = input := hd.inputPointer
    md5_word_model
    all_goals x86_norm [hs, hi, BitVec.shiftLeft_zero, BitVec.add_zero,
      read_reg64_low32, read_mem64_low32, BitVec.setWidth_add]
    all_goals simp [Operand.read]
  have h16 : RunWords 0x101e76 0x101e78 [.add (.reg 2) (.location (.reg 1))] := by
    let ex : InstructionExecution 0x101e76 0x101e78 (addR32R32Effect 0x101e76 2 2 1) := {
      pre := (fun s ↦ s.RIP = 0x101e76)
      code := codeRange 0x101e76 [0x1, 0xca]
      step := add_r32_r32_effect_step 0x101e76 0xca (by decide)
      present := fun hc ↦ program_text_slice hc 0x1e76 2 (by decide +kernel)
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
  simpa only [segment16, List.cons_append, List.nil_append] using h1.seq (h2.seq (h3.seq (h4.seq
    (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (h14.seq (h15.seq
    (h16)))))))))))))))

end Md5.Proofs.Block.Rounds
