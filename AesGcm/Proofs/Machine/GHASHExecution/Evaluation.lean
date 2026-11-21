import AesGcm.Proofs.Machine.LIR.Fn102bd0.Frame
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.GHASHExecution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
open AesGcm.Proofs.Machine.LIR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem_by multiply_eval (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    program.runBlock (dialect code) ⟨.l102bd0, args, mem⟩ = _ := by
  cfg_eval [b_l102bd0, b_l102bd0_1, b_l102bd0_2, b_l102bd0_3, b_l102bd0_4, b_l102bd0_5, b_l102bd0_6, b_l102bd0_7, b_l102bd0_8, b_l102bd0_9, b_l102bd0_10, b_l102bd0_11, b_l102bd0_12, b_l102bd0_13, b_l102bd0_14, b_l102bd0_15, b_l102bd0_16, b_l102bd0_17, b_l102bd0_18, b_l102bd0_19, b_l102bd0_20, b_l102bd0_21, b_l102bd0_22, b_l102bd0_23, b_l102bd0_24, b_l102bd0_25, b_l102bd0_26, b_l102bd0_27, b_l102bd0_28, b_l102bd0_29, b_l102bd0_30]
  cfg_name_stores
  rfl

runtime_ram_def AesGcm.Proofs.Machine.GHASHExecution.multiplyRam from AesGcm.Proofs.Machine.GHASHExecution.multiply_eval
runtime_output_def AesGcm.Proofs.Machine.GHASHExecution.multiplyOutput from AesGcm.Proofs.Machine.GHASHExecution.multiply_eval

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem multiply_returned_output (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (out : Output Value Ram Reg.count)
    (h : program.runBlock (dialect code) ⟨.l102bd0, args, mem⟩ = .returned out) :
    out = multiplyOutput code args mem := by
  rw [multiply_eval] at h
  runtime_returned_store h

set_option maxRecDepth 8192 in
theorem multiplyOutput_store (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    (multiplyOutput code args mem).store = multiplyRam code args mem := by rfl

set_option maxRecDepth 8192 in
theorem multiplyOutput_tag (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    (multiplyOutput code args mem).tag =
      some ⟨64, memLoad (multiplyRam code args mem) (args[4].get 64) 64⟩ := by
  simp only [multiplyOutput, multiplyRam]

set_option maxRecDepth 8192 in
theorem multiplyOutput_registers (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    (multiplyOutput code args mem).values[4] = ⟨64, args[4].get 64 + 8⟩ ∧
    (multiplyOutput code args mem).values[22] = args[22] ∧
    (multiplyOutput code args mem).values[39] = args[39] ∧
    (multiplyOutput code args mem).values[50] = args[50] ∧
    (multiplyOutput code args mem).values[51] = args[51] := by
  simp only [multiplyOutput]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
theorem multiplyOutput_saved (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (j : Fin 6) :
    (multiplyOutput code args mem).values[
      (match j.val with | 0 => 3 | 1 => 12 | 2 => 13 | 3 => 14 | 4 => 15 | _ => 5)]'(by split <;> decide) =
      ⟨64, memLoad (multiplyRam code args mem)
        (args[4].get 64 - BitVec.ofNat 64 (48 - 8 * j.val)) 64⟩ := by
  rcases j with ⟨j, hj⟩
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [multiplyOutput, multiplyRam, Nat.reduceMul, Nat.reduceSub]; rfl)

set_option maxRecDepth 8192 in
theorem multiplyOutput_typed (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    AesGcm.Proofs.Machine.Runtime.GPRsTyped (multiplyOutput code args mem).values := by
  intro ⟨r, hr⟩
  have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
      r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


end AesGcm.Proofs.Machine.GHASHExecution
