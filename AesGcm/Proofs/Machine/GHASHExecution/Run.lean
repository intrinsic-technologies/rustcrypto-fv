import AesGcm.Proofs.Machine.GHASHExecution.Evaluation
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.GHASHExecution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open Lean Meta Elab Tactic

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem multiply_returns (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (fr : Activation)
    (hsp : args[4].get 64 = fr.rsp) (hdi : args[7].get 64 = fr.rdi)
    (hStack : Writable code fr.original (fr.rsp - 128) 128)
    (hState : Writable code fr.original fr.rdi 32)
    (hRetRead : Readable fr.original fr.rsp 8)
    (hRet : memLoad fr.original fr.rsp 64 = fr.ret)
    (hRetLow : fr.ret.toNat < 2 ^ 32)
    (hRoom : fr.low.toNat + 128 ≤ fr.rsp.toNat)
    (hApartNum : fr.rsp.toNat + 8 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 32 ≤ fr.low.toNat) :
    ∃ out, LIR.program.runBlock (dialect code) ⟨.l102bd0, args, fr.original⟩ = .returned out := by
  have hRead := hState.readable
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hReadLow := hRead.low
  have hRetReadLow := hRetRead.low
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n 0x102bd0 2250 := by
    have hh := storeOk_of_codeRange h
      (fun x hx => hcode x (LIR.code_l102bd0 x hx))
    have hn : LIR.bytes_l102bd0.length = 2250 := by decide +kernel
    rw [hn] at hh
    exact hh.apart
  runtime_context [hRet]
  refine ⟨?out, ?eq⟩
  case eq =>
    cfg_eval [LIR.b_l102bd0, LIR.b_l102bd0_1, LIR.b_l102bd0_2, LIR.b_l102bd0_3, LIR.b_l102bd0_4, LIR.b_l102bd0_5, LIR.b_l102bd0_6, LIR.b_l102bd0_7, LIR.b_l102bd0_8, LIR.b_l102bd0_9, LIR.b_l102bd0_10, LIR.b_l102bd0_11, LIR.b_l102bd0_12, LIR.b_l102bd0_13, LIR.b_l102bd0_14, LIR.b_l102bd0_15, LIR.b_l102bd0_16, LIR.b_l102bd0_17, LIR.b_l102bd0_18, LIR.b_l102bd0_19, LIR.b_l102bd0_20, LIR.b_l102bd0_21, LIR.b_l102bd0_22, LIR.b_l102bd0_23, LIR.b_l102bd0_24, LIR.b_l102bd0_25, LIR.b_l102bd0_26, LIR.b_l102bd0_27, LIR.b_l102bd0_28, LIR.b_l102bd0_29, LIR.b_l102bd0_30, hsp, hdi]
    runtime_guards returned
    rfl

end AesGcm.Proofs.Machine.GHASHExecution
