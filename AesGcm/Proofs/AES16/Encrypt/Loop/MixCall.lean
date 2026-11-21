import AesGcm.Proofs.Machine.LIR.Fn105100
import AesGcm.Proofs.Machine.LIR.Fn106960
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

attribute [local irreducible] memStore memLoad

set_option hygiene false in
local macro "mixCall_proof" entry:term "," pc:num "," hc:ident "," bytes:ident : tactic => `(tactic| (
  have hStackLow := hStack.readable.low
  have hhelperApart {mem : Ram} {a : BitVec 64} {n : Nat} (h : Writable code mem a n) :
      RangeApart a n $pc 8 := by
    have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x ($hc:ident x hx))
    have hl : ($bytes:ident).length = 8 := by decide +kernel
    rw [hl] at hx
    exact hx.apart
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · change LIR.program.runBlock (dialect code) ⟨$entry, _, mem⟩ = _
    cfg_eval
    runtime_guards call
    rfl
  · refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish []
    · runtime_finish [span]
  ))

set_option maxHeartbeats 600000 in
theorem mix_call_runBlock (use256 third : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (hTypes : GPRsTyped args)
    (hStack : Writable code mem (args[4].get 64 - 8) 8) :
    ∃ (next : LIR.lifted.Location) (frame : LIR.lifted.StackFrame),
      LIR.program.runBlock (dialect code)
        ⟨(if third then (if use256 then .l106ce3 else .l10546a)
          else (if use256 then .l106a11 else .l1051a0)), args, mem⟩ = .call next frame ∧
      next.label = (if third then .l100580 else .l100000) ∧
      frame = { target := (if third then (if use256 then .l106ceb else .l105472) else (if use256 then .l106a19 else .l1051a8)), kept := #v[], arity := rfl, guard := some ⟨64, if third then (if use256 then 0x106ceb else 0x105472) else (if use256 then 0x106a19 else 0x1051a8)⟩ } ∧
      next.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      next.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[14].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      memLoad next.store (args[4].get 64 - 8) 64 =
        (if third then (if use256 then 0x106ceb else 0x105472) else (if use256 then 0x106a19 else 0x1051a8)) ∧
      RamWriteFrame mem next.store [span (args[4].get 64 - 8) 8] := by
  dsimp only [LIR.lifted]
  revert hTypes hStack
  refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
    a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
  clear args
  intro hTypes hStack
  change Writable code mem (a4.get 64 - 8) 8 at hStack
  cases use256 <;> cases third
  · mixCall_proof (.l1051a0), 0x1051a0, LIR.code_l1051a0, LIR.bytes_l1051a0
  · mixCall_proof (.l10546a), 0x10546a, LIR.code_l10546a, LIR.bytes_l10546a
  · mixCall_proof (.l106a11), 0x106a11, LIR.code_l106a11, LIR.bytes_l106a11
  · mixCall_proof (.l106ce3), 0x106ce3, LIR.code_l106ce3, LIR.bytes_l106ce3

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
