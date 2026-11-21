import AesGcm.Proofs.Machine.CTR.Loop.CallAdvance

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice

theorem mix_step
    (use256 mix3 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (keyWords : Vector (BitVec 16) (keyWords use256))
    (planes : Planes) (loc : LIR.lifted.Location)
    (hwork : CipherWorkingState use256 code fr args mem sp keyWords loc)
    (hlabel : loc.label = batchMixLabel use256 mix3)
    (hBase : (loc.arguments[3]'(by change 3 < 53; decide)).get 64 = sp + 8)
    (hWords : WordsAt loc.store (sp + 8) 64 (Vector.ofFn planes)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp keyWords next ∧
      next.label = (if use256 then (if mix3 then .l10932e else .l109037)
        else (if mix3 then .l107e9e else .l107ba7)) ∧
      WordsAt next.store (sp + 8) 64
        (Vector.ofFn ((if mix3 then mixColumns3 else mixColumns1) planes)) ∧
      (∀ r : Fin Reg.count, r.val ∈ [3, 4, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        next.arguments[r] = loc.arguments[r]) := by
  have low := hwork.stack.readable.low
  have stack : Writable code loc.store (sp - 8) 8 :=
    hwork.stack.sub (by bv_omega) (by bv_omega)
  have spVal := congrArg (Value.get 64) hwork.stackPointer
  obtain ⟨ca, call, label, h4, h7, store, keep, typed, frame⟩ :=
    batch_mix_call use256 mix3 code hcode loc.arguments loc.store sp (sp + 8)
      hwork.typed spVal hBase stack
  cases loc with
  | mk lab vals m =>
    change lab = _ at hlabel
    subst lab
    cases mix3
    · exact pushed_call_advance (kind := 1) hcode hwork call label typed h4 h7
        (fun h => absurd h (by decide)) store keep frame (by cases use256 <;> decide) hWords
    · exact pushed_call_advance (kind := 2) hcode hwork call label typed h4 h7
        (fun h => absurd h (by decide)) store keep frame (by cases use256 <;> decide) hWords

end AesGcm.Proofs.Machine.CTR.Loop
