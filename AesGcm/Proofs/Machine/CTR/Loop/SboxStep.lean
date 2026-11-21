import AesGcm.Proofs.Machine.CTR.Loop.CallAdvance

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice


set_option maxHeartbeats 600000 in
theorem sbox_step (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (keyWords : Vector (BitVec 16) (keyWords use256))
    (planes : Planes) (loc : LIR.lifted.Location)
    (hwork : CipherWorkingState use256 code fr args mem sp keyWords loc)
    (hlabel : loc.label = (if use256 then .l1090d1 else .l107c41))
    (hWords : WordsAt loc.store (sp + 8) 64 (Vector.ofFn planes)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp keyWords next ∧
      next.label = (if use256 then .l1090e0 else .l107c50) ∧
      WordsAt next.store (sp + 8) 64
        (Vector.ofFn (Fixslice.subBytes planes)) ∧
      (∀ r : Fin Reg.count, r.val ∈ [3, 4, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        next.arguments[r] = loc.arguments[r] ) := by
  have low := hwork.stack.readable.low
  have stack : Writable code loc.store (sp - 8) 8 :=
    hwork.stack.sub (by bv_omega) (by bv_omega)
  have spVal := congrArg (Value.get 64) hwork.stackPointer
  obtain ⟨ca, call, label, h4, h7, h6, store, keep, typed, frame⟩ :=
    batch_sbox_call use256 code hcode loc.arguments loc.store sp hwork.typed spVal stack
  cases loc with
  | mk lab vals m =>
    change lab = _ at hlabel
    subst lab
    exact pushed_call_advance (kind := 0) hcode hwork call label typed h4 h7
      (fun _ => h6) store keep frame (by cases use256 <;> decide) hWords

end AesGcm.Proofs.Machine.CTR.Loop
