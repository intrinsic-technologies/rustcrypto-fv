import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Standard.Finalize.Hmac
import Hkdf.Proofs.Standard.Finalize.Prepare
import Hkdf.Proofs.Standard.Finalize.Frame

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common
open Hkdf.Proofs.Common.Machine

theorem copy_hmac [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Context initial salt inputs) (completed : Completed initial s salt inputs) :
    ∃ t, Preserved initial t ∧ t.RIP = 0x10173f ∧
      t.regValue .rbx = stackPtr initial - 192 ∧
      HmacAt t (stackPtr initial - 192) (saltKey salt) (concatenation inputs) := by
  obtain ⟨u, buffered, rip, bx, si, dx, di⟩ := prepare_copy ctx completed
  have source : hmacBase initial = stackPtr initial - 400 := by
    change stackPtr initial - 520 + 120 = stackPtr initial - 400
    bv_omega
  have destination : frameBase initial + 328 = stackPtr initial - 192 := by
    change stackPtr initial - 520 + 328 = stackPtr initial - 192
    bv_omega
  rw [destination] at bx di
  obtain ⟨a, stateA, call, ripA, rspA, returnA⟩ := call_copy ctx buffered rip
  have siA : a.regValue .rsi = stackPtr initial - 400 :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans
      (si.trans source)
  have diA : a.regValue .rdi = stackPtr initial - 192 :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans di
  have pre := copy_pre ctx stateA.toRunning ripA rspA siA diA (by
    rw [returnA]
    exact inProgram_of_textOffset 0x173f (by decide))
  have length : a.regValue .rdx = 144 :=
    (call.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans dx
  obtain ⟨t, result, bytes, agrees⟩ := Common.Memory.memcpy_correct pre length (by decide)
  have stateT := copy_state ctx stateA result rspA diA
  have saved := copy_saved ctx result.frame rspA diA
  have callSaved := call_saved buffered.rsp call
    (offset := 48) (size := 56) (by unfold OffsetsApart; decide +kernel) (by decide)
  have persistent := copy_persistent ctx result.frame rspA diA
  have current : Preserved initial t := by
    apply buffered.toPreserved.of_observations stateT.toRunning
      (fun i hi ↦ (saved i hi).trans (callSaved i hi))
    · intro offset member i hi
      have bound : offset ≤ 520 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      have address : frameBase initial + BitVec.ofNat 64 offset =
          stackPtr initial - BitVec.ofNat 64 (520 - offset) := by
        simpa only [show rspOf u = frameBase initial from buffered.rsp] using
          Standard.stack_address (s := u) buffered.rsp bound
      have callSame := call_saved buffered.rsp call (offset := 520 - offset) (size := 8)
        (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;>
            unfold OffsetsApart <;> decide +kernel) (by decide)
      rw [← address] at callSame
      exact (persistent offset member i hi).trans (callSame i hi)
    · rw [show t.regValue .rsp = (returnBoundary a).rsp from result.rsp, returnA]
  have hmacA : HmacAt a (stackPtr initial - 400) (saltKey salt) (concatenation inputs) := by
    apply buffered.hmac.of_copy
    intro i hi
    have same := call_saved buffered.rsp call (offset := 400) (size := 144)
      (by unfold OffsetsApart; decide +kernel) (by decide)
    rw [source]
    exact same i hi
  have hmacT : HmacAt t (stackPtr initial - 192) (saltKey salt) (concatenation inputs) := by
    apply hmacA.of_copy
    intro i hi
    simpa only [siA, diA] using bytes i hi
  refine ⟨t, current, ?_, ?_, hmacT⟩
  · rw [result.rip, returnA]
  · exact (result.abi.1 .rbx (by simp)).trans
      ((call.agrees.read (n := 64) (r := 3) (by simp [callEffect, pushEffect_components])).trans bx)


theorem prepare [Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Context initial salt inputs) (completed : Completed initial s salt inputs) :
    ∃ t, State initial t ∧
      CalleePre t (returnBoundary initial) 0x10dd90 144 176 1264 ∧
      HmacAt t (t.regValue .rsi) (saltKey salt) (concatenation inputs) ∧
      stackPtr t = stackPtr initial - 528 ∧
      t.regValue .rsi = stackPtr initial - 192 ∧
      t.regValue .rdi = stackPtr initial - 400 ∧
      returnBoundary t = ⟨0x10174c, frameBase initial⟩ ∧
      memLoad t.external (frameBase initial + 96) 64 = initial.regValue .r9 ∧
      64 + (concatenation inputs).size < 2^61 := by
  obtain ⟨u, preserved, rip, bx, hmac⟩ := copy_hmac ctx completed
  have outside := (returnBoundary_valid ctx).2.2
  obtain ⟨fuel, v, run, ready, _, setup⟩ := finalizerSetup_run (returnBoundary initial) outside u
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep preserved.machine)
    (finalizerSetup_code preserved.loaded) rip
  have frame : AgreesExcept [.reg 7, .reg 6, .rip] u v := setup.agrees
  have current := Preserved.of_noMem ctx preserved run ready frame
    (by simp [Component.Covers]) (by simp) (by simp)
  have inputHmac : HmacAt v (stackPtr initial - 192) (saltKey salt) (concatenation inputs) := by
    apply hmac.of_copy
    intro i hi
    rw [frame.external (by simp [Component.Covers])]
  have values := setup.writes
  simp only [finalizerSetupEffect, Write.AllHold] at values
  change v.regValue .rdi = stackPtr u + 120 ∧ v.regValue .rsi = u.regValue .rbx at values
  have source : v.regValue .rsi = stackPtr initial - 192 := values.2.trans bx
  have target : v.regValue .rdi = stackPtr initial - 400 := by
    have sp : stackPtr u = frameBase initial := preserved.rsp
    rw [values.1, sp]
    change stackPtr initial - 520 + 120 = stackPtr initial - 400
    bv_omega
  obtain ⟨t, stateT, call, ripT, rspT, returnT⟩ := call_finalizer ctx current setup.rip
  have sourceT : t.regValue .rsi = stackPtr initial - 192 :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans source
  have targetT : t.regValue .rdi = stackPtr initial - 400 :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans target
  have pre := finalizer_pre ctx stateT.toRunning ripT rspT sourceT targetT (by
    rw [returnT]
    exact inProgram_of_textOffset 0x174c (by decide))
  have outputSame := call_saved current.rsp call (offset := 424) (size := 8)
    (by unfold OffsetsApart; decide +kernel) (by decide)
  have outputAddress : frameBase initial + 96 = stackPtr initial - 424 := by
    change stackPtr initial - 520 + 96 = stackPtr initial - 424
    bv_omega
  have outputPointer : memLoad t.external (frameBase initial + 96) 64 = initial.regValue .r9 := by
    calc
      _ = memLoad v.external (frameBase initial + 96) 64 := by
        simpa only [outputAddress] using agrees_memLoad outputSame
      _ = initial.regValue .r9 := current.outputPointer
  refine ⟨t, stateT, pre, ?_, rspT, sourceT, targetT, returnT, outputPointer,
    extract_message_bound ctx.call⟩
  rw [sourceT]
  apply inputHmac.of_copy
  exact call_saved current.rsp call (by unfold OffsetsApart; decide +kernel) (by decide)

end Hkdf.Proofs.Standard.Finalize
