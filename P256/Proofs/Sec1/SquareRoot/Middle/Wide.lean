import P256.Proofs.Sec1.SquareRoot.Middle.Prepare
import P256.Proofs.Sec1.SquareRoot.Square.Wide

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Middle

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def wideLayout : StackCallLayout 2176 32 64 88 :=
  ⟨592,248,104,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

structure WideResult [Bindings] (s t : RamState) (x beta : Nat) : Prop where
  frame : FrameState s t
  rip : t.RIP = 0x1144f5
  r12 : t.regValue .r12 = stackPtr s - 104
  r15 : t.regValue .r15 = stackPtr s - 216
  input : MontgomeryAt t (stackPtr s - 392) x
  copy : MontgomeryAt t (stackPtr s - 576) beta
  modulus : Nat256At t (stackPtr s - 216) P256.Spec.Operations.domain.p
  square : Bytes t.external (stackPtr s - 104) 64
    (fun i => UInt8.ofNat (((beta * 2^256 % P256.Spec.Operations.domain.p) *
      (beta * 2^256 % P256.Spec.Operations.domain.p)) / 256^i % 256))

theorem wide_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x beta : Nat}
    (pre : Pre s boundary) (state : WideCallState s t x beta) :
    ∃ n u, Advances boundary n t u ∧ WideResult s u x beta := by
  obtain ⟨v,run,saved,rsp,effect⟩ := call_entry pre state.frame 0x144f0 0x86ab
    (by decide) (by decide +kernel) (inProgram_of_textOffset 0x1cba0 (by decide)) state.rip
  have vin : v.regValue .rsi = stackPtr s - 248 :=
    (effect.agrees.read (r := 6) (n := 64) (by simp)).trans state.rsi
  have vout : v.regValue .rdi = stackPtr s - 104 :=
    (effect.agrees.read (r := 7) (n := 64) (by simp)).trans state.rdi
  have ret : (returnBoundary v).rip = 0x1144f5 := (callEffect_stack effect).1
  have cp : Square.WidePre v boundary := CalleePre.of_stack pre wideLayout
    saved.bindingsSupported saved.machine saved.directionFlag saved.loaded saved.allocated
    effect.rip rsp vin vout (by rw [ret]; exact inProgram_of_textOffset 0x144f5 (by decide))
  have bytes {offset len i : Nat} (ho : offset ≤ 584) (hl : len ≤ offset+8) (hi : i < len) :=
    ScalarFrame.call_byte (by decide : 584+16 ≤ 2^64) state.frame.rsp effect ho hl hi
  have value : MontgomeryAt v (v.regValue .rsi) beta := by
    rw [vin]
    exact state.candidate.of_bytes_eq (fun i hi => bytes (by decide) (by decide) hi)
  obtain ⟨u,result,square⟩ := Square.wide_square_correct cp
    ((effect.agrees.read (r := 2) (n := 64) (by simp)).trans state.rdx) value.2
  obtain ⟨n,execution⟩ := result.execution
  have preserved {offset len i : Nat} (ho : offset ≤ 584) (hl : len ≤ offset+8)
      (apart : offset+64 ≤ 104 ∨ 104+len ≤ offset) (hi : i < len) :=
    (stack_result_byte pre rsp vout result (by decide) ho hl apart hi).trans (bytes ho hl hi)
  refine ⟨1+n,u,run.trans execution,
    stack_result_frame pre saved rsp vout (by decide) (by decide) (by decide) result,
    result.rip.trans ret,?_,?_,?_,?_,?_,?_⟩
  · exact (result.calleeSaved .r12 (by simp)).trans
      ((effect.agrees.read (r := 12) (n := 64) (by simp)).trans state.r12)
  · exact (result.calleeSaved .r15 (by simp)).trans
      ((effect.agrees.read (r := 15) (n := 64) (by simp)).trans state.r15)
  · exact state.input.of_bytes_eq (fun i hi => preserved (by decide) (by decide) (by decide) hi)
  · exact state.copy.of_bytes_eq (fun i hi => preserved (by decide) (by decide) (by decide) hi)
  · exact ⟨state.modulus.1, fun i hi =>
      (preserved (by decide) (by decide) (by decide) hi).trans (state.modulus.2 i hi)⟩
  · simpa only [vout] using square

end P256.Proofs.Sec1.SquareRoot.Middle
