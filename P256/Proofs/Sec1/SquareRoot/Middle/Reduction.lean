import P256.Proofs.Sec1.SquareRoot.Middle.Wide
import P256.Proofs.Sec1.SquareRoot.Square.Reduction

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Middle

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def reductionLayout : StackCallLayout 2176 64 32 112 :=
  ⟨592,104,536,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem reduction_pre [Bindings] {s v : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (saved : SavedState s v)
    (rsp : stackPtr v = stackPtr s - 592)
    (base : CalleePre v boundary 0x1133f0 64 32 112)
    (output : v.regValue .rdi = stackPtr s - 536)
    (address : v.regValue .rdx = stackPtr s - 216)
    (modulus : Nat256At v (v.regValue .rdx) P256.Spec.Operations.domain.p)
    (inverse : v.regValue .rcx = 1) : Square.ReductionPre v boundary := by
  have bounds := stack_bounds pre.stack
  have hm : (v.regValue .rdx).toNat = (stackPtr s).toNat - 216 := by
    rw [address]; exact stack_sub_toNat pre.stack (by decide)
  have ho : (v.regValue .rdi).toNat = (stackPtr s).toNat - 536 := by
    rw [output]; exact stack_sub_toNat pre.stack (by decide)
  have hs : (stackPtr v).toNat = (stackPtr s).toNat - 592 := by
    rw [rsp]; exact stack_sub_toNat pre.stack (by decide)
  refine ⟨base,?_,?_,?_,?_,modulus,inverse⟩
  · change (v.regValue .rdx).toNat + 32 < 2^32
    rw [hm]; omega
  · intro a ha
    apply Option.isSome_iff_exists.mp
    apply saved.allocated
    apply Option.isSome_iff_exists.mpr
    apply pre.stack.2.1
    apply stack_buffer_contains pre.stack (offset := 216) (len := 32) (by decide) (by decide)
    change (v.regValue .rdx).toNat ≤ a.toNat ∧ a.toNat < (v.regValue .rdx).toNat + 32 at ha
    rw [address] at ha
    exact ha
  · intro a ha hb
    change (v.regValue .rdx).toNat ≤ a ∧ a < (v.regValue .rdx).toNat + 32 at ha
    change (v.regValue .rdi).toNat ≤ a ∧ a < (v.regValue .rdi).toNat + 32 at hb
    rw [hm] at ha
    rw [ho] at hb
    omega
  · intro a ha hb
    change (v.regValue .rdx).toNat ≤ a ∧ a < (v.regValue .rdx).toNat + 32 at ha
    change (stackPtr v).toNat - 112 ≤ a ∧ a < (Stack.region v 112).start + (Stack.region v 112).size at hb
    rw [hm] at ha
    rw [stack_region_end,hs] at hb
    omega

theorem reduction_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x beta : Nat}
    (pre : Pre s boundary) (state : WideResult s t x beta) :
    ∃ n u, Advances boundary n t u ∧ FrameState s u ∧ u.RIP = 0x11450a ∧
      MontgomeryAt u (stackPtr s - 392) x ∧ MontgomeryAt u (stackPtr s - 576) beta ∧
      MontgomeryAt u (stackPtr s - 536) (beta*beta % P256.Spec.Operations.domain.p) := by
  obtain ⟨n1,t1,run1,ready1,_,setup⟩ := reductionSetup_run boundary pre.outerBoundary t
    (readyToStep state.frame.machine state.frame.bindingsSupported)
    (reductionSetup_code state.frame.loaded) state.rip
  have state1 := state.frame.of_registers pre ready1 setup.agrees (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [reductionSetupEffect, Effect.components])
    (by simp [reductionSetupEffect, Effect.components, Component.Covers])
  have mem1 := setup.agrees.external (by simp [reductionSetupEffect, Effect.components, Component.Covers])
  obtain ⟨v,run2,saved,rsp,effect⟩ := call_entry pre state1 0x14505 0xffffeee6
    (by decide) (by decide +kernel) (inProgram_of_textOffset 0x133f0 (by decide)) setup.rip
  have vin : v.regValue .rsi = stackPtr s - 104 :=
    (effect.agrees.read (r := 6) (n := 64) (by simp)).trans (setup.writes.2.2.1.trans state.r12)
  have vout : v.regValue .rdi = stackPtr s - 536 :=
    (effect.agrees.read (r := 7) (n := 64) (by simp)).trans (setup.writes.1.trans (state.frame.stack_address 48))
  have vm : v.regValue .rdx = stackPtr s - 216 :=
    (effect.agrees.read (r := 2) (n := 64) (by simp)).trans (setup.writes.2.2.2.trans state.r15)
  have ret : (returnBoundary v).rip = 0x11450a := (callEffect_stack effect).1
  have base : CalleePre v boundary 0x1133f0 64 32 112 := CalleePre.of_stack pre reductionLayout
    saved.bindingsSupported saved.machine saved.directionFlag saved.loaded saved.allocated
    effect.rip rsp vin vout (by rw [ret]; exact inProgram_of_textOffset 0x1450a (by decide))
  have bytes {offset len i : Nat} (ho : offset ≤ 584) (hl : len ≤ offset+8) (hi : i < len) :=
    (ScalarFrame.call_byte (by decide : 584+16 ≤ 2^64) state1.rsp effect ho hl hi).trans
      (congrArg (fun m : Ram => m[_]?) mem1)
  have modulus : Nat256At v (v.regValue .rdx) P256.Spec.Operations.domain.p := by
    rw [vm]
    exact ⟨state.modulus.1, fun i hi => (bytes (by decide) (by decide) hi).trans (state.modulus.2 i hi)⟩
  have cp := reduction_pre pre saved rsp base vout vm modulus
    ((effect.agrees.read (r := 1) (n := 64) (by simp)).trans setup.writes.2.1)
  have input : Bytes v.external (v.regValue .rsi) 64
      (fun i => UInt8.ofNat (((beta * 2^256 % P256.Spec.Operations.domain.p) *
        (beta * 2^256 % P256.Spec.Operations.domain.p)) / 256^i % 256)) := by
    rw [vin]
    exact fun i hi => (bytes (by decide) (by decide) hi).trans (state.square i hi)
  have bound : (beta * 2^256 % P256.Spec.Operations.domain.p) *
      (beta * 2^256 % P256.Spec.Operations.domain.p) < P256.Spec.Operations.domain.p * 2^256 := by
    have lt := Nat.mod_lt (beta * 2^256) Field.Montgomery.p_pos
    exact Nat.mul_lt_mul_of_lt_of_lt lt (Nat.lt_trans lt Field.Montgomery.p_lt_radix)
  obtain ⟨u,result,value⟩ := Square.reduction_correct cp input bound
  obtain ⟨n3,run3⟩ := result.execution
  refine ⟨n1+1+n3,u,(run1.trans run2).trans run3,
    stack_result_frame pre saved rsp vout (by decide) (by decide) (by decide) result,
    result.rip.trans ret,?_,?_,?_⟩
  · apply state.input.of_bytes_eq
    intro i hi
    exact (stack_result_byte pre rsp vout result (by decide) (by decide) (by decide)
      (by decide) hi).trans (bytes (by decide) (by decide) hi)
  · apply state.copy.of_bytes_eq
    intro i hi
    exact (stack_result_byte pre rsp vout result (by decide) (by decide) (by decide)
      (by decide) hi).trans (bytes (by decide) (by decide) hi)
  · rw [vout] at value
    exact Field.montgomeryAt_product value

end P256.Proofs.Sec1.SquareRoot.Middle
