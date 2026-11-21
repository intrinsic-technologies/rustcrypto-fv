import P256.Proofs.Signing.Core.Iteration.Output.Memory
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Ecdh.Normalize.Conversion.Wrapper
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program SecretKeyFromBytes.Scalar
open NextNonce (scalarFrame coreFrame base_add)

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem convert_call {x input : Nat} (pre : SignPre s boundary) (frame : Frame s t)
    (offset : Nat) (disp : BitVec 32) (bound : offset+5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress+BitVec.ofNat 64 offset) 5 (disp.signExtend 64) = 0x107d00)
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 offset)
    (inputBound : input+32 ≤ 2280) (inputApart : input+32 ≤ 528 ∨ 560 ≤ input)
    (src : t.regValue .rsi = frameBase s+BitVec.ofNat 64 input)
    (dst : t.regValue .rdi = frameBase s+528)
    (value : Field.MontgomeryAt t (frameBase s+BitVec.ofNat 64 input) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress+BitVec.ofNat 64 offset+5#64 ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r) ∧
      (∀ i < 65, u.external[s.regValue .rdi+BitVec.ofNat 64 i]? = t.external[s.regValue .rdi+BitVec.ofNat 64 i]?) ∧
      (∀ i < 32, u.external[frameBase s+136+BitVec.ofNat 64 i]? = t.external[frameBase s+136+BitVec.ofNat 64 i]?) := by
  let layout : StackCallLayout 4584 32 32 40 :=
    ⟨2288,2280-input,1752,by decide,by decide,by omega,by decide,by omega,by decide,by omega⟩
  obtain ⟨n,u,run,fu,ipu,_,regs,keep,memory⟩ := FieldCall.unary_call (resultAt:=fun u p => Nat256At u p x)
    pre.toCalleePre (scalarFrame frame) layout rfl (by change 32+48 ≤ 1752; decide) offset disp bound bytes target
    (by decide) (inProgram_of_textOffset 0x7d00 (by decide))
    (fun v hp hx => Ecdh.Normalize.Conversion.callee_correct hp hx) rip
    (src.trans (base_add s (by omega))) (dst.trans (base_add s (by decide)))
    (by simpa only [layout,← base_add s (offset:=input) (by omega)] using value)
  refine ⟨n,u,run,coreFrame fu,ipu,regs,output_of_stack_frame pre memory,?_⟩
  intro i hi
  have h := keep 2144 32 (by decide) (by decide) (.inr (by change 1752+32 ≤ 2144; decide)) i hi
  simpa only [← base_add s (offset:=136) (by decide),BitVec.ofNat_eq_ofNat] using h

theorem encode_call {value : Nat} (pre : SignPre s boundary) (frame : Frame s t)
    (rip : t.RIP = 0x10d3d7) (src : t.regValue .rsi = frameBase s+176)
    (dst : t.regValue .rdi = frameBase s+432)
    (scalar : Nat256At t (frameBase s+176) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10d3dc ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],u.regValue r = t.regValue r) ∧
      (∀ i < 65,u.external[s.regValue .rdi+BitVec.ofNat 64 i]? = t.external[s.regValue .rdi+BitVec.ofNat 64 i]?) ∧
      (∀ i < 64,u.external[frameBase s+104+BitVec.ofNat 64 i]? = t.external[frameBase s+104+BitVec.ofNat 64 i]?) := by
  obtain ⟨v,runV,readyV,effect⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) (scalarFrame frame) 0xd3d7 0x5ac4
    (by decide) (by decide +kernel) (by decide) (inProgram_of_textOffset 0x12ea0 (by decide)) rip
  change (callEffect (fun _ => 0x112ea0) 0x10d3dc t).Holds t v at effect
  have cp := local_call_pre pre frame readyV effect (inProgram_of_textOffset 0xd3dc (by decide))
    (reserve:=0) (by decide) (inputBytes:=32) (outputBytes:=32) (by decide) (by decide)
    (by decide) (by decide) (.inl (by decide)) src dst
  have valueV : Nat256At v (v.regValue .rsi) value := by
    have vr : v.regValue .rsi = frameBase s+176 := (effect.agrees.read (n:=64) (r:=6) (by simp)).trans src
    rw [vr]
    exact ⟨scalar.1,fun i hi => (local_call_copy frame effect (offset:=176) (len:=32) (by decide) i hi).trans (scalar.2 i hi)⟩
  obtain ⟨u,result,_,_,_⟩ := Projective.Multiply.Machine.Radix.Serialize.scalar_encode_correct cp valueV
  obtain ⟨n,run⟩ := result.execution
  exact ⟨1+n,u,runV.trans run,after_call pre frame readyV effect result (by decide) (by decide) dst,
    result.rip.trans (callEffect_stack effect).1,call_preserved effect result,
    call_output pre frame effect result (by decide) (by decide) dst,
    local_result_copy pre frame effect result dst (by decide) (by decide) (.inl (by decide))⟩

end P256.Proofs.Signing.Core.Iteration.Output
