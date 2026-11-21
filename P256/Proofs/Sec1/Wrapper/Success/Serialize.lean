import P256.Proofs.Sec1.Wrapper.Success.Relocate
import P256.Proofs.Sec1.Wrapper.Success.Return
import P256.Proofs.Sec1.Wrapper.Success.Sites
import P256.Proofs.Sec1Serialize

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

theorem serialize [bindings : Bindings] {initial s : RamState}
    {input : ByteArray} {slices : Array Input} {point : Curve.Point}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x10184b) (affine : Sec1.AffineAt s (stackPtr initial - 224) point) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = 0x101870 ∧
      (MemoryRegion.mk (stackPtr initial - 232).toNat 65).HasBytes t.external
        (Sec1Serialize.encodedPoint point) ∧
      MemoryWriteFrame s t (wrapperRegions publicKeyFromSec1Bytes initial) ∧
      t.regValue .r14 = s.regValue .r14 ∧ t.regValue .rbx = s.regValue .rbx := by
  obtain ⟨n,a,ha,sa,ipa,src,dst,zero,affineA,fa⟩ :=
    relocate valid state outside rip affine
  obtain ⟨b,called⟩ := call valid outside sa serializeSite ipa src dst
  have affineB : Sec1.AffineAt b (b.regValue .rsi) point := by
    rw [called.input]
    exact affineA.of_bytes_eq (called.bytes 96 65 (by decide) (by decide))
  obtain ⟨t,result,_,bytes⟩ := Sec1Serialize.serializer_correct bindings b
    (returnBoundary initial) point called.pre affineB
    ((called.registers .rdx (by decide)).trans zero)
  obtain ⟨st,ipt,regs⟩ := returned valid sa called result (by decide)
  obtain ⟨m,run⟩ := result.execution
  refine ⟨_,t,(ha.trans called.execution).trans run,st,ipt,?_,?_,?_,?_⟩
  · change (MemoryRegion.mk (b.regValue .rdi).toNat 65).HasBytes t.external _ at bytes
    rwa [called.output] at bytes
  · have first : MemoryWriteFrame s a (wrapperRegions publicKeyFromSec1Bytes initial) := by
      apply fa.memoryWriteFrame
      intro c hc addr covered
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      exact ⟨callStack publicKeyFromSec1Bytes initial, by simp [wrapperRegions],
        stack_component_within valid.stackAvailable.1 (by decide) (by decide) covered⟩
    apply memoryWriteFrame_trans first
    intro addr ha
    apply result_frame valid called result addr
    intro region hr hin
    have eq : region = Stack.region initial 4048 := by simpa using hr
    subst region
    exact ha (callStack publicKeyFromSec1Bytes initial) (by simp [wrapperRegions])
      (stack_contains_callStack hin)
  · exact (regs .r14 (by simp)).trans (fa.read (n := 64) (r := 14) (by simp))
  · exact (regs .rbx (by simp)).trans (fa.read (n := 64) (r := 3) (by simp))

end P256.Proofs.Sec1.Wrapper.Success
