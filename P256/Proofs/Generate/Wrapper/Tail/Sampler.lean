import P256.Proofs.Generate.Wrapper.Entry
import P256.Proofs.Generate.Model.Value

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem sampler_work_frame [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (entry : SamplerEntry initial s input)
    (result : Sampler.Result s t (returnBoundary initial)) :
    MemoryWriteFrame s t #v[workRegion initial] := by
  have bounds := stack_bounds call.stackAvailable.1
  have rsp : (stackPtr s).toNat = (stackPtr initial).toNat-272 := by
    rw [entry.rsp]
    exact stack_sub_toNat call.stackAvailable.1 (by decide)
  have dst : (s.regValue .rdi).toNat = (stackPtr initial).toNat-184 := by
    rw [entry.destination]
    exact stack_sub_toNat call.stackAvailable.1 (by decide)
  have src : (s.regValue .rsi).toNat = (stackPtr initial).toNat-256 := by
    rw [entry.descriptor]
    exact stack_sub_toNat call.stackAvailable.1 (by decide)
  intro a ha
  apply result.frame a
  intro r hr hin
  apply ha (workRegion initial) (by simp)
  have cases : r = registerRegion s .rdi 104 ∨ r = registerRegion s .rsi 16 ∨
      r = Stack.region s 3624 := by simpa [Sampler.writes] using hr
  change (stackPtr initial).toNat-4024 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat-4024+(4024-24)
  rcases cases with rfl | rfl | rfl
  · change (s.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rdi).toNat+104 at hin
    rw [dst] at hin
    constructor <;> omega
  · change (s.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rsi).toNat+16 at hin
    rw [src] at hin
    constructor <;> omega
  · change (stackPtr s).toNat-3624 ≤ a.toNat ∧
      a.toNat < (Stack.region s 3624).start+(Stack.region s 3624).size at hin
    rw [stack_region_end,rsp] at hin
    constructor <;> omega

theorem after_sampler [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (entry : SamplerEntry initial s input)
    (result : Sampler.Result s t (returnBoundary initial)) : State initial t 264 := by
  have memory := sampler_work_frame call entry result
  obtain ⟨n,previous⟩ := entry.execution
  obtain ⟨fuel,run⟩ := result.execution
  refine ⟨⟨n+fuel,previous.trans run⟩,result.bindingsSupported,result.machine,result.loaded,
    result.directionFlag,?_,
    (result.calleeSaved .r14 (by simp)).trans entry.output,
    (result.calleeSaved .rbx (by simp)).trans entry.capacity,
    (work_read call.stackAvailable.1 memory (by decide)).trans entry.savedRbx,
    (work_read call.stackAvailable.1 memory (by decide)).trans entry.savedR14,
    (work_read call.stackAvailable.1 memory (by decide)).trans entry.savedR15,
    ?_,?_,fun a ha => result.allocated a (entry.allocated a ha),
    memoryWriteFrame_trans entry.frame (work_frame call.stackAvailable.1 memory)⟩
  · have h : stackPtr t = stackPtr s+8 := result.rsp
    rw [h]
    rw [entry.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · have h := work_read call.stackAvailable.1 memory (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans entry.returnAddress
  · intro r hr
    apply (result.calleeSaved r ?_).trans (entry.otherRegisters r hr)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

theorem sample_correct [bindings : Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat}
    (sampler : Sampler.Contract bindings)
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d) :
    ∃ t, State initial t 264 ∧ t.RIP = 0x106dad ∧
      t.regValue .r15 = stackPtr initial-184 ∧
      SecretKeyFromBytes.Scalar.Nat256At t (stackPtr initial-184) d ∧
      Sec1.AffineAt t (stackPtr initial-152) (Points.mul d Operations.domain.G) := by
  obtain ⟨s,entry⟩ := entry_with_slices hb hm call
  obtain ⟨t,result,scalar,point,_⟩ := sampler s (returnBoundary initial) input d entry.pre draw
  refine ⟨t,after_sampler call entry result,result.rip.trans entry.samplerReturn,
    (result.calleeSaved .r15 (by simp)).trans entry.buffer,entry.destination ▸ scalar,?_⟩
  rw [entry.destination] at point
  have address : stackPtr initial-184+32 = stackPtr initial-152 := by
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  rwa [address] at point

end P256.Proofs.Generate.Wrapper
