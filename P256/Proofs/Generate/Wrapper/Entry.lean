import P256.Proofs.Generate.Wrapper.Prepare
import P256.Proofs.Generate.Wrapper.SamplerPre

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem entry_with_slices [bindings : Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices) :
    ∃ t, SamplerEntry initial t input := by
  obtain ⟨u,su,rip,source,destination,buffer,pointer,length⟩ := prepare_descriptor hb hm call
  have outside := outer_boundary call hm hb
  obtain ⟨t,st,ce,_⟩ := su.call_rel32 call outside 0x6da8 0xffff9e23 rip
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0xbd0 (by decide))
  have push : pushAddr u = stackPtr initial-272 := by
    rw [pushAddr,su.rsp,BitVec.sub_sub]
    rfl
  have ca : AgreesExcept [.reg 4,.mem (stackPtr initial-272) 8,.rip] u t := by
    simpa only [pushEffect_components,push] using ce.agrees
  have src : t.regValue .rsi = stackPtr initial-256 :=
    (ca.read (n := 64) (r := 6) (by simp)).trans source
  have dst : t.regValue .rdi = stackPtr initial-184 :=
    (ca.read (n := 64) (r := 7) (by simp)).trans destination
  have ret : (returnBoundary t).rip = 0x106dad := (callEffect_stack ce).1
  have words (off : Nat) (ho : off = 256 ∨ off = 248) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) 64 =
        memLoad u.external (stackPtr initial-BitVec.ofNat 64 off) 64 := by
    apply memLoad_agrees_apart ca
    intro a len member
    have eq : a = stackPtr initial-272 ∧ len = 8 := by simpa using member
    obtain ⟨rfl,rfl⟩ := eq
    exact stack_sub_apart call.stackAvailable.1 (a := 272) (b := off)
      (by decide) (by change off ≤ 4024; omega) (by decide) (by omega) (.inl (by omega))
  have pre := sampler_pre call st outside ce.rip src dst
    (by rw [src]; exact (words 256 (.inl rfl)).trans pointer)
    (by
      rw [src,show stackPtr initial-256+8 = stackPtr initial-248 by
        simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl]
      exact (words 248 (.inr rfl)).trans length) ret
  exact ⟨t,st,pre,dst,src,ret,(ca.read (n := 64) (r := 15) (by simp)).trans buffer⟩

theorem entry_correct [bindings : Bindings] {initial : RamState} {input : ByteArray}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCall signingKeyGenerateFromRng initial [input]) :
    ∃ t, SamplerEntry initial t input := by
  obtain ⟨slices,call⟩ := call
  exact entry_with_slices hb hm call

end P256.Proofs.Generate.Wrapper
