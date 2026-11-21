import P256.Proofs.EcdhWrapper.Scalar.PayloadMemory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program.ScalarFrame SecretKeyFromBytes.Scalar

theorem payload_correct [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input} {x : Nat}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬InProgram (returnBoundary initial).rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (frame : MemoryWriteFrame initial s (wrapperRegions ecdhDiffieHellman initial))
    (rip : s.RIP = 0x106923) (rsp : stackPtr s = stackPtr initial-504)
    (al : (s.regValue .rax).setWidth 8 = 1) (bpl : (s.regValue .rbp).setWidth 8 = 1)
    (scalar : Nat256At s (stackPtr initial-264) x) :
    ∃ t, (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ ReadyToStep t ∧
      ProgramLoaded t ∧ t.RIP = 0x1069b6 ∧ stackPtr t = stackPtr initial-504 ∧
      Nat256At t (stackPtr initial-160) x ∧
      MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial) ∧
      AgreesExcept (payloadClobbers initial) s t := by
  obtain ⟨na,a,ra,readyA,ea,valueA⟩ := first_copy call outside ready loaded grow rip rsp scalar
  have ga := first_copy_agrees rsp ea
  have frameA := memoryWriteFrame_trans frame (ga.memoryWriteFrame (payload_writes call.stackAvailable.1))
  have spA : stackPtr a = stackPtr initial-504 :=
    (ea.agrees.read (n := 64) (r := 4) (by simp [FirstCopy.effect,Effect.components])).trans rsp
  have alA : (a.regValue .rax).setWidth 8 = 1 :=
    (congrArg (BitVec.setWidth 8)
      (ea.agrees.read (n := 64) (r := 0) (by simp [FirstCopy.effect,Effect.components]))).trans al
  have bplA : (a.regValue .rbp).setWidth 8 = 1 :=
    (congrArg (BitVec.setWidth 8)
      (ea.agrees.read (n := 64) (r := 5) (by simp [FirstCopy.effect,Effect.components]))).trans bpl
  obtain ⟨b,rb,readyB,ripB,spB,gb⟩ := validity call outside readyA
    (wrapper_frame_loaded call call.programLoaded frameA) (fun z hz => ga.grow z (grow z hz))
    ea.rip spA alA bplA
  have totalB : AgreesExcept (payloadClobbers initial) s b :=
    (ga.trans gb).mono (by simp [payloadClobbers,Nonzero.clobbers])
  have frameB := memoryWriteFrame_trans frame
    (totalB.memoryWriteFrame (payload_writes call.stackAvailable.1))
  have rspB := spB.trans spA
  have valueB := validity_scalar call.stackAvailable.1 gb valueA
  obtain ⟨nt,t,rt,readyT,et,valueT⟩ := second_copy call outside readyB
    (wrapper_frame_loaded call call.programLoaded frameB) (fun z hz => totalB.grow z (grow z hz))
    ripB rspB valueB
  have gt := second_copy_agrees rspB et
  have total : AgreesExcept (payloadClobbers initial) s t := (totalB.trans gt).mono (by simp)
  have frameT := memoryWriteFrame_trans frame (total.memoryWriteFrame (payload_writes call.stackAvailable.1))
  refine ⟨t,⟨na+10+nt,(ra.trans rb).trans rt⟩,readyT,
    wrapper_frame_loaded call call.programLoaded frameT,et.rip,?_,valueT,frameT,total⟩
  exact ((Copy32.frame et).read (n := 64) (r := 4) (by simp [Copy32.components])).trans rspB

end P256.Proofs.EcdhWrapper.Scalar
