import P256.Proofs.EcdhWrapper.Computed
import P256.Proofs.EcdhWrapper.Finish.Copy
import P256.Proofs.EcdhWrapper.Finish.Return

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem ecdh_correct_of_raw [bindings : Bindings]
    (raw : ∀ (s : RamState) (boundary : ReturnBoundary) (bytes : ByteArray),
      Sec1.AffineDecodePre s boundary bytes → ∃ t, CalleeResult s t boundary 80 3360 ∧
        Sec1.AffineResultAt t (s.regValue .rdi) (Points.decodePoint bytes))
    {initial : RamState} {secret peer : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall ecdhDiffieHellman initial [secret,peer]) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion ecdhDiffieHellman initial [secret,peer],allocatorStateRegion,
          randomSourceRegion,callStack ecdhDiffieHellman initial] ∧
      readOutput ecdhDiffieHellman initial final =
        .ok (P256.Spec.Ecdh.diffieHellman #[secret,peer]) := by
  obtain ⟨slices,call⟩ := hCall
  obtain ⟨s,⟨n,run⟩,hb,hm,df,loaded,grow,rip,rsp,data,frame,saved,ret,out,cap,_,_⟩ :=
    computed_of_raw raw hBindings hMachine call
  obtain ⟨t,copy,hbt,hmt,dft,lt,gt,ipt,spt,cxt,r8t,bytes,_,_,_,_,ft,words,_⟩ :=
    Finish.Copy.correct hBindings hMachine call hb hm df loaded grow frame rip rsp out cap data
  have savedT : ∀ reg ∈ savedRegisters,
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 reg.2) 64 =
        initial.regValue reg.1 := by
    intro reg member
    have bound : reg.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (words reg.2 64 (by omega) (by omega)).trans (saved reg member)
  have retT : memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip := by
    have keep := words 0 64 (by decide) (by decide)
    simp only [BitVec.sub_zero] at keep
    exact keep.trans ret
  obtain ⟨fuel,final,unique,machine,supported,calleeSaved,direction,_,framed,result⟩ :=
    Finish.Return.correct hBindings hMachine call hbt hmt dft lt gt ipt spt cxt r8t
      savedT retT ft bytes ⟨n+12,run.trans copy⟩
  exact ⟨fuel,final,unique,machine,supported,calleeSaved,direction,framed,result⟩

end P256.Proofs.EcdhWrapper
