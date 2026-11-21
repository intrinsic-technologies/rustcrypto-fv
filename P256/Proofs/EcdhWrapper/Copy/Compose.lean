import P256.Proofs.EcdhWrapper.Copy
import P256.Proofs.EcdhWrapper.Copy.SetupPre
import P256.Proofs.EcdhWrapper.Copy.Buffer

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.EcdhWrapper.Copy (CopyResult)

theorem copy_entry_correct [bindings : Bindings] {initial : RamState} {secret peer : ByteArray}
    {slices : Array Input} (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    ∃ s t u, GuardedEntry initial s secret ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      (Copy.setupEffect s).Holds s t ∧
      CopyResult (returnBoundary initial) secret t u 0x10687d := by
  obtain ⟨s, hs⟩ := guards_correct hb hm call
  have outside := outer_boundary call hm hb
  obtain ⟨n,t,run,ready,_,effect⟩ := Copy.setup_correct (returnBoundary initial) outside s hs.ready
    (programText_slice (programLoaded_codeIn hs.loaded) 0x6830 Copy.setupBytes
      (by decide +kernel) (by decide +kernel)) (Copy.setup_pre call hs)
  have agrees : AgreesExcept [.reg 13,.mem (stackPtr s+32) 8,.mem (stackPtr s+40) 8,.rip] s t := by
    simpa [Copy.setupEffect, Effect.components, Write.component, Operand.component] using effect.agrees
  have frame : MemoryWriteFrame s t (wrapperRegions ecdhDiffieHellman initial) := by
    apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨callStack ecdhDiffieHellman initial, by simp [wrapperRegions], ?_⟩
    · have addr := Copy.setup_address hs.rsp (off := 32) (by simp)
      exact stack_component_within call.stackAvailable.1 (offset := 472)
        (by decide) (by decide)
        ((congrArg (fun addr => (Component.mem addr 8).Covers a) addr).mp ha)
    · have addr := Copy.setup_address hs.rsp (off := 40) (by simp)
      exact stack_component_within call.stackAvailable.1 (offset := 464)
        (by decide) (by decide)
        ((congrArg (fun addr => (Component.mem addr 8).Covers a) addr).mp ha)
  have fullFrame := memoryWriteFrame_trans hs.frame frame
  have loaded := wrapper_frame_loaded call call.programLoaded fullFrame
  have rsp : stackPtr t = stackPtr initial - 504 :=
    (agrees.read (n := 64) (r := 4) (by simp)).trans hs.rsp
  have source : t.regValue .rax = memLoad initial.external (initial.regValue .rdi) 64 :=
    (agrees.read (n := 64) (r := 0) (by simp)).trans hs.sourceAddress
  obtain ⟨address,pointer,_,bound,bytes,_⟩ := preserved_first_input call fullFrame
  have sourceAddress : t.regValue .rax = address := source.trans pointer
  have size : secret.size = 32 := ((arguments_iff secret peer).mp call.argumentsValid).1
  have pre := Copy.buffer_pre call (hs.agrees.trans agrees).grow effect.rip rsp source
    (by
      change (MemoryRegion.mk (t.regValue .rax).toNat 32).Bounded
      rw [sourceAddress, ← size]
      exact bound)
    (by
      change (MemoryRegion.mk (t.regValue .rax).toNat 32).HasBytes t.external secret
      rw [sourceAddress, ← size]
      exact bytes)
  obtain ⟨u,copied⟩ := copy_correct ready loaded outside pre
  exact ⟨s,t,u,hs,⟨n,run⟩,effect,copied⟩

end P256.Proofs.EcdhWrapper
