import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Branch
import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.Success

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper.Epilogue

open P256.Proofs.SignatureFromSlice.Wrapper.Epilogue (State)

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem accept [bindings : Bindings] {initial t : RamState} {value : Nat × Nat}
    (pre : Success.Pre initial) (state : State initial t)
    (low : (returnBoundary initial).rip.toNat < 2^32) (rip : t.RIP = 0x102280)
    (tag : loadBytes t.external (stackPtr initial - 88) 8 = .ok (0 : BitVec 64))
    (first : Nat256At t (stackPtr initial - 80) value.1)
    (second : Nat256At t (stackPtr initial - 48) value.2) :
    ∃ fuel u, Returns (returnBoundary initial) fuel t u ∧
      SupportedIntegerMachineState bindings.processor u ∧
      MachineRamUnitStrideDecodable bindings u ∧
      CalleeSavedRegistersUnchanged initial u ∧ DirectionFlagUnset u ∧ SuccessfulStatus u ∧
      MemoryWriteFrame t u #v[registerRegion initial .rcx 72] ∧
      readOutput signatureFromSlice initial u = .ok (Ecdsa.encodeFixed value) := by
  obtain ⟨a,ha,sa,ipa,ma⟩ := tag_branch (valid := true) state pre.stack pre.outside rip tag
  have firstA : Nat256At a (stackPtr initial - 80) value.1 := by
    simpa only [Nat256At, ma] using first
  have secondA : Nat256At a (stackPtr initial - 48) value.2 := by
    simpa only [Nat256At, ma] using second
  obtain ⟨n,u,hu,machine,bindingsSupported,saved,direction,status,frame,output⟩ :=
    Success.accept pre sa low ipa firstA secondA
  refine ⟨_,u,ha.returns hu,machine,bindingsSupported,saved,direction,status,?_,output⟩
  intro x hx
  rw [frame x hx,ma]

theorem reject [bindings : Bindings] {initial t : RamState}
    (state : State initial t) (stack : Stack.Valid initial 656)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : (returnBoundary initial).rip.toNat < 2^32)
    (rip : t.RIP = 0x102280)
    (tag : loadBytes t.external (stackPtr initial - 88) 8 = .ok (1 : BitVec 64))
    (null : memLoad t.external (stackPtr initial - 80) 64 = 0) :
    ∃ fuel u, Returns (returnBoundary initial) fuel t u ∧
      SupportedIntegerMachineState bindings.processor u ∧
      MachineRamUnitStrideDecodable bindings u ∧
      CalleeSavedRegistersUnchanged initial u ∧ DirectionFlagUnset u ∧
      FailureStatus u invalidSignatureBytesStatus ∧ u.external = t.external := by
  obtain ⟨a,ha,sa,ipa,ma⟩ := tag_branch (valid := false) state stack outside rip tag
  have nullA : loadBytes a.external (stackPtr initial - 80) 8 = .ok (0 : BitVec 64) := by
    have bytes := Bytes.of_memLoad (n := 64)
      (readable_of_grow (stack_sub_readable stack (offset := 80) (len := 8)
        (by decide) (by decide)) state.allocated).mem
    change Bytes t.external (stackPtr initial - 80) 8
      (storedByte (memLoad t.external (stackPtr initial - 80) 64)) at bytes
    rw [null] at bytes
    rw [ma]
    exact bytes.loadBytes64
  obtain ⟨b,hb,sb,ipb,axb,mb⟩ := reject_branch sa stack outside ipa nullA
  obtain ⟨u,hu,machine,bindingsSupported,saved,direction,memory,ax⟩ :=
    Return.restore (locals := 72) sb stack (by decide) outside low 0x22a9
      ⟨by decide, by decide, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩ ipb
  refine ⟨_,u,(ha.trans hb).returns hu,machine,bindingsSupported,saved,direction,
    ?_,(memory.trans mb).trans ma⟩
  change (u.regValue .rax).setWidth 32 = 1
  rw [ax,axb]
  rfl

end P256.Proofs.SignatureFromSlice.Wrapper.Epilogue
