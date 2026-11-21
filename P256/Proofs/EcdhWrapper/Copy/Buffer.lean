import P256.Proofs.Program.StackBuffer
import P256.Proofs.Program.WrapperFirstInput
import P256.Proofs.EcdhWrapper.Copy.Interface
import P256.Spec.Program.Functions

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.EcdhWrapper.Copy

theorem buffer_pre [Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP = 0x10683d) (rsp : stackPtr s = stackPtr initial - 504)
    (source : s.regValue .rax = memLoad initial.external (initial.regValue .rdi) 64)
    (bounded : (registerRegion s .rax 32).Bounded)
    (bytes : (registerRegion s .rax 32).HasBytes s.external secret) :
    CopyPre secret s .rax 0x10683d := by
  have address : stackPtr s + 112 = stackPtr initial - 392 := by
    rw [rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have bufferBounded := stack_buffer_bounded call.stackAvailable.1
    (offset := 392) (len := 32) (by decide) (by decide)
  refine ⟨rip, bounded, bytes, ?_, ?_, ?_⟩
  · rw [address]
    exact stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) grow
      (by decide) (by decide) (by decide)
  · rw [address]
    have sourceRegion : registerRegion s .rax 32 ∈ readRegions initial slices := by
      change MemoryRegion.mk (s.regValue .rax).toNat 32 ∈ _
      have size : secret.size = 32 := bytes.1
      rw [source, ← size]
      exact first_input_region call
    have disjoint := wrapper_read_disjoint call sourceRegion
      (callStack ecdhDiffieHellman initial) (by simp [wrapperRegions])
    intro i hi j hj eq
    apply disjoint (s.regValue .rax + BitVec.ofNat 64 j).toNat
      (memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hj)
    rw [← eq]
    exact stack_contains_callStack
      (stack_buffer_contains call.stackAvailable.1 (by decide) (by decide)
        (memoryRegion_contains_add bufferBounded (Nat.le_refl _) (Nat.le_refl _) hi))
  · rw [address]
    exact stack_buffer_avoids call.stackAvailable.1 (call_stack_avoids call)
      (by decide) (by decide)

end P256.Proofs.EcdhWrapper.Copy
