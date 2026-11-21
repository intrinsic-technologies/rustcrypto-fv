import P256.Proofs.EcdhWrapper.Peer.Call
import P256.Proofs.EcdhWrapper.Scalar.Prefix.Memory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

theorem call_frame {initial s t : RamState} (stack : Stack.Valid initial 4104)
    (ag : AgreesExcept (callComponents initial) s t) :
    MemoryWriteFrame s t (wrapperRegions ecdhDiffieHellman initial) := by
  apply ag.memoryWriteFrame
  intro c hc a cover
  simp only [callComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact cover.elim
  exact ⟨callStack ecdhDiffieHellman initial,by simp [wrapperRegions],
    stack_component_within (routine := ecdhDiffieHellman) stack
      (offset := 512) (by decide) (by decide) cover⟩

theorem return_frame [Bindings] {initial s called t : RamState}
    (stack : Stack.Valid initial 4104)
    (frame : MemoryWriteFrame initial s (wrapperRegions ecdhDiffieHellman initial))
    (ag : AgreesExcept (callComponents initial) s called)
    (rsp : stackPtr called = stackPtr initial-512)
    (output : called.regValue .rdi = stackPtr initial-128)
    (result : CalleeResult called t (returnBoundary initial) 80 3360) :
    MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial) :=
  memoryWriteFrame_trans (memoryWriteFrame_trans frame (call_frame stack ag))
    (Scalar.prefix_work_frame stack
      (result.stack_frame stack rsp output (savedBytes := 48)
        (by decide) (by decide) (by decide) (by decide)))

theorem call_byte {initial s called : RamState} {offset len : Nat}
    (stack : Stack.Valid initial 4104)
    (ag : AgreesExcept (callComponents initial) s called)
    (below : offset ≤ 504) (extent : len ≤ offset+8) {i : Nat} (hi : i<len) :
    called.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      s.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  apply ag.byte
  intro c hc cover
  simp only [callComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact cover.elim
  obtain ⟨j,hj,eq⟩ := cover
  exact stack_sub_apart stack (a := 512) (b := offset)
    (by decide) (by omega) (by decide) extent (.inl (by omega)) j hj i hi eq.symm

theorem return_word [Bindings] {initial s called t : RamState} {offset : Nat}
    (stack : Stack.Valid initial 4104)
    (ag : AgreesExcept (callComponents initial) s called)
    (rsp : stackPtr called = stackPtr initial-512)
    (output : called.regValue .rdi = stackPtr initial-128)
    (result : CalleeResult called t (returnBoundary initial) 80 3360)
    (range : offset ≤ 48 ∨ offset=464 ∨ offset=472) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  apply memByte_congr
  exact (result.stack_byte stack rsp output (frameOffset := 504) (outputOffset := 128) (len := 8)
    (by decide) (by decide) (by rcases range with h | rfl | rfl <;> omega)
    (by omega) (by rcases range with h | rfl | rfl <;> omega) hi).trans
      (call_byte stack ag (by rcases range with h | rfl | rfl <;> omega) (by omega) hi)

theorem return_scalar [Bindings] {initial s called t : RamState} {x : Nat}
    (stack : Stack.Valid initial 4104)
    (ag : AgreesExcept (callComponents initial) s called)
    (rsp : stackPtr called = stackPtr initial-512)
    (output : called.regValue .rdi = stackPtr initial-128)
    (result : CalleeResult called t (returnBoundary initial) 80 3360)
    (scalar : Nat256At s (stackPtr initial-160) x) :
    Nat256At t (stackPtr initial-160) x := by
  refine ⟨scalar.1,fun i hi => ?_⟩
  exact (result.stack_byte stack rsp output (frameOffset := 504) (outputOffset := 128) (offset := 160) (len := 32)
    (by decide) (by decide) (by decide) (by decide) (.inr (by decide)) hi).trans
      ((call_byte stack ag (offset := 160) (len := 32) (by decide) (by decide) hi).trans
        (scalar.2 i hi))

end P256.Proofs.EcdhWrapper.Peer
