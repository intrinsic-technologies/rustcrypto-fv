import P256.Proofs.Verifying.Wrapper.MessageInput
import P256.Proofs.Verifying.Message.Interface
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.StackBuffer

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def messageLayout : StackCallLayout 10280 72 24 9992 :=
  ⟨288,112,208,by decide,by decide,by decide,by decide,by decide,by decide,Or.inr (by decide)⟩

theorem message_pre [Bindings] {initial t : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (base : CalleePre t (returnBoundary initial) 0x10d570 72 24 9992)
    (frame : MemoryWriteFrame initial t (wrapperRegions verifyingKeyVerify initial))
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (sp : stackPtr t = stackPtr initial-288)
    (descriptor : t.regValue .rdx = stackPtr initial-128)
    (scalars : t.regValue .r8 = stackPtr initial-280) (count : t.regValue .rcx = 1)
    (pointer : memLoad t.external (stackPtr initial-128) 64 =
      memLoad initial.external (initial.regValue .rdi+16#64) 64)
    (length : memLoad t.external (stackPtr initial-120) 64 = BitVec.ofNat 64 message.size) :
    Message.Pre t (returnBoundary initial) message := by
  have stack : Stack.Valid initial 10280 := call.stackAvailable.1
  have bounds := stack_bounds stack
  have spNat : (stackPtr t).toNat = (stackPtr initial).toNat-288 := by
    rw [sp]
    exact stack_sub_toNat stack (by decide)
  have stackSub : ∀ a, (Stack.region t 9992).Contains a →
      (Stack.region initial 10280).Contains a := by
    intro a ha
    change (stackPtr t).toNat-9992 ≤ a ∧ a <
      (Stack.region t 9992).start+(Stack.region t 9992).size at ha
    rw [stack_region_end,spNat] at ha
    change (stackPtr initial).toNat-10280 ≤ a ∧ a <
      (Stack.region initial 10280).start+(Stack.region initial 10280).size
    rw [stack_region_end]
    constructor <;> omega
  have localAllocated (offset len : Nat) (within : offset ≤ 10280) (extent : len ≤ offset+8) :
      (MemoryRegion.mk (stackPtr initial-BitVec.ofNat 64 offset).toNat len).Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (grow a
      (Option.isSome_iff_exists.mpr (stack.2.1 a (stack_buffer_contains stack within extent ha))))
  have localApart (offset len : Nat) (above : offset+8 ≤ 288) :
      (MemoryRegion.mk (stackPtr initial-BitVec.ofNat 64 offset).toNat len).Disjoint
        (Stack.region t 9992) := by
    intro a ha hb
    change (stackPtr initial-BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (stackPtr initial-BitVec.ofNat 64 offset).toNat+len at ha
    rw [stack_sub_toNat stack (by omega)] at ha
    change (stackPtr t).toNat-9992 ≤ a ∧ a <
      (Stack.region t 9992).start+(Stack.region t 9992).size at hb
    rw [stack_region_end,spNat] at hb
    omega
  obtain ⟨address,original,_,bounded,bytes,_⟩ := preserved_message_input call frame
  have region : Message.messageRegion t message = MemoryRegion.mk address.toNat message.size := by
    simp only [Message.messageRegion,descriptor,pointer,original]
  refine {
    toCalleePre := base
    count := count
    descriptorBounded := ?_
    descriptorAllocated := ?_
    descriptorStack := ?_
    messageLength := ?_
    messageBounded := region ▸ bounded
    messageAllocated := region ▸ hasBytes_allocated bytes
    messageStack := ?_
    messageBytes := region ▸ bytes
    signatureBounded := ?_
    signatureAllocated := ?_
    signatureStack := ?_
  }
  · simpa only [registerRegion,descriptor,show (128 : BitVec 64) = 128#64 from rfl] using stack_buffer_bounded stack
      (offset := 128) (len := 16) (by decide) (by decide)
  · simpa only [registerRegion,descriptor,show (128 : BitVec 64) = 128#64 from rfl] using localAllocated 128 16 (by decide) (by decide)
  · simpa only [registerRegion,descriptor,show (128 : BitVec 64) = 128#64 from rfl] using localApart 128 16 (by decide)
  · rw [descriptor]
    have addressEq : stackPtr initial-128+8 = stackPtr initial-120 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    simpa only [addressEq] using length
  · rw [region,← original]
    intro a ha hb
    exact wrapper_read_disjoint call (message_input_region call)
      (callStack verifyingKeyVerify initial) (by simp [wrapperRegions]) a ha
      (stack_contains_callStack (stackSub a hb))
  · simpa only [registerRegion,scalars,show (280 : BitVec 64) = 280#64 from rfl] using stack_buffer_bounded stack
      (offset := 280) (len := 64) (by decide) (by decide)
  · simpa only [registerRegion,scalars,show (280 : BitVec 64) = 280#64 from rfl] using localAllocated 280 64 (by decide) (by decide)
  · simpa only [registerRegion,scalars,show (280 : BitVec 64) = 280#64 from rfl] using localApart 280 64 (by decide)

end P256.Proofs.Verifying.Wrapper
