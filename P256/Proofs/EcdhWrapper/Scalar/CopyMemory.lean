import P256.Proofs.EcdhWrapper.Scalar.Call
import P256.Proofs.Program.ScalarFrame.Copy32
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.StackBuffer

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program.ScalarFrame

theorem stack_copy_pre [Bindings] {initial t : RamState} {secret peer : ByteArray}
    {slices : Array Input} {pc : BitVec 64} {src dst : Nat}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (rsp : stackPtr t = stackPtr initial-504) (rip : t.RIP = pc)
    (srcBound : src+32 ≤ 504) (dstBound : dst+32 ≤ 504)
    (apart : OffsetsApart (BitVec.ofNat 64 dst) 32 (BitVec.ofNat 64 src) 32) :
    Copy32.Pre pc (fun s => (Operand.reg 4 : Operand 64).read s+BitVec.ofNat 64 src)
      (fun s => (Operand.reg 4 : Operand 64).read s+BitVec.ofNat 64 dst) t := by
  have stack : Stack.Valid initial 4104 := call.stackAvailable.1
  have avoids := call_stack_avoids call
  change (Stack.region initial 4104).Avoids _ at avoids
  have read (off : Nat) (bound : off+8 ≤ 504) :
      MemReadable t (stackPtr t+BitVec.ofNat 64 off) 8 := by
    rw [scalar_stack_address (frameOffset := 504) rsp (by decide) (by omega)]
    exact readable_of_grow (stack_sub_readable stack
      (offset := 504-off) (len := 8) (by omega) (by omega)) grow
  have write (off : Nat) (bound : off+8 ≤ 504) :
      Common.Instructions.CrossPageStore.Writable t (stackPtr t+BitVec.ofNat 64 off) 8 := by
    rw [scalar_stack_address (frameOffset := 504) rsp (by decide) (by omega)]
    exact stack_buffer_writable stack avoids grow
      (offset := 504-off) (len := 8) (by omega) (by omega) (by decide)
  have code (off : Nat) (bound : off+8 ≤ 504) (k n : Nat) (kn : k+n ≤ 118431) :
      RangeApart (stackPtr t+BitVec.ofNat 64 off) 8
        (Extracted.textAddress+BitVec.ofNat 64 k) n := by
    rw [scalar_stack_address (frameOffset := 504) rsp (by decide) (by omega)]
    exact stack_buffer_code_apart stack avoids
      (offset := 504-off) (len := 8) (by omega) (by omega) kn
  refine ⟨rip,?_,?_,?_,?_⟩
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc] using read (src+_) (by omega)
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc] using write (dst+_) (by omega)
  · intro i hi j hj eq
    exact apart.ne (stackPtr t) hi hj (by decide) eq
  · intro i hi k n bound
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simpa only [stackPtr,Operand.read_reg64,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc] using code (dst+_) (by omega) k n bound

end P256.Proofs.EcdhWrapper.Scalar
