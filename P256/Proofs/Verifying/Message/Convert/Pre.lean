import P256.Proofs.Verifying.Message.Convert.Memory
import P256.Proofs.Ecdh.Initial.Prefix.Constants

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem key_copy_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {ip : BitVec 64} {source destination : RamState → BitVec 64}
    (pre : Pre initial boundary message) (state : Message.Frame initial s)
    {offset sourceOffset : Nat} (bound : offset + 32 ≤ 1176) (sourceBound : sourceOffset + 32 ≤ 72)
    (rip : s.RIP = ip) (dst : destination s = stackPtr s + BitVec.ofNat 64 offset)
    (src : source s = initial.regValue .rsi + BitVec.ofNat 64 sourceOffset) :
    Copy32.Pre ip source destination s := by
  apply copy_pre pre state bound rip dst
  · intro i hi
    rw [src]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (key_readable pre state (offset := sourceOffset + 0) (len := 8) (by omega))
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (key_readable pre state (offset := sourceOffset + 8) (len := 8) (by omega))
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (key_readable pre state (offset := sourceOffset + 16) (len := 8) (by omega))
    · simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        (key_readable pre state (offset := sourceOffset + 24) (len := 8) (by omega))
  · rw [dst, src]
    exact key_stack_apart pre state bound sourceBound

theorem one_copy_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {ip : BitVec 64} {source destination : RamState → BitVec 64}
    (pre : Pre initial boundary message) (state : Message.Frame initial s)
    {offset : Nat} (bound : offset + 32 ≤ 1176) (rip : s.RIP = ip)
    (dst : destination s = stackPtr s + BitVec.ofNat 64 offset)
    (src : source s = 0x202580) : Copy32.Pre ip source destination s := by
  apply copy_pre pre state bound rip dst
  · intro i hi
    rw [src]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact Ecdh.Initial.Prefix.one_readable state.loaded (k := 0) (by decide)
    · exact Ecdh.Initial.Prefix.one_readable state.loaded (k := 1) (by decide)
    · exact Ecdh.Initial.Prefix.one_readable state.loaded (k := 2) (by decide)
    · exact Ecdh.Initial.Prefix.one_readable state.loaded (k := 3) (by decide)
  · rw [dst, src]
    intro i hi j hj eq
    rw [scalar_stack_address (frameOffset := 1176) state.rsp (by decide) (by omega)] at eq
    apply pre.avoids (Stack.region initial 9992) (by simp) _
      (stack_contains pre.toCalleePre (offset := 1176-offset) (len := 32) (by omega) (by omega) ⟨i, hi, rfl⟩) (.inl ?_)
    rw [eq]
    exact Ecdh.Initial.Prefix.one_byte hj

end P256.Proofs.Verifying.Message.Convert
