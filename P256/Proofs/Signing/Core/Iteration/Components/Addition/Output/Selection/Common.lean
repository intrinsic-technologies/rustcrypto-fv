import P256.Proofs.Signing.Core.Iteration.Components.Addition.Memory
import P256.Proofs.Field.Add.Correction
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Arithmetic
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Selection

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem lowByte_read_dword (s : RamState) (r : BitVec 5) :
    ((Operand.reg r : Operand 32).read s).setWidth 8 = (Operand.reg r : Operand 8).read s := by
  simp only [Operand.read, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]

@[local x86_local] theorem storeByteRegister_local (p : BitVec 64) (len : Nat)
    (am : AddrMode) (src : BitVec 5) :
    Effect.Local (storeEffect p len (storeAddrAt p am len)
      (fun s => (Operand.reg src : Operand 8).read s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, storeAddrAt, AddrMode.addr_obs h, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

structure Pre (entry : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = entry
  writable : MemWritable s (stackPtr s) 1
  apart : ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s) 1
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Selection
