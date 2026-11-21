import P256.Proofs.EcdhWrapper.Copy.Interface
import P256.Proofs.Program.Input
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Curve.LinearCombination.NafReverse.Load
import P256.Proofs.Common.Curve.LinearCombination.NafReverse.Store
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

variable {input : ByteArray} {s : RamState} {sourceRegister : Syntax.Reg} {entry : BitVec 64}

theorem CopyPre.readable (h : CopyPre input s sourceRegister entry) (off len : Nat) (hl : off + len ≤ 32) :
    MemReadable s (s.regValue sourceRegister + BitVec.ofNat 64 off) len := by
  have hr := hasBytes_memReadable h.sourceBounded h.sourceBytes
  refine ⟨?_, ?_⟩
  · have := hr.low
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2^64),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · intro i hi
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hr.mem (off+i) (by omega)

theorem CopyPre.contains (h : CopyPre input s sourceRegister entry) {i : Nat} (hi : i < 32) :
    (MemoryRegion.mk (stackPtr s + 112).toNat 32).Contains
      ((stackPtr s + 112) + BitVec.ofNat 64 i).toNat := by
  have hl := h.writable.low
  have ha : ((stackPtr s + 112) + BitVec.ofNat 64 i).toNat =
      (stackPtr s + 112).toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by omega)]
  rw [ha]
  constructor <;> dsimp <;> omega

theorem CopyPre.codeApart (h : CopyPre input s sourceRegister entry) (off len : Nat) (hl : off + len ≤ 32)
    (offset codeLen : Nat) (hc : offset + codeLen ≤ 118431) :
    RangeApart ((stackPtr s + 112) + BitVec.ofNat 64 off) len
      (Extracted.textAddress + BitVec.ofNat 64 offset) codeLen := by
  intro i hi j hj he
  have hn := h.avoids _ (h.contains (i := off+i) (by omega))
  apply hn
  apply Or.inl
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, he]
  have hp := inProgram_of_textOffset (offset+j) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hp

theorem CopyPre.byteWritable (h : CopyPre input s sourceRegister entry) (off : Nat) (hl : off + 1 ≤ 32) :
    MemWritable s ((stackPtr s + 112) + BitVec.ofNat 64 off) 1 := by
  have hw := h.writable.add off hl
  exact ⟨hw.low, hw.mem, hw.tables⟩

@[x86_local] theorem copyByteStore_local (p : BitVec 64) (len : Nat)
    (am : AddrMode) (r : BitVec 5) :
    Effect.Local (storeEffect p len (storeAddrAt p am len)
      (fun s => (Operand.reg r : Operand 8).read s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, storeAddrAt, AddrMode.addr_obs h, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

@[x86_compose] theorem copy_write_reg_external (s : RamState) {n : Nat}
    (r : BitVec 5) (v : BitVec n) :
    ((Operand.reg r : Operand n).write s v).external = s.external := rfl

@[x86_compose] theorem copy_write_mem_external (s : RamState) {n : Nat}
    (a : BitVec 64) (v : BitVec n) :
    ((Operand.mem a : Operand n).write s v).external = memStore s.external a v := rfl

end P256.Proofs.EcdhWrapper.Copy
