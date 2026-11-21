import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Execution
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Bytes
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Payload

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key message : ByteArray}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10df0d)
    (inner : HashStateAt s (stackPtr initial - 272) (Suffix.innerHash key message))
    (outer : HashStateAt s (stackPtr initial - 232) (Suffix.outerHash key))
    (count : loadBytes s.external (stackPtr initial - 200) 8 = .ok 1) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = 0x10e01b ∧
      t.regValue .rdi = stackPtr initial - 232 ∧
      t.regValue .rsi = stackPtr initial - 400 ∧ t.regValue .rdx = 1 ∧
      HashStateAt t (stackPtr initial - 232) (Suffix.outerHash key) ∧
      (MemoryRegion.mk (stackPtr initial - 400).toNat 64).HasBytes t.external
        (tailFirst (HMAC.xorPad (HMAC.keyBlock key) 0x5c ++
          Standards.NIST.SHA2.SHA256.hashBytes
            (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message))) := by
  obtain ⟨a, stateA, serialized⟩ := serialize pre state rip
  have frameA := serialized.agrees.memoryWriteFrame (serialize_writes pre state)
  have innerLocal : HashStateAt s (stackPtr s + 136) (Suffix.innerHash key message) := by
    simpa only [state.rsp,
      show stackPtr initial - 408 + 136 = stackPtr initial - 272 by bv_omega] using inner
  have digest := Serialize.payload (serialize_pre pre state rip) innerLocal serialized
  have source : (MemoryRegion.mk (stackPtr a + 72).toNat 32).HasBytes a.external
      (Standards.NIST.SHA2.SHA256.hashBytes
        (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message)) := by
    simpa only [Serialize.rsp_unchanged serialized, Suffix.innerHash,
      serializeHash_compressBlocks_bytePadding_eq_hashBytes] using digest
  have countA : loadBytes a.external (stackPtr a + 208) 8 = .ok 1 := by
    rw [stateA.rsp,
      show stackPtr initial - 408 + 208 = stackPtr initial - 200 by bv_omega]
    exact (agrees_loadBytes (agrees_above pre frameA 200 8 (by decide) (by decide))).trans count
  obtain ⟨u, t, stateT, marked, copied⟩ := pad pre stateA serialized.rip
  have frameT := (marked.agrees.trans copied.agrees).memoryWriteFrame
    (pad_writes pre stateA marked)
  have bytes := Pad.payload marked copied countA source
    ((readable pre stateA 72 64 (by decide)).of_holds marked)
    (((readable pre stateA 8 64 (by decide)).of_holds marked).of_holds copied)
  have rspU : stackPtr u = stackPtr a := marked.agrees.read (n := 64) (r := 4)
    (by simp [Pad.Mark.effect, Effect.components, Write.component, Operand.component])
  have destinationA : a.regValue .rdi = stackPtr s + 176 := by
    exact Write.allHold_iff.mp serialized.writes
      ⟨(.reg 7 : Operand 64), stackPtr s + 176⟩ (by simp [Serialize.effect])
  have destinationT : t.regValue .rdi = stackPtr initial - 232 := by
    have same := (marked.agrees.trans copied.agrees).read (n := 64) (r := 7)
      (by simp [Pad.Mark.effect, Pad.Copy.effect, Effect.components,
        Write.component, Operand.component])
    change t.regValue .rdi = a.regValue .rdi at same
    rw [same, destinationA, state.rsp]
    bv_omega
  have sourceT : t.regValue .rsi = stackPtr initial - 400 := by
    have same : t.regValue .rsi = stackPtr u + 8 :=
      Write.allHold_iff.mp copied.writes ⟨(.reg 6 : Operand 64), stackPtr u + 8⟩
        (by simp [Pad.Copy.effect,
          show rspOf u = stackPtr u from Operand.read_reg64 u 4])
    rw [same, rspU, stateA.rsp]
    bv_omega
  have countT : t.regValue .rdx = 1 :=
    Write.allHold_iff.mp copied.writes ⟨(.reg 2 : Operand 64), 1⟩
      (by simp [Pad.Copy.effect])
  refine ⟨t, stateT, copied.rip, destinationT, sourceT, countT,
    hash_of_frame pre frameT (hash_of_frame pre frameA outer), ?_⟩
  simpa only [show rspOf a = stackPtr a from Operand.read_reg64 a 4, stateA.rsp,
    show stackPtr initial - 408 + 8 = stackPtr initial - 400 by bv_omega,
    Pad.padded, ← tailFirst_outer key message] using bytes

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare
