import Sha2.Proofs.Common.SHA256.Absorb.Proof.Stage
import Sha2.Proofs.Wrapper.Absorb.Arithmetic

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem count_values {l : Layout} {sp : BitVec 64} {s t : RamState} {len : Nat}
    (length : Blocks.readReg s l.registers.remaining = BitVec.ofNat 64 len) (bound : len < 2^64)
    (effect : (Stage.count.effect l sp s).Holds s t) :
    t.regValue .rdx = BitVec.ofNat 64 (len / 64) ∧
      (StatusFlags.ofRFLAGS t.RFLAGS).ZF = decide (len / 64 = 0) := by
  have shifted : Blocks.readReg s l.registers.remaining >>> 6 = BitVec.ofNat 64 (len / 64) := by
    rw [length, Wrapper.Absorb.block_count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  refine ⟨effect.writes.trans shifted, ?_⟩
  have flags := effect.flags
  change (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6
    (Blocks.readReg s l.registers.remaining)).Allows (StatusFlags.ofRFLAGS t.RFLAGS) at flags
  have zero := flags.2.2.2.1
  change (StatusFlags.ofRFLAGS t.RFLAGS).ZF = _ at zero
  rw [zero, shifted]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.mod_eq_of_lt (by omega : len / 64 < 2^64)] at h'
    exact h'
  · intro h
    rw [h]
    rfl

theorem split_values {l : Layout} {sp : BitVec 64} {s t : RamState}
    {source : BitVec 64} {len : Nat}
    (length : Blocks.readReg s l.registers.remaining = BitVec.ofNat 64 len)
    (address : Blocks.readReg s l.alignedSource = source) (bound : len < 2^61)
    (effect : (Stage.splitTail.effect l sp s).Holds s t) :
    Blocks.readReg t l.registers.remaining = BitVec.ofNat 64 (len % 64) ∧
      Blocks.readReg t l.alignedSource = source + BitVec.ofNat 64 (64 * (len / 64)) := by
  have asNat : (Blocks.readReg s l.registers.remaining).toNat = len := by
    rw [length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨effect.writes.2.2.1.trans ?_, effect.writes.2.2.2.trans ?_⟩
  · rw [Wrapper.Absorb.tail_length, asNat]
  · rw [address, BitVec.and_comm, Wrapper.Absorb.full_length _ (by rw [asNat]; exact bound), asNat]

end Sha2.Proofs.Common.SHA256.Absorb
