import Sha3.Proofs.Image
import Sha3.Proofs.Permutation.Layout
import X86Proofs.Program.ReadWrite.Bytes

namespace Sha3.Proofs.Permutation

open X86 X86.Machine X86Proofs Sha3.Spec.Program Keccak

def constantAddress (copy : Copy) (round : Fin 24) : BitVec 64 :=
  constantBase copy + BitVec.ofNat 64 (8 * round.val)

theorem constantAddress_low (copy : Copy) (round : Fin 24) : (constantAddress copy round).toNat + 8 ≤ 2 ^ 32 := by
  have h : ∀ (c : Copy) (r : Fin 24), (constantAddress c r).toNat + 8 ≤ 2 ^ 32 := by intro c; cases c <;> decide +kernel
  exact h copy round

theorem constantByte (copy : Copy) (round : Fin 24) (byte : Fin 8) :
    Extracted.programSections.fetchByte (constantAddress copy round + BitVec.ofNat 64 byte.val) =
      some (storedByte roundConstants[round.val] byte.val) := by
  have h : ∀ (c : Copy) (r : Fin 24) (b : Fin 8),
      Extracted.programSections.fetchByte (constantAddress c r + BitVec.ofNat 64 b.val) =
        some (storedByte roundConstants[r.val] b.val) := by intro c; cases c <;> decide +kernel
  exact h copy round byte

theorem constant_bytes {s : RamState} (h : ProgramLoaded s) (copy : Copy) (round : Fin 24) :
    Bytes s.external (constantAddress copy round) 8 (storedByte (roundConstant (round.val : Int))) := by
  rw [roundConstant_eq]
  intro byte hbyte
  exact programLoaded_fetchByte h (constantByte copy round ⟨byte, hbyte⟩)

theorem constant_readable {s : RamState} (h : ProgramLoaded s) (copy : Copy) (round : Fin 24) :
    MemReadable s (constantAddress copy round) 8 :=
  (constant_bytes h copy round).readable (constantAddress_low copy round)

theorem constant_memLoad {s : RamState} (h : ProgramLoaded s) (copy : Copy) (round : Fin 24) :
    memLoad s.external (constantAddress copy round) 64 = roundConstant (round.val : Int) :=
  (constant_bytes h copy round).memLoad (by decide) (by decide)

theorem constant_operand_read {s : RamState} (h : ProgramLoaded s) (copy : Copy) (round : Fin 24) :
    (Operand.mem (constantAddress copy round) : Operand 64).read s =
      roundConstant (round.val : Int) :=
  constant_memLoad h copy round

theorem constant_operand_read_of_code {s : RamState}
    (h : CodeIn Extracted.programImage s) (copy : Copy) (round : Fin 24) :
    (Operand.mem (constantAddress copy round) : Operand 64).read s =
      roundConstant (round.val : Int) :=
  constant_operand_read (fun address byte hbyte ↦ (h (address, byte) hbyte).2) copy round

end Sha3.Proofs.Permutation
