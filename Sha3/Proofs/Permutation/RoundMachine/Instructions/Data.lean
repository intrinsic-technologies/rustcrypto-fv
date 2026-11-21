import Sha3.Proofs.Permutation.RoundMachine.Instructions.Bytes
import Sha3.Proofs.Permutation.RoundAlgebra

namespace Sha3.Proofs.Permutation.RoundMachine

open RoundAlgebra

def dataPc (copy : Copy) (i : Fin 258) : Nat :=
  ((roundInstructionBytes copy)[i.val]'(by rw [roundInstructionBytes_length]; omega)).1.toNat

set_option maxRecDepth 4096 in
def dataOp (i : Fin 257) : Instruction :=
  (program[i.val]'(by change i.val < 257; exact i.isLt)).2

def dataBytes (copy : Copy) (i : Fin 257) : List UInt8 :=
  ((roundInstructionBytes copy)[i.val]'(by rw [roundInstructionBytes_length]; omega)).2

end Sha3.Proofs.Permutation.RoundMachine
