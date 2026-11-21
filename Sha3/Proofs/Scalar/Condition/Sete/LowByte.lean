import X86Proofs.Program.ReadWrite.WriteResult

namespace X86Proofs

open X86 X86.Helpers

theorem Operand.read_writeResult_self8 {σ : Type} [Machine.PhysicalMemory σ]
    (s : X86.State σ) (r : BitVec 5) (value : BitVec 8) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read (writeResult s (.reg r) value nextIP) =
      mergeGPR 8 value ((Operand.reg r : Operand 64).read s) := by
  simp [writeResult, Operand.write, gprIndex]

theorem Operand.read_writeOutputs_self8 {σ : Type} [Machine.PhysicalMemory σ]
    (s : X86.State σ) (r : BitVec 5) (out : BitVec 8 × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read
        (writeOutputs s (.reg r) out oracleUsed nextIP) =
      mergeGPR 8 out.1 ((Operand.reg r : Operand 64).read s) := by
  simp [writeOutputs, Operand.write, gprIndex, setFlags]

end X86Proofs
