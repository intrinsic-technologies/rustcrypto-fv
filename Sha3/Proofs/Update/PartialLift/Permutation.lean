import Sha3.Proofs.Update.PartialLift.Result
import Sha3.Proofs.Update.PermutationCall
import Sha3.Proofs.Update.FullBlocks

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def fillCallDisplacement : Variant → BitVec 32
  | .sha224 => 0x234
  | .sha256 => 0x554
  | .sha384 => 0x824
  | .sha512 => 0xad4

theorem fill_call_image (v : Variant) :
    ∀ byte ∈ codeRange (v.updateAddress + 0xe7#64) (encodeCallRel32 (fillCallDisplacement v)),
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2 := by
  cases v <;> decide +kernel

theorem fill_call_target (v : Variant) :
    branchTarget (v.updateAddress + 0xe7#64) 5 ((fillCallDisplacement v).signExtend 64) =
      Permutation.entryAddress .absorb := by
  cases v <;> decide +kernel

theorem fill_call_return (v : Variant) :
    BitVec.add (v.updateAddress + 0xe7#64) 5#64 = divisionAddress v := by
  cases v <;> decide +kernel

theorem FillResult.permutation_advance [Bindings] {v : Variant} {caller s t : RamState}
    {bytes : ByteArray} {state : Incremental.State} {initialBytes : Nat → UInt8}
    {position count : Nat} (hc : CallContext v caller bytes state)
    (hi : BodyInvariant caller s) (boundary : ReturnBoundary) (hb : ¬InProgram boundary.rip)
    (hinitial : Bytes s.external (caller.regValue .rsi) 200 initialBytes)
    (hposition : position < v.rate) (hcount : count ≤ bytes.size)
    (hfill : position + count = v.rate)
    (hr : FillResult v (caller.regValue .rsi) (caller.regValue .rdx) position count
      (fun i ↦ initialBytes (position + i)) (fun i ↦ (bytes.data[i]?).getD 0) s t) :
    ∃ u, Advances boundary 6340 t u ∧ BodyInvariant caller u ∧
      u.RIP = divisionAddress v ∧
      u.regValue .r15 = caller.regValue .rsi ∧
      (Operand.mem (frameBase caller) : Operand 64).read u =
        (Operand.mem (frameBase caller) : Operand 64).read s ∧
      u.regValue .rbx = caller.regValue .rdx + BitVec.ofNat 64 count ∧
      u.regValue .r12 = s.regValue .r12 ∧
      Permutation.memoryLanes (caller.regValue .rsi) u =
        (Incremental.update Keccak.keccakLanes v.rate
          ⟨Permutation.memoryLanes (caller.regValue .rsi) s, position⟩
          (bytes.extract 0 count)).lanes ∧
      (Incremental.update Keccak.keccakLanes v.rate
          ⟨Permutation.memoryLanes (caller.regValue .rsi) s, position⟩
          (bytes.extract 0 count)).cursor = 0 := by
  have it := bodyInvariant_of_frame hc hi hr.ready hr.frame
  obtain ⟨u, ha, iu, ipu, saved, lanes, _, slot⟩ := Update.permutation_advance hc it boundary hb
    (v.updateAddress + 0xe7#64) (fillCallDisplacement v) hr.rip hr.pointerReg
    (fill_call_image v) (fill_call_target v)
    (by rw [fill_call_return]; exact offset_inProgram v 0xec (by decide))
  have hsize : (bytes.extract 0 count).size = count := by
    simp only [ByteArray.size_extract, Nat.min_eq_left hcount, Nat.sub_zero]
  have hu := Incremental.update_eq_rate Keccak.keccakLanes v.rate
    (Incremental.State.mk (Permutation.memoryLanes (caller.regValue .rsi) s) position)
    (bytes.extract 0 count) hposition (by simpa only [hsize] using hfill)
  refine ⟨u, ha, iu, (fill_call_return v) ▸ ipu, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (saved .r15 (by simp)).trans hr.lanesReg
  · exact slot.trans (FullBlocks.slot_of_stateWrites hc hr.frame (stateWrites_clobbers caller position))
  · exact (saved .rbx (by simp)).trans hr.sourceReg
  · exact (saved .r12 (by simp)).trans (hr.frame.read (n := 64) (r := 12) (by simp [clobbers]))
  · rw [hu]
    exact lanes.trans (congrArg Keccak.keccakLanes
      (hr.lanes hinitial (by dsimp only; have := v.rate_le; omega) hcount))
  · rw [hu]

end Sha3.Proofs.Update.Partial
