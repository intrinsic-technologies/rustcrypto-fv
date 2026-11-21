import Sha3.Proofs.Wrapper.Loop.Instructions
import Sha3.Proofs.Wrapper.Loop.Preservation
import Sha3.Proofs.InputSlices

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {keccak fullState : Bool}

private theorem tableAddress_of_index {kind : Kind} {base : BitVec 5} {s : RamState}
    {address : BitVec 64} {i : Nat}
    (hbase : (Operand.reg base : Operand 64).read s = address)
    (hindex : (Operand.reg (kind.indexReg v fullState) : Operand 64).read s = BitVec.ofNat 64 i) :
    tableAddress kind base s (v := v) (fullState := fullState) = address + BitVec.ofNat 64 (8 * i) := by
  rw [tableAddress, hbase, hindex, BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  rw [Nat.mul_comm 8 i, BitVec.ofNat_mul]
  rfl

theorem State.prefix [bindings : Bindings] {initial s : RamState} {v : Variant}
    {kind : Kind} {inputs : Array Input} {start stop i split : Nat}
    (h : State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop i s)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v kind.mode initial inputs split)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (hip : s.RIP = kind.start v (keccak := keccak) (fullState := fullState)) (hi : i < inputs.size) :
    ∃ t, Advances (returnBoundary initial) 5 s t ∧
      State (keccak := keccak) (fullState := fullState) initial v kind inputs start stop i t ∧
      t.RIP = kind.start v (keccak := keccak) (fullState := fullState) + BitVec.ofNat 64 (kind.callOffset v fullState) ∧
      (Operand.reg (kind.nextReg v fullState) : Operand 64).read t = BitVec.ofNat 64 (i + 1) ∧
      t.regValue .rdx = inputs[i].address ∧
      t.regValue .rcx = BitVec.ofNat 64 inputs[i].bytes.size ∧
      t.regValue .rsi = statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode ∧
      t.regValue .rdi = statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode + 200 ∧
      AgreesExcept (prefixClobbers kind v fullState) s t := by
  have hp : tableAddress kind 12 s (v := v) (fullState := fullState) = initial.regValue .rdi + BitVec.ofNat 64 (8 * i) :=
    tableAddress_of_index h.registers.pointers h.index
  have hl : tableAddress kind 14 s (v := v) (fullState := fullState) = initial.regValue .rdx + BitVec.ofNat 64 (8 * i) :=
    tableAddress_of_index h.registers.lengths h.index
  have hpLoad := pointerTable_load_of_memoryWriteFrame (i := ⟨i, hi⟩)
    (hCall.inputSlices kind.mode_ne_digest) (hCall.sliceSeparation kind.mode_ne_digest) h.invariant.frame
  have hlLoad := lengthTable_load_of_memoryWriteFrame (i := ⟨i, hi⟩)
    (hCall.inputSlices kind.mode_ne_digest) (hCall.sliceSeparation kind.mode_ne_digest) h.invariant.frame
  obtain ⟨t, hrun, hready, _, htip, hnext, hptr, hlen, hstate, hcursor, hframe⟩ :=
    prefix_advance kind v (keccak := keccak) (fullState := fullState) (hfull := fun hf ↦ (hCall.fullState_valid hf).1) s h.invariant.ready h.invariant.loaded outside hip
      (by rw [hp]; exact hpLoad.1) (by rw [hl]; exact hlLoad.1)
      (by
        rw [h.registers.pointer]
        cases hc : kind.cursorReg v fullState with
        | none =>
          simp only [cursorValue, hc]
          change s.regValue .rsp + _ = _
          rw [h.registers.stack]
          cases kind <;> cases v <;> cases fullState <;>
            simp_all [Kind.cursorReg, Kind.largeFollower, Kind.cursorStackOffset,
              statePointer, Kind.mode, Mode.stateOffset, BitVec.add_assoc]
        | some r => simpa only [cursorValue, hc] using h.registers.cursor r hc)

  have hframe' : AgreesExcept (prefixClobbers kind v fullState) s t := hframe
  refine ⟨t, hrun, h.after_prefix hCall hready hframe', htip, ?_, ?_, ?_, ?_, ?_, hframe'⟩
  · simpa only [h.index, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using hnext
  · exact hptr.trans (by simpa only [hp, Operand.read, Fin.getElem_fin] using hpLoad.2)
  · exact hlen.trans (by simpa only [hl, Operand.read, Fin.getElem_fin] using hlLoad.2)
  · exact hstate.trans h.registers.pointer
  · exact hcursor.trans (congrArg (· + 200) (hstate.trans h.registers.pointer))

end Sha3.Proofs.Wrapper.Loop
