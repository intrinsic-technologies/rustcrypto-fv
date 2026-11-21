import Sha3.Proofs.Update.Partial.Context
import Sha3.Proofs.Update.FullBlocks.Context

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

theorem Context.of_invariant [Bindings] {v : Variant} {caller s : RamState}
    {bytes : ByteArray} {state : Incremental.State} {position count : Nat}
    (hc : CallContext v caller bytes state) (h : BodyInvariant caller s)
    (hpointer : (Operand.reg 15 : Operand 64).read s = caller.regValue .rsi)
    (hsource : (Operand.reg 3 : Operand 64).read s = caller.regValue .rdx)
    (hposition : (Operand.reg 0 : Operand 64).read s = BitVec.ofNat 64 position)
    (hposition_lt : position < v.rate) (hcount : position + count ≤ v.rate)
    (hsize : count ≤ bytes.size) :
    ∃ initialBytes : Nat → UInt8,
      Bytes s.external (caller.regValue .rsi) 200 initialBytes ∧
      Context v (caller.regValue .rsi) (caller.regValue .rdx) position count
        (fun i ↦ initialBytes (position + i)) (fun i ↦ (bytes.data[i]?).getD 0) s := by
  let initialBytes := fun i ↦ memByte s.external (caller.regValue .rsi + BitVec.ofNat 64 i)
  have hbytes : Bytes s.external (caller.regValue .rsi) 200 initialBytes :=
    Bytes.of_isSome (fun i hi ↦ h.grows _ (hc.stateRead.mem i (by omega)))
  have hrate := v.rate_le
  refine ⟨initialBytes, hbytes, h.ready,
    CodeIn.of_loaded h.loaded (SectionsLow.codeLow programSections_low), hpointer,
    hsource, hposition, hposition_lt, hcount, ?_, hbytes.sub position (200 - position) (by omega),
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [h.memory]
    · exact hc.inputBytes i (by omega)
    · intro region hr hcontains
      exact hc.inputApart region hr _ (FullBlocks.input_contains hc (by omega)) hcontains
  · have hl := hc.inputRead.low
    omega
  · have hl := hc.stateRead.low
    simp only [destination, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro i hi j hj he
    have hs := FullBlocks.state_contains hc (i := position + i) (by omega)
    have hr := FullBlocks.input_contains hc (i := j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hs
    change caller.regValue .rsi + BitVec.ofNat 64 position + BitVec.ofNat 64 i =
      caller.regValue .rdx + BitVec.ofNat 64 j at he
    rw [he] at hs
    exact hc.inputApart (stateRegion caller) (by simp [writeRegions]) _ hr hs
  · intro i hi
    have hs := FullBlocks.state_contains hc (i := position + i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hs
    exact hc.avoids (stateRegion caller) (by simp [writeRegions]) _ hs

end Sha3.Proofs.Update.Partial
