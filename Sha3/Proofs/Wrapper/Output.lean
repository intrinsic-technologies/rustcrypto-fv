import Sha3.Proofs.Wrapper.ExecutionSpec
import Sha3.Proofs.Finalize.Contract
import Sha3.Proofs.Incremental.Padding

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem output_of_canonical {v : Variant} {mode : Mode} {initial final : RamState}
    {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hbytes : ∀ i : Fin (v.digestBytes fullState),
      final.external[BitVec.ofNat 64 ((mode.output (mode.entry v keccak fullState) initial).start + i.val)]? =
        some (Finalize.digest v (Incremental.canonicalState Keccak.keccakLanes v.rate
          (message (afterInputs mode inputs split))) keccak fullState)[i]) :
    readBytes (mode.output (mode.entry v keccak fullState) initial) (mode.entry v keccak fullState).outputBytes final = .ok (expectedDigest v mode inputs split keccak fullState) := by
  apply readBytes_eq_of_bytes
  intro i
  have hi : i.val < v.digestBytes fullState := by
    rw [← Mode.entry_digestBytes mode v keccak fullState]
    exact i.isLt
  have hb := hbytes ⟨i.val, hi⟩
  simpa only [expectedDigest, Finalize.digest,
    Incremental.finalize_canonicalState _ _ v.rate_pos _ (Variant.suffix keccak), Absorption.digestLanes,
    Fin.getElem_fin, Vector.getElem_ofFn] using hb

theorem beforeOutput_of_canonical {v : Variant} {mode : Mode} {initial final : RamState}
    {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hbytes : ∀ i : Fin (v.digestBytes fullState),
      final.external[BitVec.ofNat 64
          ((outputRegion (mode.entry v keccak fullState) initial).start + i.val)]? =
        some (Finalize.digest v (Incremental.canonicalState Keccak.keccakLanes v.rate
          (message (inputs.extract 0 split))) keccak fullState)[i]) :
    readOutput (mode.entry v keccak fullState) initial final =
      .ok (expectedBeforeDigest v inputs split mode keccak fullState) := by
  apply readOutput_eq_of_bytes
  intro i
  have hi : i.val < v.digestBytes fullState := by
    rw [← Mode.entry_digestBytes mode v keccak fullState]
    exact i.isLt
  have hb := hbytes ⟨i.val, hi⟩
  simpa only [expectedBeforeDigest, Finalize.digest,
    Incremental.finalize_canonicalState _ _ v.rate_pos _ (Variant.suffix keccak), Absorption.digestLanes,
    Fin.getElem_fin, Vector.getElem_ofFn] using hb

theorem readOutput_congr {entry : Routine} {output : Routine → RamState → MemoryRegion}
    {initial s t : RamState}
    (he : ∀ i : Fin entry.outputBytes,
      t.external[BitVec.ofNat 64 ((output entry initial).start + i.val)]? =
        s.external[BitVec.ofNat 64 ((output entry initial).start + i.val)]?) :
    readBytes (output entry initial) entry.outputBytes t = readBytes (output entry initial) entry.outputBytes s := by
  simp only [readBytes, he]

theorem readOutput_of_memoryWriteFrame {entry : Routine}
    {output : Routine → RamState → MemoryRegion} {initial s t : RamState}
    {regions : Vector MemoryRegion n}
    (hBound : (output entry initial).Bounded)
    (hSize : (output entry initial).size = entry.outputBytes)
    (hFrame : MemoryWriteFrame s t regions)
    (hApart : ∀ region ∈ regions, (output entry initial).Disjoint region) :
    readBytes (output entry initial) entry.outputBytes t = readBytes (output entry initial) entry.outputBytes s := by
  apply readOutput_congr
  intro i
  apply hFrame
  intro region hr ha
  apply hApart region hr _ ?_ ha
  have hLow : (output entry initial).start + (output entry initial).size < 2^32 := hBound
  have hi := i.isLt
  simp only [MemoryRegion.Contains, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  constructor <;> omega

end Sha3.Proofs.Wrapper
