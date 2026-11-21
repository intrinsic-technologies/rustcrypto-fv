import K256.Proofs.Common.Machine
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Sec1.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.Refine

theorem stackWritable {s : RamState} {bytes : ByteArray} {offset len : Nat}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (depth : offset ≤ 1928)
    (fits : len ≤ offset + 8) (pos : 0 < len) :
    Writable Extracted.programImage s.external (stackPtr s - BitVec.ofNat 64 offset) len := by
  let region := Stack.region s publicKeyFromSec1Bytes.minStackBytes
  have room : 1928 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have index : (BitVec.ofNat 64 offset).toNat = offset :=
    Nat.mod_eq_of_lt (by omega)
  have start : (stackPtr s - BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - offset := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, index]; omega), index]
  have belongs : region ∈ writtenRegions publicKeyFromSec1Bytes s := by
    simp [region, writtenRegions, publicKeyFromSec1Bytes]
  apply Writable.of_avoids call.stackAvailable.1 call.stackAvailable.2.1
    (call.separation.2 _ belongs).1
  · exact fun x hx => Or.inl ⟨x.2, Common.programSections_fetchByte_of_mem hx⟩
  · intro b hb
    have := not_pageTableEntriesApart_frames hb
    exact Or.inr (contains_iff.mpr (by simp only [pageTables]; omega))
  · rw [start]
    change (stackPtr s).toNat - 1928 ≤ _
    omega
  · rw [start]
    change _ ≤ (stackPtr s).toNat - 1928 +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 1928))
    omega
  · exact pos

end K256.Proofs.Sec1.Wrapper
