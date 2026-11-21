import Sha1.Proofs.Compress.Machine.Cuts

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.NIST.SHA1

theorem blockData_of_snapshot80 {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s : RamState}
    (hFrame : FrameData stack input M s)
    (hWords : Write.AllHold s (snapshot80 stack input H M)) :
    BlockData stack input (compress H M) M s := by
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hWords
  exact ⟨⟨hWords.1, hWords.2.1, hWords.2.2.1, hWords.2.2.2.1,
    hWords.2.2.2.2.1⟩, hFrame.stackPointer, hWords.2.2.2.2.2, hFrame.writable,
    hFrame.readable, hFrame.words, hFrame.apart, hFrame.code⟩

end Sha1.Proofs.Compress.Machine
