import P256.Proofs.SHA256.Entry.Branch
import P256.Proofs.Program.LeafReturn

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem compression_correct_zero [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray}
    (pre : CompressionPre s boundary hash input 0) :
    ∃ t, CompressionResult s t boundary hash input ∧ t.external = s.external := by
  obtain ⟨u, run, ready, rip, frame⟩ := entry_branch pre
  have memory : u.external = s.external := frame.external (by simp [Component.Covers])
  have rip' : u.RIP = 0x1181a8 := by simpa only [ite_true] using rip
  obtain ⟨t, result, finalMemory, _⟩ := leaf_return [] (by simp) (by simp)
    pre.toCalleePre run ready (codeOffset := 0x181a8) rip' (by decide) (by decide +kernel)
    (frame.mono (by simp [leafComponents]))
  have totalMemory := finalMemory.trans memory
  refine ⟨t, ⟨result, ?_⟩, totalMemory⟩
  have size : input.size = 0 := pre.inputBytes.1
  have unchanged : compressBlocks hash input = hash := by
    simp only [compressBlocks, size, Nat.zero_div, compressBlocksFrom]
  rw [unchanged]
  exact ⟨pre.hashWords.1, fun i hi ↦ by
    rw [totalMemory]
    exact pre.hashWords.2 i hi⟩

end P256.Proofs.SHA256
