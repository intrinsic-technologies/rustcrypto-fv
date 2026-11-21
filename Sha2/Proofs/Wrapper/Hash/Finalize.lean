import Sha2.Proofs.Common.SHA256.Compression.Correctness
import Sha2.Proofs.Wrapper.Hash.Finalize.Pad
import Sha2.Proofs.Wrapper.Hash.Finalize.Compress
import Sha2.Proofs.Wrapper.Hash.Finalize.Control
import Sha2.Proofs.Wrapper.Hash.Finalize.Zero
import Sha2.Proofs.Common.Memory.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256

theorem finalize [Bindings] {v : Variant}
    {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context initial inputs v)
    (buffered : Buffered initial s message v) (rip : s.RIP = (v.pc 0x1bb)) :
    ∃ t, Compressed initial t message v := by
  obtain ⟨padded, padState⟩ := Finalize.pad ctx buffered rip
  obtain ⟨branched, branchState, branchRip, branchBytes⟩ := Finalize.branch ctx padState
  by_cases small : message.size % 64 < 56
  · have firstRip : branched.RIP = (v.pc 0x2b4) := by simpa only [small, ite_true] using branchRip
    have prefixBytes := Sha2.Proofs.Common.Memory.hasBytes_prefix branchBytes (count := 56) (by change 56 ≤ 64; decide)
    rw [Finalize.paddedBuffer_prefix message small] at prefixBytes
    obtain ⟨lengthReady, lengthState⟩ := Finalize.length ctx branchState firstRip prefixBytes
    obtain ⟨finished, finalState, finalRip⟩ := Finalize.compress_last Compression.block_correct ctx lengthState
    refine ⟨finished, ⟨finalState.toPreserved, finalRip, _, finalState.hashWords, ?_⟩⟩
    simpa only [Finalize.finalBlock, Finalize.finalPrefix, tailFirst, small, ite_true]
      using Finalize.digest_tail_compressions v message
  · have firstRip : branched.RIP = (v.pc 0x206) := by simpa only [small, ite_false] using branchRip
    obtain ⟨first, firstState, firstRip⟩ := Finalize.compress_first Compression.block_correct ctx branchState firstRip branchBytes
    obtain ⟨zeroed, zeroState, zeroRip, zeroBytes⟩ := Finalize.zero ctx firstState firstRip
    have prefixBytes : (⟨(stackPtr initial - 344).toNat, 56⟩ : MemoryRegion).HasBytes
        zeroed.external (Finalize.finalPrefix message) := by
      simpa only [Finalize.finalPrefix, small, ite_false] using zeroBytes
    obtain ⟨lengthReady, lengthState⟩ := Finalize.length ctx zeroState zeroRip prefixBytes
    obtain ⟨finished, finalState, finalRip⟩ := Finalize.compress_last Compression.block_correct ctx lengthState
    refine ⟨finished, ⟨finalState.toPreserved, finalRip, _, finalState.hashWords, ?_⟩⟩
    simpa only [Finalize.finalBlock, Finalize.finalPrefix, Finalize.paddedBuffer,
      tailFirst, tailLast, small, ite_false] using Finalize.digest_tail_compressions v message

end Sha2.Proofs.Wrapper.Hash
