import Sha2.Proofs.Common.SHA256.Finalize.Contract
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Pad
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Compress
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Control
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Zero
import Sha2.Proofs.Common.Memory.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] (L : Layout) : Contract L := by
  intro initial s n reserve regions message wf flow code blocks stride machine stack avoids
    returnAddress state prepared within
  let ctx : Context L initial regions reserve :=
    ⟨wf, flow, code, blocks, stride, machine, stack, avoids, returnAddress, within⟩
  obtain ⟨padded, padState⟩ := pad ctx state prepared
  obtain ⟨branched, branchState, branchRip, branchBytes⟩ := branch ctx padState
  by_cases small : message.size % 64 < 56
  · have firstRip : branched.RIP = L.length := by simpa only [small, ite_true] using branchRip
    have prefixBytes := Sha2.Proofs.Common.Memory.hasBytes_prefix branchBytes (count := 56)
      (by change 56 ≤ 64; decide)
    rw [Sha2.Proofs.Wrapper.Hash.Finalize.paddedBuffer_prefix message small] at prefixBytes
    obtain ⟨lengthReady, lengthState⟩ := length ctx branchState firstRip prefixBytes
    obtain ⟨finished, finalState, finalRip, pointer⟩ := compress_last ctx lengthState
    refine ⟨finished, ⟨finalState.toPreserved, finalRip, pointer, _, finalState.hashWords, ?_⟩⟩
    simpa only [finalBlock, finalPrefix, Sha2.Proofs.Wrapper.Hash.Finalize.finalBlock,
      Sha2.Proofs.Wrapper.Hash.Finalize.finalPrefix, tailFirst, small, ite_true]
      using Sha2.Proofs.Wrapper.Hash.Finalize.digest_tail_compressions L.hashVariant message
  · have firstRip : branched.RIP = L.firstHead := by simpa only [small, ite_false] using branchRip
    obtain ⟨first, firstState, firstRip⟩ := compress_first ctx branchState firstRip branchBytes
    obtain ⟨zeroed, zeroState, zeroRip, zeroBytes⟩ := zero ctx firstState firstRip
    have prefixBytes : (⟨(L.buffer (L.sp initial)).toNat, 56⟩ : MemoryRegion).HasBytes
        zeroed.external (finalPrefix message) := by
      simpa only [finalPrefix, Sha2.Proofs.Wrapper.Hash.Finalize.finalPrefix, small, ite_false] using zeroBytes
    obtain ⟨lengthReady, lengthState⟩ := length ctx zeroState zeroRip prefixBytes
    obtain ⟨finished, finalState, finalRip, pointer⟩ := compress_last ctx lengthState
    refine ⟨finished, ⟨finalState.toPreserved, finalRip, pointer, _, finalState.hashWords, ?_⟩⟩
    simpa only [finalBlock, finalPrefix, paddedBuffer, Sha2.Proofs.Wrapper.Hash.Finalize.finalBlock,
      Sha2.Proofs.Wrapper.Hash.Finalize.finalPrefix, Sha2.Proofs.Wrapper.Hash.Finalize.paddedBuffer,
      tailFirst, tailLast, small, ite_false] using Sha2.Proofs.Wrapper.Hash.Finalize.digest_tail_compressions L.hashVariant message

end Sha2.Proofs.Common.SHA256.Finalize
