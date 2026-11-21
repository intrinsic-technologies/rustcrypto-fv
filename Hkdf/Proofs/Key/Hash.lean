import Hkdf.Proofs.Key.Hash.Blocks
import Hkdf.Proofs.Key.Hash.Buffer
import Hkdf.Proofs.Key.Hash.Pad
import Hkdf.Proofs.Key.Hash.Finish

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Hkdf.Proofs.Common.SHA256

theorem run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (ctx : Context initial boundary key)
    (prepared : Prepared initial boundary s) (rip : s.RIP = 0x11638e)
    (large : 64 < key.size) : ∃ t, Key.Ready initial boundary key t := by
  obtain ⟨a, initialized⟩ := prepare ctx prepared rip
  obtain ⟨b, stateB, ripB, hashB, tailPointerB, tailLengthB, blocksB⟩ :=
    compress_full_blocks ctx initialized
  have rspB : rspOf b = blockAddress initial := stateB.rsp
  have hashWords : HashStateAt b (rspOf b + 296)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash key) := by
    simpa only [rspB] using hashB
  have blocks : memLoad b.external (rspOf b + 328) 64 =
      BitVec.ofNat 64 (key.size / 64) := by
    simpa only [rspB] using blocksB
  obtain ⟨c, stateC, ripC, streamC⟩ := buffer ctx stateB ripB hashWords
    (tailPointerB.trans initialized.tailPointer)
    (tailLengthB.trans initialized.tailLength) blocks
  obtain ⟨d, stateD, ripD, hashD⟩ := pad ctx stateC ripC streamC
  exact finish ctx stateD ripD hashD large

end Hkdf.Proofs.Key.Hash
