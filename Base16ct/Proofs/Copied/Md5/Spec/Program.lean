import Prelude
import Base16ct.Proofs.Copied.Md5.Spec.State
import Base16ct.Proofs.Copied.Md5.Spec.Program.Binary.Image

namespace Base16ct.Proofs.Copied.Md5.Spec.Program

open Prelude X86 Standards.RFC

def InPageTables (address : BitVec 64) : Prop :=
  ∃ region ∈ #v[(⟨0x1000, 8⟩ : MemoryRegion), ⟨0x2000, 32⟩], region.Contains address.toNat

namespace Slices

end Slices

namespace Digest

end Digest

namespace OneMessage

end OneMessage

namespace TwoMessages

end TwoMessages

namespace ResetThenDigest

end ResetThenDigest

namespace NewWithPrefix

end NewWithPrefix

namespace DynFinalizeInto

end DynFinalizeInto

namespace DynFinalizeIntoReset

end DynFinalizeIntoReset

namespace DynFinalizeBoxed

end DynFinalizeBoxed

namespace DeserializeDigestSlices

end DeserializeDigestSlices

namespace Compress

end Compress

namespace CoreUpdateBlocks

end CoreUpdateBlocks

namespace CoreFinalize

end CoreFinalize

namespace CoreReset

end CoreReset

end Base16ct.Proofs.Copied.Md5.Spec.Program
