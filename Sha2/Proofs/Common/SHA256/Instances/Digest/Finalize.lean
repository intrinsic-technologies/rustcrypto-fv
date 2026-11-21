import Sha2.Proofs.Common.SHA256.Instances.Digest.Code
import Sha2.Proofs.Common.SHA256.Instances.Finalize
import Sha2.Proofs.Common.SHA256.Finalize.State

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

 theorem normalized {s t : RamState} {message : ByteArray} {v : Wrapper.Variant}
    (hasher : HasherAt s (rspOf s) message v.initialHash)
    (result : (Blocks.Digest.Normalize.effect (Segment.normalize.pc v) s).Holds s t) :
    Finalize.Prepared (Finalization.digest.layout v) (rspOf s) message t := by
  have memory : t.external = s.external := result.agrees.external (by
    simp [Blocks.Digest.Normalize.effect, Effect.components, Component.Covers])
  have zero : (Finalization.digest.layout v).buffer (rspOf s) = rspOf s := BitVec.add_zero _
  have writes :
      t.regValue .r14 = rspOf s + 64 ∧
      t.regValue .r12 = (memLoad s.external (rspOf s + 63) 8).setWidth 64 ∧
      t.regValue .r13 = memLoad s.external (rspOf s + 96) 64 := result.writes
  have nextPC : Segment.normalize.pc v + 16 = (Finalization.digest.layout v).entry := by
    cases v <;> decide +kernel
  refine ⟨result.rip.trans nextPC, ?_, ?_, ?_, writes.2.2.trans hasher.blocks, ?_⟩
  · exact result.agrees.read (n := 64) (r := 4) (by simp [Blocks.Digest.Normalize.effect, Effect.components])
  · rw [zero]
    exact hasher.of_bytes (fun i _ => congrArg (fun m => m[rspOf s + BitVec.ofNat 64 i]?) memory)
  · change t.regValue .r12 = BitVec.ofNat 64 (message.size % 64)
    rw [writes.2.1, memLoad_8]
    change ((s.external[rspOf s + 63]?).getD 0).toBitVec.setWidth 64 = _
    rw [hasher.tailLength]
    simp only [Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, UInt8.toNat_toBitVec, UInt8.toNat_ofNat', BitVec.toNat_ofNat]
    have bound := Nat.mod_lt message.size (by decide : 0 < 64)
    omega

  · intro _
    change t.regValue .r14 = (Finalization.digest.layout v).buffer (rspOf s) + 64
    rw [zero]
    exact writes.1

end Sha2.Proofs.Common.SHA256.Instances.Digest
