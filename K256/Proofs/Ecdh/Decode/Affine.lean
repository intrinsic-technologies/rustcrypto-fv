import K256.Proofs.Ecdh.Decode.Affine.Identity
import K256.Proofs.Ecdh.Decode.Affine.Coordinates
import K256.Proofs.Ecdh.Transfer
import K256.Proofs.Ecdh.Decode.Input

namespace K256.Proofs.Ecdh.Decode.Affine

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Ecdh.LIR
open Standards.SECG.ECC

theorem execution {fr : Activation} {args m bytes} (e : Entry fr args m bytes)
    {p : Curve.Point} (h : K256.Spec.Secp256k1.groupPoint bytes = some p) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l121480,args,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ out.values[4] = ⟨64,fr.rsp+8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = args[i]) ∧
      RamWriteFrame m out.store (writes fr) ∧ memLoad out.store (fr.rdi+88) 8 = 1 ∧
      AffinePointAt out.store fr.rdi p ∧ CallerWidths out.values := by
  rcases groupPoint_cases h with ⟨rfl,rfl⟩ | ⟨size,tag,header,valid,decoded⟩
  · obtain ⟨out,run,post⟩ := identityExecution e (by decide)
    exact ⟨out,Transfer.sec1Exec (src := .l121480) (dst := .l121480) (by decide) rfl run,post⟩
  · obtain ⟨out,run,post⟩ := coordinateExecution e header valid size decoded
    exact ⟨out,Transfer.sec1Exec (src := .l121480) (dst := .l121480) (by decide) rfl run,post⟩

end K256.Proofs.Ecdh.Decode.Affine
