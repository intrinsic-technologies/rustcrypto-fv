import K256.Proofs.Ecdh.Decode.Convert.Representation
import K256.Proofs.Ecdh.Decode.Convert.Resume
import K256.Proofs.Ecdh.Decode.Convert.Entry
import K256.Proofs.Ecdh.Decode.Convert.Return

namespace K256.Proofs.Ecdh.Decode.Convert

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program K256.Proofs.CFG
open K256.Proofs.Refine K256.Proofs.Lift Ecdh.LIR Standards.SECG.ECC
open Standards.SECG.DomainParameters.Secp256k1 Generate.Generator.Multiply

theorem execution (fr : Activation) (a : Values Value Reg.count)
    (entry : Atom.All Extracted.programImage a fr.original (Fn10fa10.frameAt .l10fa10 fr))
    (src : Readable fr.original fr.rsi 84)
    (srcApart : Outside [ParseSignature.callStack fr] fr.rsi 84)
    (dst : Writable Extracted.programImage fr.original fr.rdi 120)
    (dstApart : Outside [ParseSignature.callStack fr] fr.rdi 120)
    {point : Curve.Point} (input : AffinePointAt fr.original fr.rsi point)
    (onCurve : Curve.onCurve domain point = true) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10fa10,a,fr.original⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn10fa10.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,120⟩] ∧
      ParseSignature.ArgumentWidths out.values ∧
      ∃ peer : Projective, peer.Stored out.store fr.rdi ∧ peer.valid ∧ peer.value = point := by
  obtain ⟨b,m,call,f,sp,bx,coords,keep,widths,writes,ret,saved⟩ :=
    convertEntry fr a entry src srcApart
  obtain ⟨o,run,tag,atoms,c,f',w,frame⟩ :=
    afterBarrier entry f sp bx coords keep widths writes ret saved
  obtain ⟨out,finish,tag',done_,stores,w',output⟩ :=
    convertReturn fr o.values o.store atoms c f' (flag_cases input) w (dst.of_frame frame) dstApart
  refine ⟨out,ParseSignature.exec_call call run ?_ ?_,tag',done_,?_,w',storedPoint input onCurve output⟩
  · rw [tag]
    rfl
  · exact finish
  · have subset {r : MemoryRegion} {rs : List MemoryRegion} (mem : r ∈ rs) : RegionsWithin [r] rs := by
      intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact ⟨_,mem,Nat.le_refl _,Nat.le_refl _⟩
    exact ((RamWriteFrame.refl _ _).trans frame (subset (List.mem_cons_self ..))).trans stores
      (subset (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

end K256.Proofs.Ecdh.Decode.Convert
