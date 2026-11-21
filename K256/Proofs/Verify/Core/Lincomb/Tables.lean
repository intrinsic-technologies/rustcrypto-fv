import K256.Proofs.Verify.Core.Lincomb.Phases
import K256.Proofs.Verify.Core.Lincomb.Relocate

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)



theorem Copied.slotSub {m n : Ram} {fr : Activation} {src dst size : Nat}
    (copy : Copied m (slot fr src) n (slot fr dst) size) {off len : Nat} (fit : off + len ≤ size) :
    Copied m (slot fr (src + off)) n (slot fr (dst + off)) len := by
  simpa only [slot, BitVec.ofNat_add, BitVec.add_assoc] using copy.sub fit

theorem relocate {fr : Activation} {a b c g : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m n : Ram} (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) (frame : CallerFrame fr c g m n) (points : PeerPrepared fr g n p u v) :
    ∃ d t, Reaches .l10fc13 g n .l10fc62 d t ∧ CallerFrame fr c d m t ∧
      d[13] = ⟨64,slot fr 0x1568⟩ ∧
      Prepared t (slot fr 0x1568) (slot fr 0x1ce8) domain.G u ∧
      Prepared t (slot fr 0x1f08) (slot fr 0x2688) p v := by
  have df : c[22].get 1 = 0 := congrArg (Value.get 1) ((args.keep 22 (by decide)).trans h.df)
  have whole {g' : Registers} {t : Ram} (f : CallerFrame fr c g' m t) :=
    h.frame.trans f.frame (frameBounds e).1
  obtain ⟨a₁,m₁,s₁,f₁,r₁,h₁,c₁,w₁⟩ := CopySite.step .peerTable e (whole frame) frame
    ⟨points.digitsPtr,points.memcpy,points.tablePtr⟩ (fun h => (h rfl).elim) df
  obtain ⟨a₂,m₂,s₂,f₂,r₂,h₂,c₂,w₂⟩ := CopySite.step .peerDigits e (whole f₁) f₁ r₁ (fun _ => h₁) df
  obtain ⟨a₃,m₃,s₃,f₃,r₃,h₃,c₃,w₃⟩ := CopySite.step .generator e (whole f₂) f₂ r₂ (fun _ => h₂) df
  obtain ⟨a₄,m₄,s₄,f₄,r₄,_,c₄,w₄⟩ := CopySite.step .peer e (whole f₃) f₃ r₃ (fun _ => h₃) df
  have same {q q' : Ram} {site : CopySite} (f : RamWriteFrame q q' (workWrites fr 8 site.dst site.len))
      (off len : Nat) (fit : off + len ≤ 10952) (ok : off + len ≤ site.dst ∨ site.dst + site.len ≤ off) :
      Copied q (slot fr off) q' (slot fr off) len :=
    Copied.of_frame f (workOutside e (by decide) fit (by cases site <;> decide) ok)
  have gen₁ := points.generator.of_copy (same w₁ 0xbc8 1920 (by decide) (by decide))
    (same w₁ 0x1348 544 (by decide) (by decide))
  have peer₁ := points.peer.of_copy c₁ (same w₁ 8 544 (by decide) (by decide))
  have gen₂ := gen₁.of_copy (same w₂ 0xbc8 1920 (by decide) (by decide))
    (same w₂ 0x1348 544 (by decide) (by decide))
  have peer₂ := peer₁.of_copy (same w₂ 0x228 1920 (by decide) (by decide)) c₂
  have peer₃ := peer₂.of_copy (same w₃ 0x228 1920 (by decide) (by decide))
    (same w₃ 0x9a8 544 (by decide) (by decide))
  have gen₃ := gen₂.of_copy (c₃.slotSub (off := 0) (by decide)) (c₃.slotSub (off := 0x780) (by decide))
  exact ⟨a₄,m₄,((s₁.trans s₂).trans s₃).trans s₄,f₄,r₄.table,
    gen₃.of_copy (same w₄ 0x1568 1920 (by decide) (by decide))
      (same w₄ 0x1ce8 544 (by decide) (by decide)),
    peer₃.of_copy (c₄.slotSub (off := 0) (by decide)) (c₄.slotSub (off := 0x780) (by decide))⟩

end K256.Proofs.Verify.Core.Lincomb
