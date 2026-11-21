import K256.Proofs.Signing.UpdateV.Finalize.Padding.Mark
import K256.Proofs.Signing.UpdateV.Finalize.Padding.Compress

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

theorem padding (outer : Bool) {a : Registers} {m : Ram} {sp src : BitVec 64} {msg : ByteArray}
    (rsp : a[4] = ⟨64,sp⟩) (df : a[22] = ⟨1,0⟩)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → a[i].width = 64)
    (source : if outer then src = sp + 208 else a[15].get 64 + 64 = src)
    (depth : 344 ≤ sp.toNat) (limit : sp.toNat + 312 < 2^32)
    (read : Readable m src 104) (above : sp.toNat + (if outer then 208 else 312) ≤ src.toNat)
    (stack : Writable Extracted.programImage m (sp - 344) 656)
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (state : Buffered m src msg) (small : msg.size % 64 < 56) :
    ∃ b t, Reaches (padStart outer) a m (padEnd outer) b t ∧
      b[4] = ⟨64,sp⟩ ∧ (∀ i : Fin Reg.count, i.val ∈ savedRegs → b[i] = a[i]) ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15] → b[i].width = 64) ∧
      RamWriteFrame m t [paddingRegion sp,⟨(sp + 271).toNat,1⟩] ∧
      (outer = false → memLoad t (sp + 271) 8 = 0) ∧
      Compression.StateAt t (sp + 72) (digestState msg) := by
  obtain ⟨b,t,first,kept,frame,clear,marked⟩ :=
    markPadding outer rsp df widths source depth limit read above stack image state small
  obtain ⟨c,u,last,rc,kc,wc,writes,digest⟩ :=
    compressPadding outer depth limit (stack.of_frame frame) marked
  refine ⟨c,u,first.trans last,rc,fun i hi => (kc i hi).trans (kept i hi),wc,
    frame.trans writes ?_,fun inner => ?_,digest⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
  · apply Eq.trans (writes.memLoad_eq ?_) (clear inner)
    have pos : (sp+271).toNat = sp.toNat + 271 := toNat_add_ofNat sp 271 (by omega)
    refine ⟨by omega, fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change sp.toNat - 344 + 520 ≤ _
    omega

end K256.Proofs.Signing.UpdateV.Finalize
