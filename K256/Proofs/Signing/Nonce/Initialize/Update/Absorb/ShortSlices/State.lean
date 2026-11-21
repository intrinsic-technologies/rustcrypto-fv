import K256.Proofs.Verify.Hash.Update.State
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices.Memory
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Buffer

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private theorem resultBytes {fr : Activation} {m : Ram} {secret reduced : ByteArray}
    (env : Environment fr (.seeded secret reduced))
    (written : RamWriteFrame fr.original m [fr.region, ⟨fr.rdi.toNat,64⟩])
    (second last : Bool) :
    (⟨(destination fr second last).toNat, length last⟩ : MemoryRegion).HasBytes
      (result fr second last m) (if last then ByteArray.empty else reduced) := by
  cases last
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, bytes⟩ := env.slicesAt written
    change (MemoryRegion.mk (fr.rsp+208).toNat 32).HasBytes m reduced at bytes
    apply Verify.Hash.Update.bytesStore
    · apply Sec1.Wrapper.Copy.memCopy_hasBytes (by decide)
      apply Verify.Hash.Update.bytesStore bytes
      apply RangeApart.of_offsets (x := fr.rsp) (c := -720) (d := 208) (by unfold sp; bv_omega) rfl
      decide
    · apply RangeApart.of_offsets (x := context fr second) (c := 127) (d := 65) rfl
        (by change _ + 64 + 1 = _ + 65; bv_omega)
      decide
  · exact ⟨rfl, fun i => (Nat.not_lt_zero i.val i.isLt).elim⟩

theorem afterIteration {fr : Activation} {secret reduced input : ByteArray} {state : State}
    {a b : Verify.Core.Registers} {m : Ram} (second last : Bool)
    (env : Environment fr (.seeded secret reduced)) (live : Live (loopAt second) fr a m state)
    (slots : Slots fr m) (ctx : UpdateV.HmacStateAt m (context fr second) state.key input)
    (size : input.size % 64 = used last)
    (regs : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i])
    (r14 : second = false → b[14] = a[14])
    (widths : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → b[i].width = 64) :
    let n := result fr second last m
    Live (target second last) fr b n state ∧ Slots fr n ∧
      UpdateV.HmacStateAt n (context fr second) state.key (input ++ if last then ByteArray.empty else reduced) := by
  have dep := env.depth
  have lim := env.limit
  have writes := resultFrame env second last m
  have localWrites := resultLocal env second last
  have nextSlots := slotsAfter slots writes (slotOutside env second last 8 (by decide))
    (slotOutside env second last 112 (by decide)) (slotOutside env second last 120 (by decide))
  have tail (old : FrameTail fr a m) : FrameTail fr b (result fr second last m) :=
    frameTailAfter env old writes localWrites
  refine ⟨liveAfter env live writes localWrites ?_ widths ?_, nextSlots, ?_⟩
  · cases second
    · obtain ⟨rsp, df, si, mx, ft, fc, _, rest⟩ := live.atoms
      have saved : memLoad (result fr false last m) (fr.rsp - 592) 64 = fr.rdi := by
        rw [show fr.rsp - 592 = sp fr + 120 by unfold sp; bv_omega]
        exact nextSlots.state
      cases last <;> exact ⟨(regs 4 (by decide)).trans rsp, (regs 22 (by decide)).trans df,
        (r14 rfl).trans si, (regs 39 (by decide)).trans mx, (regs 50 (by decide)).trans ft,
        (regs 51 (by decide)).trans fc, saved, tail rest⟩
    · obtain ⟨rsp, df, mx, ft, fc, rest⟩ := live.atoms
      cases last <;> exact ⟨(regs 4 (by decide)).trans rsp, (regs 22 (by decide)).trans df,
        (regs 39 (by decide)).trans mx, (regs 50 (by decide)).trans ft,
        (regs 51 (by decide)).trans fc, tail rest⟩
  · cases second <;> cases last <;> intro h <;> cases h
  · have bytes := resultBytes env live.writes second last
    have len : (if last then ByteArray.empty else reduced).size = length last := bytes.1
    apply appendShortAfter ctx writes
    · rw [size,len]; cases last <;> decide
    · apply outsideResult <;> cases second <;> cases last <;> short_address
    · rw [size]
      apply outsideResult <;> cases second <;> cases last <;> short_address
    · apply outsideResult <;> cases second <;> cases last <;> short_address
    · apply outsideResult <;> cases second <;> cases last <;> short_address
    · rw [len,size]; exact bytes
    · rw [size,len]
      cases last <;> exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.ShortSlices
