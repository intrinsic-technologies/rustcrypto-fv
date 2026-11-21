import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Finish
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Frames
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Result
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.Runtime.StackGeometry

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem return_from_core {code : CodeMap} {fr child : Activation}
    {args : Values Value Reg.count} {before : Ram} {sealed : ByteArray}
    {out : Output Value Ram Reg.count} {result : Option ByteArray}
    (hworking : Atom.All code args before (LIR.Aes128gcmDecryptInPlace.frameAt .l10128b fr))
    (hframe : RamWriteFrame fr.original before [fr.region])
    (hsetup : RamWriteFrame before child.original [span (fr.rsp - 464) 48])
    (hsp : child.rsp = fr.rsp - 464) (hlow : child.low = fr.rsp - 2848)
    (hdesc : child.r8 = fr.rsp - 456 + 16)
    (h39 : child.mxcsr = fr.mxcsr) (h50 : child.ftw = fr.ftw) (h51 : child.fcw = fr.fcw)
    (hsize : 16 ≤ sealed.size) (hsep : (callStack fr).Disjoint (span fr.r8 sealed.size))
    (hdone : Atom.All code out.values out.store (LIR.Fn1022c0.frameInfo.doneAtoms child))
    (htyped : GPRsTyped out.values)
    (hwrites : RamWriteFrame child.original out.store
      [child.region, span fr.r8 (sealed.size - 16), span (child.r8 + 8) 8])
    (hpost : match result with
      | some plain => out.values[0].get 8 = 0 ∧
          (span fr.r8 (sealed.size - 16)).HasBytes out.store plain
      | none => out.values[0].get 8 = 1 ∧ RamWriteFrame child.original out.store [child.region]) :
    ∃ final, LIR.program.Exec (dialect code) ⟨⟨.l1012cf, out.values, out.store⟩, []⟩ final ∧
      resultPost code fr (sealed.size - 16) result final := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, saved3, saved12, saved13, saved14,
    saved15, saved5, retRead, savedRet, retLow, stack, room, _⟩ := hworking
  change Readable before fr.rsp 8 at retRead
  change Writable code before (fr.rsp - 2848) 2848 at stack
  change fr.low.toNat + 2848 ≤ fr.rsp.toNat at room
  have lowerNat : (fr.rsp - (2848 : BitVec 64)).toNat = fr.rsp.toNat - 2848 :=
    stack_sub_toNat fr room (Nat.le_refl _)
  have childNat : (fr.rsp - (464 : BitVec 64)).toNat = fr.rsp.toNat - 464 :=
    stack_sub_toNat fr room (by decide)
  have savedNat : (fr.rsp - (48 : BitVec 64)).toNat = fr.rsp.toNat - 48 :=
    stack_sub_toNat fr room (by decide)
  have slotAddr : child.r8 + 8 = fr.rsp - 456 + 24 := by
    rw [hdesc]
    bv_omega
  have slotNat : (child.r8 + 8).toNat = fr.rsp.toNat - 432 := by
    have he : fr.rsp - 456 + (24 : BitVec 64) = fr.rsp - 432 := by bv_omega
    rw [slotAddr, he]
    exact stack_sub_toNat fr room (by decide)
  have childRoom : child.low.toNat ≤ child.rsp.toNat := by
    rw [hlow, hsp, lowerNat, childNat]
    omega
  have stackSep : (span fr.r8 sealed.size).Disjoint (span (fr.rsp - 2848) 2856) := by
    intro addr hbuf hstack
    apply hsep addr ?_ hbuf
    simp only [MemoryRegion.Contains, callStack, span, lowerNat] at hstack ⊢
    omega
  have coreOutside : Outside [child.region, span fr.r8 (sealed.size - 16),
      span (child.r8 + 8) 8] (fr.rsp - 48) 56 := by
    rw [slotAddr]
    exact core_saved_outside false fr.rsp fr.r8 sealed.size child
      (show 2848 ≤ fr.rsp.toNat by omega) retRead.low hsize hsp childRoom stackSep
  let setupRegion := span (fr.rsp - 464) 48
  let payload := span fr.r8 (sealed.size - 16)
  let regions := [setupRegion, child.region, payload, span (child.r8 + 8) 8]
  have throughCore : RamWriteFrame before out.store regions := by
    refine ⟨?_, fun x hx => hwrites.present x (hsetup.present x hx)⟩
    intro x hx
    rw [hwrites.outside x ⟨hx.1, fun r hr => hx.2 r (List.mem_cons_of_mem _ hr)⟩]
    exact hsetup.outside x ⟨hx.1, fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hx.2 _ (List.mem_cons_self ..)⟩
  have savedOutside : Outside regions (fr.rsp - 48) 56 := by
    refine ⟨coreOutside.1, ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · right
      simp only [setupRegion, span, childNat, savedNat]
      omega
    · exact coreOutside.2 r hr
  have workRead : Readable before (fr.rsp - 456) 456 :=
    stack.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have finishRead : Readable before (fr.rsp - 456) 464 := by
    apply readable_append (k := 8) workRead
    have he : fr.rsp - 456 + BitVec.ofNat 64 456 = fr.rsp := by bv_omega
    rw [he]
    exact retRead
  obtain ⟨doneSP, doneDF, _, _, _, _, _, _, doneMXCSR, doneFTW, doneFCW, _⟩ := hdone
  change out.values[4] = ⟨64, child.rsp + 8⟩ at doneSP
  change out.values[39] = ⟨32, child.mxcsr⟩ at doneMXCSR
  change out.values[50] = ⟨16, child.ftw⟩ at doneFTW
  change out.values[51] = ⟨16, child.fcw⟩ at doneFCW
  have outSP : out.values[4].get 64 = fr.rsp - 456 := by
    rw [doneSP, hsp]
    change fr.rsp - 464 + 8 = fr.rsp - 456
    bv_omega
  obtain ⟨final, exec, tag, done, _, mem, status⟩ :=
    status_exec_of_frame false code fr out.values before out.store regions throughCore savedOutside
      htyped outSP (outSP ▸ finishRead) savedRet retLow saved3 saved12 saved13 saved14 saved15 saved5
      doneDF (h39 ▸ doneMXCSR) (h50 ▸ doneFTW) (h51 ▸ doneFCW)
  have setupInStack : RegionsWithin [setupRegion] [fr.region] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region, List.mem_singleton_self _, ?_, ?_⟩ <;>
      simp only [setupRegion, span, Activation.region, childNat] <;> omega
  have setupFrame := hframe.trans hsetup setupInStack
  have childInStack : fr.region.start ≤ child.region.start ∧
      child.region.start + child.region.size ≤ fr.region.start + fr.region.size := by
    simp only [Activation.region, hlow, hsp, lowerNat, childNat]
    omega
  refine ⟨final, exec, tag, done, ?_⟩
  cases result with
  | none =>
    refine ⟨by rw [status, hpost.1]; rfl, ?_⟩
    rw [mem]
    apply setupFrame.trans hpost.2
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨fr.region, List.mem_singleton_self _, childInStack⟩
  | some plain =>
    refine ⟨by rw [status, hpost.1]; rfl, ?_, mem ▸ hpost.2⟩
    rw [mem]
    have setupWide : RamWriteFrame fr.original child.original [fr.region, payload] :=
      (RamWriteFrame.refl _ _).trans setupFrame (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨fr.region, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩)
    apply setupWide.trans hwrites
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fr.region, List.mem_cons_self .., childInStack⟩
    · exact ⟨payload, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨fr.region, List.mem_cons_self .., ?_, ?_⟩ <;>
        simp only [span, Activation.region, slotNat] <;> omega

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
