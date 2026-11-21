import K256.Proofs.Verify.Wrapper.HashFinalize.State
import K256.Proofs.Verify.Hash.Mark.Call
import K256.Proofs.Verify.Hash.Mark.ZeroFill
import K256.Proofs.Verify.Hash.Mark.Buffer
import K256.Proofs.Verify.LIR.Fn106390.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy

namespace K256.Proofs.Verify.Wrapper.HashFinalize

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC Hash.FinalBlocks
open Hash.Mark (copied marked pushed resume)

variable {initial : RamState} {key msg sig : ByteArray} {p : Curve.Point} {r s : Nat}
    {a : Core.Registers} {m : Ram}

set_option maxHeartbeats 600000 in
theorem mark (call : ValidCall verifyingKeyVerify initial [key,msg,sig])
    (buffer : HashBuffer initial a m p r s msg) :
    ∃ b t, Core.Reaches .l103170 a m
      (if msg.size % 64 < 56 then .l103289 else .l1031cd) b t ∧
      State initial b t p r s msg (Hash.compressBlocks Hash.initialHash msg) ∧
      (⟨(localSp initial + 8).toNat,64⟩ : MemoryRegion).HasBytes t (Hash.paddedBuffer msg) := by
  let sp := localSp initial
  let n := msg.size % 64
  let dst := sp + 9 + BitVec.ofNat 64 n
  let rem := 63 - n
  let padding : List MemoryRegion := [⟨(sp-8).toNat,80⟩]
  obtain ⟨depth, low⟩ := Hash.Update.stackBounds call
  have base : sp.toNat = (stackPtr initial).toNat - 536 :=
    Common.stackOffset call.stackAvailable (by decide)
  have dep : 8 ≤ sp.toNat := by omega
  have room : sp.toNat + 352 ≤ 2^32 := by omega
  have nBound : n < 64 := Nat.mod_lt _ (by decide)
  have slotNat : (sp-8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp from dep)
  have atNat (off : Nat) (bound : off ≤ 352) :
      (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off :=
    toNat_add_ofNat _ _ (by omega)
  have markNat : (sp+8+BitVec.ofNat 64 n).toNat = sp.toNat + 8 + n := by
    rw [BitVec.add_assoc]
    change (sp + (BitVec.ofNat 64 8 + BitVec.ofNat 64 n)).toNat = _
    rw [← BitVec.ofNat_add, atNat (8+n) (by omega)]
    omega
  have dstNat : dst.toNat = sp.toNat + 9 + n := by
    change (sp+9+BitVec.ofNat 64 n).toNat = _
    rw [BitVec.add_assoc]
    change (sp + (BitVec.ofNat 64 9 + BitVec.ofNat 64 n)).toNat = _
    rw [← BitVec.ofNat_add, atNat (9+n) (by omega)]
    omega
  have copyNat : (sp+8).toNat = sp.toNat + 8 := atNat 8 (by decide)
  have sourceNat : (sp+248).toNat = sp.toNat + 248 := atNat 248 (by decide)
  have posNat : (sp+71).toNat = sp.toNat + 71 := atNat 71 (by decide)
  have countNat : (sp+104).toNat = sp.toNat + 104 := atNat 104 (by decide)
  have window : Writable Extracted.programImage m (sp-8) 360 :=
    Hash.Update.writable (off := 544) call buffer.memory
      (by dsimp only [sp,localSp]; bv_omega) (by decide) (by decide) (by decide)
  have slotIn (ptr : BitVec 64) (len : Nat)
      (lo : (sp-8).toNat ≤ ptr.toNat) (hi : ptr.toNat + len ≤ (sp-8).toNat + 80) :
      InRegions padding ptr len :=
    ⟨_, List.mem_cons_self, lo, hi, by omega⟩
  have copyFrame : RamWriteFrame m (copied m sp) (Hash.Update.footprint initial) :=
    Sec1.Wrapper.Copy.memCopy_frame (.refl _ _) (Hash.Update.frameSlot (off := 528) call
      (by dsimp only [sp,localSp]; bv_omega) (by decide) (by decide))
  have markFrame : RamWriteFrame (copied m sp) (marked m sp n) padding :=
    (RamWriteFrame.refl _ _).memStore _ (slotIn _ 1 (by omega) (by omega))
  have pushFrame : RamWriteFrame (copied m sp) (pushed m sp n) padding :=
    markFrame.memStore _ (slotIn _ 8 (by omega) (by omega))
  have padWithin : RegionsWithin padding (Hash.Update.footprint initial) := by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_, ?_⟩
    · change (stackPtr initial).toNat - 880 ≤ (sp-8).toNat
      omega
    · change (sp-8).toNat + 80 ≤ (stackPtr initial).toNat - 880 + 696
      omega
  have included x hx := Common.fnCode_subset_programImage x (code_l103170 x hx)
  have copyGuard : RepMovsOk Extracted.programImage m 0 (sp+248) (sp+8) 13 8 0x103182 3 := by
    have source : Readable m (sp+248) 104 := window.readable.sub (by omega) (by omega)
    have destination : Writable Extracted.programImage m (sp+8) 104 :=
      window.sub (by omega) (by omega)
    exact Generate.Generator.Multiply.Prepare.copyGuard source
      (ParseSignature.storeOk_of_codeRange (off := 18) destination included (by decide))
      (Or.inr (by change (sp+8).toNat + 104 ≤ (sp+248).toNat; omega))
  have copiedWin := window.of_frame copyFrame
  have markedWin := copiedWin.of_frame markFrame
  have markGuard : StoreOk Extracted.programImage (copied m sp)
      (sp+8+BitVec.ofNat 64 n) 1 0x103197 6 :=
    ParseSignature.storeOk_of_codeRange (off := 39) (copiedWin.sub (by omega) (by omega))
      included (by decide)
  have pushGuard : StoreOk Extracted.programImage (marked m sp n) (sp-8) 8 0x1031bd 6 :=
    ParseSignature.storeOk_of_codeRange (off := 77) (markedWin.sub (by omega) (by omega))
      included (by decide)
  have markedMemory := Hash.Update.advance call buffer.memory (copyFrame.trans markFrame padWithin)
  obtain ⟨gotRead, gotTarget⟩ := Verify.LIR.Fn106390.callSlots_loaded
    (sections := Extracted.programSections) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (inputMemory call markedMemory.frame).2.2.2 (0x203e10, 0x12a700) (by decide)
  have df : a[22].get 1 = 0 := congrArg (Value.get 1) buffer.df
  obtain ⟨args, enter, count, hashReg, spReg, byte, dstReg, remReg, lenReg, preserveCall⟩ :=
    Hash.Mark.call (sp := sp) msg.size (congrArg (Value.get 64) buffer.rsp) df copyGuard
      (LoadOk.of_region copiedWin.readable (by omega) (by omega))
      (LoadOk.of_region copiedWin.readable (by omega) (by omega))
      buffer.pos buffer.count markGuard pushGuard ⟨gotRead.low, gotRead.present⟩ gotTarget
  have remNat : (BitVec.ofNat 64 rem).toNat = rem := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have pushedWin := copiedWin.of_frame pushFrame
  have retWord : memLoad (pushed m sp n) (sp-8) 64 = 0x1031c3 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have retRead : LoadOk (pushed m sp n) (sp-8) 8 :=
    LoadOk.of_region pushedWin.readable (by omega) (by omega)
  have fillWin : Writable Extracted.programImage (pushed m sp n) dst (BitVec.ofNat 64 rem).toNat :=
    pushedWin.sub (by omega) (by rw [remNat]; omega)
  have retApart : Outside [ParseSignature.buffer dst (BitVec.ofNat 64 rem).toNat] (sp-8) 8 := by
    refine ⟨by omega, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inl (by change (sp-8).toNat + 8 ≤ dst.toNat; omega)
  have argsDf : args[22].get 1 = 0 :=
    (congrArg (Value.get 1) (preserveCall 22 (by decide) (by decide))).trans df
  obtain ⟨out, fill, tag, outSp, preserveFill, fillFrame, zero⟩ :=
    Hash.Mark.zeroFill Common.fnCode_subset_programImage spReg count byte dstReg argsDf fillWin
      retRead (by decide) retWord retApart
  rw [remNat] at fillFrame zero
  have fillWithin : RegionsWithin [ParseSignature.buffer dst rem] padding := by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_, ?_⟩
    · change (sp-8).toNat ≤ dst.toNat
      omega
    · change dst.toNat + rem ≤ (sp-8).toNat + 80
      omega
  have paddedFrame := pushFrame.trans fillFrame fillWithin
  have writes := copyFrame.trans paddedFrame padWithin
  have readable : Readable out.store (sp+8) 64 :=
    (window.of_frame writes).readable.sub (by omega) (by omega)
  have bytes := Hash.Mark.buffer_after_fill msg room buffer.bytes fillFrame readable zero
  have hashCopied : Hash.Compression.StateAt (copied m sp) (sp+72)
      (Hash.compressBlocks Hash.initialHash msg) := by
    refine ⟨buffer.state.1, fun i hi => ?_⟩
    have h := Hash.Mark.copied_load m sp (64 + 4*i) 32 (by omega)
    have addr (off : Nat) : sp + BitVec.ofNat 64 (off + (64 + 4*i)) =
        sp + BitVec.ofNat 64 (off + 64) + BitVec.ofNat 64 (4*i) := by
      rw [← Nat.add_assoc, BitVec.ofNat_add, ← BitVec.add_assoc]
    rw [addr 8, addr 248] at h
    exact h.trans (buffer.state.2 i hi)
  have hashFinal := stateOutside hashCopied paddedFrame (by omega) (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inl (by change (sp-8).toNat + 80 ≤ sp.toNat + 72; omega))
  have ops := buffer.operands.afterHashWrites call writes (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    change (stackPtr initial).toNat - 880 + 696 ≤ sp.toNat + 352
    omega)
  have remOut : out.values[14].get 64 = BitVec.ofNat 64 rem :=
    congrArg (Value.get 64) ((preserveFill 14 (by decide) (by decide)).trans remReg)
  obtain ⟨b, branch, preserveBranch⟩ := paddingBranch out.values out.store msg.size remOut
  have keep (i : Fin Reg.count) (hi : i.val ∈ [5,12,13,22,39,50,51]) : b[i] = a[i] := by
    have branchMem : i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    have fillMem : i.val ∈ [3,5,9,10,11,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    have callMem : i.val ∈ [5,9,10,11,12,13,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    exact (preserveBranch i branchMem).trans ((preserveFill i.val fillMem i.isLt).trans
      (preserveCall i.val callMem i.isLt))
  have resumePath : Core.Reaches .l103170 a m .l1031c3 out.values out.store := by
    refine .step (congrArg (Transfer.next _ []) enter) ?_
    have filled : program.Exec (dialect Extracted.programImage)
        ⟨⟨.l12a700, args, pushed m sp n⟩, []⟩ out :=
      .done (congrArg (Transfer.next _ []) fill)
    exact ParseSignature.exec_reaches_resume filled resume [] (by rw [tag]; rfl)
  have branchPath : Core.Reaches .l1031c3 out.values out.store
      (if msg.size % 64 < 56 then .l103289 else .l1031cd) b out.store := by
    by_cases short : msg.size % 64 < 56
    · simp only [short, ite_true] at branch ⊢
      exact .step (congrArg (Transfer.next _ []) branch) (.refl _)
    · simp only [short, ite_false] at branch ⊢
      exact .step (congrArg (Transfer.next _ []) branch) (.refl _)
  exact ⟨b, out.store, resumePath.trans branchPath,
    ⟨⟨Hash.Update.advance call buffer.memory writes, (preserveBranch 4 (by decide)).trans outSp,
      (keep 5 (by decide)).trans buffer.rbp, (keep 13 (by decide)).trans buffer.r13,
      (keep 22 (by decide)).trans buffer.df,
      (congrArg Value.width (keep 12 (by decide))).trans buffer.r12Width,
      (congrArg Value.width (keep 39 (by decide))).trans buffer.mxcsr,
      (congrArg Value.width (keep 50 (by decide))).trans buffer.ftw,
      (congrArg Value.width (keep 51 (by decide))).trans buffer.fcw⟩,
      ops, hashFinal,
      (preserveBranch 3 (by decide)).trans ((preserveFill 3 (by decide) (by decide)).trans hashReg),
      congrArg Value.width ((preserveBranch 14 (by decide)).trans
        ((preserveFill 14 (by decide) (by decide)).trans remReg)),
      (preserveBranch 15 (by decide)).trans ((preserveFill 15 (by decide) (by decide)).trans lenReg)⟩,
    bytes⟩

end K256.Proofs.Verify.Wrapper.HashFinalize
