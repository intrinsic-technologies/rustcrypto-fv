import K256.Proofs.Signing.Hash.Memory
import K256.Proofs.Signing.Hash.Mark.Call
import K256.Proofs.Signing.Hash.Mark.Buffer
import K256.Proofs.Verify.Wrapper.HashFinalize.Mark

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash (compressBlocks initialHash)

open K256.Proofs.Verify.Hash.Compression (StateAt)
open Mark (copied marked pushed resume)
open Verify.Hash.FinalBlocks (stateOutside)

set_option maxHeartbeats 600000 in
theorem mark {a : Values Value Reg.count} {m : Ram} {sp : BitVec 64} {message : ByteArray}
    (rsp : a[4] = ⟨64, sp⟩) (direction : a[22] = ⟨1, 0⟩)
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (stack : Writable Extracted.programImage m (sp - 512) 1672)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32)
    (ready : Buffer sp message a m) :
    ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l1055bf, a, m⟩, []⟩ ⟨⟨markTarget message, b, t⟩, []⟩ ∧
      Frame sp a b m t ∧ Padding sp message b t := by
  let n := message.size % 64
  let dst := sp + 9 + BitVec.ofNat 64 n
  let rem := 63 - n
  let padding : List MemoryRegion := [⟨(sp-8).toNat,80⟩]
  have dep : 8 ≤ sp.toNat := by omega
  have room : sp.toNat + 592 ≤ 2^32 := by omega
  have nBound : n < 64 := Nat.mod_lt _ (by decide)
  have slotNat : (sp-8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp from dep)
  have atNat (off : Nat) (bound : off ≤ 592) :
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
  have sourceNat : (sp+488).toNat = sp.toNat + 488 := atNat 488 (by decide)
  have posNat : (sp+71).toNat = sp.toNat + 71 := atNat 71 (by decide)
  have countNat : (sp+104).toNat = sp.toNat + 104 := atNat 104 (by decide)
  have bottom : (sp - 512).toNat = sp.toNat - 512 :=
    BitVec.toNat_sub_of_le (show (512 : BitVec 64) ≤ sp from depth)
  have window : Writable Extracted.programImage m (sp-8) 600 :=
    stack.sub (by omega) (by omega)
  have slotIn (ptr : BitVec 64) (len : Nat)
      (lo : (sp-8).toNat ≤ ptr.toNat) (hi : ptr.toNat + len ≤ (sp-8).toNat + 80) :
      InRegions padding ptr len :=
    ⟨_, List.mem_cons_self, lo, hi, by omega⟩
  have copyFrame : RamWriteFrame m (copied m sp) (regions sp) :=
    Sec1.Wrapper.Copy.memCopy_frame (.refl _ _) (by
      exact ⟨_, List.mem_cons_self, by change sp.toNat - 512 ≤ _; omega,
        by change _ ≤ sp.toNat - 512 + 624; omega, by omega⟩)
  have markFrame : RamWriteFrame (copied m sp) (marked m sp n) padding :=
    (RamWriteFrame.refl _ _).memStore _ (slotIn _ 1 (by omega) (by omega))
  have pushFrame : RamWriteFrame (copied m sp) (pushed m sp n) padding :=
    markFrame.memStore _ (slotIn _ 8 (by omega) (by omega))
  have padWithin : RegionsWithin padding (regions sp) := by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_, ?_⟩
    · change sp.toNat - 512 ≤ (sp-8).toNat
      omega
    · change (sp-8).toNat + 80 ≤ sp.toNat - 512 + 624
      omega
  have included x hx := Common.fnCode_subset_programImage x (code_l1055bf x hx)
  have copyGuard : RepMovsOk Extracted.programImage m 0 (sp+488) (sp+8) 13 8 0x1055d1 3 := by
    have source : Readable m (sp+488) 104 := window.readable.sub (by omega) (by omega)
    have destination : Writable Extracted.programImage m (sp+8) 104 :=
      window.sub (by omega) (by omega)
    exact Generate.Generator.Multiply.Prepare.copyGuard source
      (ParseSignature.storeOk_of_codeRange (off := 18) destination included (by decide))
      (Or.inr (by change (sp+8).toNat + 104 ≤ (sp+488).toNat; omega))
  have copiedWin := window.of_frame copyFrame
  have markedWin := copiedWin.of_frame markFrame
  have markGuard : StoreOk Extracted.programImage (copied m sp)
      (sp+8+BitVec.ofNat 64 n) 1 0x1055e6 6 :=
    ParseSignature.storeOk_of_codeRange (off := 39) (copiedWin.sub (by omega) (by omega))
      included (by decide)
  have pushGuard : StoreOk Extracted.programImage (marked m sp n) (sp-8) 8 0x10560c 6 :=
    ParseSignature.storeOk_of_codeRange (off := 77) (markedWin.sub (by omega) (by omega))
      included (by decide)
  have markedImage := imageAfter depth stack (copyFrame.trans markFrame padWithin) image
  obtain ⟨gotRead, gotTarget⟩ := Verify.LIR.Fn106390.callSlots_loaded
    (sections := Extracted.programSections) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    markedImage (0x203e10, 0x12a700) (by decide)
  have df : a[22].get 1 = 0 := congrArg (Value.get 1) direction
  obtain ⟨args, enter, count, hashReg, spReg, byte, dstReg, remReg, lenReg, preserveCall⟩ :=
    Mark.call (sp := sp) message.size (congrArg (Value.get 64) rsp) df copyGuard
      (LoadOk.of_region copiedWin.readable (by omega) (by omega))
      (LoadOk.of_region copiedWin.readable (by omega) (by omega))
      ready.len ready.blocks markGuard pushGuard ⟨gotRead.low, gotRead.present⟩ gotTarget
  have remNat : (BitVec.ofNat 64 rem).toNat = rem := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have pushedWin := copiedWin.of_frame pushFrame
  have retWord : memLoad (pushed m sp n) (sp-8) 64 = 0x105612 :=
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
    Verify.Hash.Mark.zeroFill Common.fnCode_subset_programImage spReg count byte dstReg argsDf fillWin
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
  have bytes := Mark.buffer_after_fill message room ready.bytes fillFrame readable zero
  have hashCopied : StateAt (copied m sp) (sp+72)
      (compressBlocks initialHash message) := by
    refine ⟨ready.state.1, fun i hi => ?_⟩
    have h := Mark.copied_load m sp (64 + 4*i) 32 (by omega)
    have addr (off : Nat) : sp + BitVec.ofNat 64 (off + (64 + 4*i)) =
        sp + BitVec.ofNat 64 (off + 64) + BitVec.ofNat 64 (4*i) := by
      rw [← Nat.add_assoc, BitVec.ofNat_add, ← BitVec.add_assoc]
    rw [addr 8, addr 488] at h
    exact h.trans (ready.state.2 i hi)
  have hashFinal := stateOutside hashCopied paddedFrame (by omega) (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inl (by change (sp-8).toNat + 80 ≤ sp.toNat + 72; omega))
  have remOut : out.values[14].get 64 = BitVec.ofNat 64 rem :=
    congrArg (Value.get 64) ((preserveFill 14 (by decide) (by decide)).trans remReg)
  obtain ⟨b, branch, preserveBranch⟩ := Mark.paddingBranch out.values out.store message.size remOut
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
  have resumePath : Verify.Core.Reaches .l1055bf a m .l105612 out.values out.store := by
    refine .step (congrArg (Transfer.next _ []) enter) ?_
    have filled : program.Exec (dialect Extracted.programImage)
        ⟨⟨.l12a700, args, pushed m sp n⟩, []⟩ out :=
      .done (congrArg (Transfer.next _ []) fill)
    exact ParseSignature.exec_reaches_resume filled resume [] (by rw [tag]; rfl)
  have branchPath : Verify.Core.Reaches .l105612 out.values out.store
      (if message.size % 64 < 56 then .l1056d8 else .l10561c) b out.store := by
    by_cases short : message.size % 64 < 56
    · simp only [short, ite_true] at branch ⊢
      exact .step (congrArg (Transfer.next _ []) branch) (.refl _)
    · simp only [short, ite_false] at branch ⊢
      exact .step (congrArg (Transfer.next _ []) branch) (.refl _)
  have same14 := (preserveBranch 14 (by decide)).trans
    ((preserveFill 14 (by decide) (by decide)).trans remReg)
  refine ⟨b, out.store, resumePath.trans branchPath,
    ⟨(preserveBranch 4 (by decide)).trans outSp, (keep 22 (by decide)).trans direction,
      fun i hi => keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega),
      writes⟩, ⟨?_, hashFinal,
      (preserveBranch 3 (by decide)).trans ((preserveFill 3 (by decide) (by decide)).trans hashReg),
      (preserveBranch 15 (by decide)).trans ((preserveFill 15 (by decide) (by decide)).trans lenReg),
      bytes⟩⟩
  intro i hi
  by_cases last : i.val = 14
  · have eq : i = 14 := Fin.ext last
    subst i
    exact congrArg Value.width same14
  · have small : i.val ∈ [5,12,13] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    exact (congrArg Value.width (keep i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at small ⊢; omega))).trans (ready.widths i small)

end K256.Proofs.Signing.Hash
