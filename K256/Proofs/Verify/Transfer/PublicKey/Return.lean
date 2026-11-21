import K256.Proofs.Verify.Transfer.PublicKey.Packing
import K256.Proofs.Ecdh.Decode.Affine.Selection
import K256.Proofs.Sec1.Parser.Result.AfterAffine
import K256.Proofs.Sec1.Parser.Frame.Return
import K256.Proofs.Sec1.LIR.Fn106390.Frame
import K256.Proofs.Ecdh.Decode.Repr
import K256.Proofs.ParseSignature.Contract
import K256.Spec.Secp256k1

namespace K256.Proofs.Verify.Transfer.PublicKey

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR Standards.SECG.ECC

open Sec1.Parser

private theorem stepGuard {p : Prop} [Decidable p] {t : Transfer Value Ram Label signature Reg.count}
    {o : Outcome Value Ram Label signature Reg.count}
    (h : (if p then t else .stuck).next (dialect Extracted.programImage) [] = o)
    (live : o ≠ .stuck) : t.next (dialect Extracted.programImage) [] = o := by
  split at h
  · exact h
  · exact (live h.symm).elim

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem returnWidths {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : program.Exec (dialect Extracted.programImage) ⟨⟨.l106565,a,m⟩,[]⟩ out)
    (widths : ParseSignature.ArgumentWidths a) : ParseSignature.ArgumentWidths out.values := by
  cases run with
  | done h =>
    change (program.runBlock _ ⟨.l106565,a,m⟩).next _ [] = .done out at h
    cfg_eval [b_l106565] at h
    repeat' replace h := stepGuard h (by intro impossible; cases impossible)
    simp only [Transfer.next, Outcome.done.injEq] at h
    subst out
    intro ⟨i, bound⟩ hi
    have w := widths ⟨i, bound⟩ hi
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact w
  | next h _ =>
    change (program.runBlock _ ⟨.l106565,a,m⟩).next _ [] = .next _ at h
    cfg_eval [b_l106565] at h
    repeat' replace h := stepGuard h (by intro impossible; cases impossible)
    simp only [Transfer.next, reduceCtorEq] at h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem copyWidths {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : program.Exec (dialect Extracted.programImage) ⟨⟨.l106548,a,m⟩,[]⟩ out)
    (widths : Ecdh.Decode.Affine.CallerWidths a) : ParseSignature.ArgumentWidths out.values := by
  cases run with
  | done h =>
    change (program.runBlock _ ⟨.l106548,a,m⟩).next _ [] = .done out at h
    cfg_eval [b_l106548] at h
    repeat' replace h := stepGuard h (by intro impossible; cases impossible)
    simp only [Transfer.next, reduceCtorEq] at h
  | next h tail =>
    change (program.runBlock _ ⟨.l106548,a,m⟩).next _ [] = .next _ at h
    cfg_eval [b_l106548] at h
    repeat' replace h := stepGuard h (by intro impossible; cases impossible)
    simp only [Transfer.next, Outcome.next.injEq] at h
    cases h
    apply returnWidths tail
    intro ⟨i, bound⟩ hi
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · exact widths 2 (by decide)
    · rfl
    · exact widths 8 (by decide)
    · exact widths 9 (by decide)

private theorem jumpGuard {p : Prop} [Decidable p]
    {t : Transfer Value Ram Label signature Reg.count} {dest : Location Value Ram Label signature}
    (h : (if p then t else .stuck) = .jump dest) : t = .jump dest := by
  split at h <;> first | exact h | contradiction

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem stageWidths {a b : Values Value Reg.count} {m n : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨.l1064f4,a,m⟩ =
      .jump ⟨.l106518,b,n⟩) (widths : Ecdh.Decode.Affine.CallerWidths a) :
    Ecdh.Decode.Affine.CallerWidths b := by
  cfg_eval [b_l1064f4] at step
  repeat' replace step := jumpGuard step
  split at step <;> injection step with eq <;> cases eq
  intro ⟨i, bound⟩ hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · rfl
  · exact widths 8 (by decide)
  · exact widths 9 (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem selectWidths {a b : Values Value Reg.count} {m n : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨.l106518,a,m⟩ =
      .jump ⟨.l106548,b,n⟩) (widths : Ecdh.Decode.Affine.CallerWidths a) :
    Ecdh.Decode.Affine.CallerWidths b := by
  cfg_eval [b_l106518] at step
  repeat' replace step := jumpGuard step
  split at step <;> split at step <;> injection step with eq <;> cases eq
  all_goals
    intro ⟨i, bound⟩ hi
    have w := widths ⟨i, bound⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> exact w

private theorem acceptedWidths {m : Ram} {c : Values Value Reg.count} {sp dst : BitVec 64}
    {out : Output Value Ram Reg.count}
    (stack : Writable Extracted.programImage m sp 249)
    (rsp : c[4].get 64 = sp) (bx : c[3].get 64 = sp + 160)
    (r12 : (c[12].get 64).setWidth 8 = 0) (r15 : c[15].get 64 = dst)
    (df : c[22].get 1 = 0) (tag : memLoad m (sp + 4) 8 = 4)
    (flag : memLoad m (sp + 248) 8 = 1) (widths : Ecdh.Decode.Affine.CallerWidths c)
    (run : program.Exec (dialect Extracted.programImage) ⟨⟨.l1064f4,c,m⟩,[]⟩ out) :
    ParseSignature.ArgumentWidths out.values := by
  let staged := memCopy m (sp + 72) (sp + 160) 88
  have stack' : Writable Extracted.programImage staged sp 249 := stack.memStore _ _
  have stageWrite : StoreOk Extracted.programImage m (sp + 72) 88 0x106501 3 :=
    ParseSignature.storeOk_of_codeRange (off := 13) (stack.of_offsets rfl (addr_self _) (by decide))
      (fun x hx => Common.fnCode_subset_programImage x (code_l1064f4 x hx)) (by decide)
  have stageRead : Readable m (sp + 160) 88 :=
    stack.readable.of_offsets rfl (addr_self _) (by decide)
  have stageApart : (sp + 72).toNat + 88 ≤ (sp + 160).toNat := by
    rw [toNat_of_offsets (a := sp + 72) rfl (addr_self _) stack.readable.low (n := 88) (by decide),
      toNat_of_offsets (a := sp + 160) rfl (addr_self _) stack.readable.low (n := 88) (by decide)]
    change sp.toNat + 72 + 88 ≤ sp.toNat + 160
    omega
  have stagedByte (off : BitVec 64) (sep : RangeApart (sp + 72) 88 (sp + off) 1) :
      memLoad staged (sp + off) 8 = memLoad m (sp + off) 8 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ sep
  obtain ⟨a, stage, arx, _, kept⟩ := Result.stage sp 4 rsp bx
    ⟨df, stageRead.low, stageWrite.low, stageRead.present, stageWrite.present, .inr stageApart,
      stageWrite.tables, stageWrite.apart, stageWrite.notCode⟩
    (LoadOk.of_offsets stack'.readable rfl (addr_self _) (by decide))
    ((stagedByte 4 (RangeApart.of_offsets rfl rfl (by decide))).trans tag)
  simp only [show 2 ≤ (4 : BitVec 8).toNat ∧ (4 : BitVec 8).toNat < 6 by decide] at stage
  have writeFlag : StoreOk Extracted.programImage staged (sp + 160) 1 0x10652c 7 :=
    ParseSignature.storeOk_of_codeRange (off := 20) (stack'.of_offsets rfl (addr_self _) (by decide))
      (fun x hx => Common.fnCode_subset_programImage x (code_l106518 x hx)) (by decide)
  have stack'' : Writable Extracted.programImage (memStore staged (sp + 160) (Result.selectedByte 4 1 0)) sp 249 :=
    stack'.memStore _ _
  obtain ⟨b, select, _, _⟩ := Result.select (args := a) (mem := staged) sp dst 4 1 0
    ((congrArg (Value.get 64) (kept.reg 4 (by decide))).trans rsp)
    ((congrArg (Value.get 64) (kept.reg 15 (by decide))).trans r15)
    (by rw [arx]; rfl)
    ((congrArg (fun v : Value => (v.get 64).setWidth 8) (kept.reg 12 (by decide))).trans r12)
    (LoadOk.of_offsets stack'.readable rfl (addr_self _) (by decide))
    ((stagedByte 248 (RangeApart.of_offsets rfl rfl (by decide))).trans flag)
    writeFlag (LoadOk.of_offsets stack''.readable rfl (addr_self _) (by decide))
  simp only [show Result.selectedByte 4 1 0 ≠ 0 by decide, ↓reduceIte] at select
  apply copyWidths (Ecdh.Decode.Affine.afterJump (Ecdh.Decode.Affine.afterJump run stage) select)
  exact selectWidths select (stageWidths stage widths)

theorem finish (fr : Activation) {m : Ram} {c : Values Value Reg.count} {p : Curve.Point}
    (frame : RamWriteFrame fr.original m [fr.region])
    (stack : Writable Extracted.programImage fr.original (fr.rsp-1544) 1544)
    (room : fr.low.toNat+1544 ≤ fr.rsp.toNat) (slot : Readable fr.original fr.rsp 8)
    (retLow : fr.ret.toNat < 2^32) (slots : saved fr m)
    (dst : Writable Extracted.programImage fr.original fr.rdi 96) (above : fr.rsp.toNat+8 ≤ fr.rdi.toNat)
    (rsp : c[4] = ⟨64,fr.rsp-344⟩) (bx : c[3] = ⟨64,fr.rsp-344+160⟩)
    (r12 : c[12] = ⟨64,0⟩) (r15 : c[15] = ⟨64,fr.rdi⟩) (df : c[22] = ⟨1,0⟩)
    (kept : ∀ i : Fin Reg.count, i.val ∈ [5,13,39,50,51] → c[i] = fr.entryValue i.val)
    (widths : Ecdh.Decode.Affine.CallerWidths c)
    (tag : memLoad m (fr.rsp-344+4) 8 = 4) (flag : memLoad m (fr.rsp-344+160+88) 8 = 1)
    (pt : Ecdh.Decode.AffinePointAt m (fr.rsp-344+160) p) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1064f4,c,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn106390.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,96⟩] ∧
      ParseSignature.ArgumentWidths out.values ∧ memLoad out.store fr.rdi 64 = 0 ∧
      Ecdh.Decode.AffinePointAt out.store (fr.rdi+8) p := by
  let sp := fr.rsp - 344
  let outRegion : MemoryRegion := ⟨fr.rdi.toNat, 96⟩
  let scratchRegion : MemoryRegion := ⟨fr.rsp.toNat - 272, 89⟩
  let n := Result.resultStore m sp fr.rdi 1
  have spOffset (off : BitVec 64) (h : off.toNat ≤ 1544) :
      (fr.rsp - off).toNat = fr.rsp.toNat - off.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have slotBound := slot.low
  have dstBound := dst.readable.low
  have dstPayloadNat : (fr.rdi+8).toNat = fr.rdi.toNat+8 :=
    toNat_of_offsets rfl (addr_self fr.rdi) dstBound (n := 88) (by decide)
  have spStageNat : (sp+72).toNat = fr.rsp.toNat-272 := by
    rw [show sp+72 = fr.rsp-272 by dsimp only [sp]; bv_omega]
    exact spOffset 272 (by decide)
  have spFlagNat : (sp+160).toNat = fr.rsp.toNat-184 := by
    rw [show sp+160 = fr.rsp-184 by dsimp only [sp]; bv_omega]
    exact spOffset 184 (by decide)
  have stackWindow : Writable Extracted.programImage m sp 249 :=
    (stack.of_offsets (addr_sub fr.rsp 344) (addr_sub fr.rsp 1544) (by decide)).of_frame frame
  have outputWindow : Writable Extracted.programImage m (fr.rdi+8) 88 :=
    (dst.of_offsets rfl (addr_self _) (by decide)).of_frame frame
  have apartCopy : (sp + 72).toNat + 88 ≤ (fr.rdi + 8).toNat := by
    rw [spStageNat, dstPayloadNat]
    omega
  have tagFlag : memLoad m (sp+248) 8 = 1 := by
    rw [show sp+248 = sp+160+88 by bv_omega]
    exact flag
  have selected : Result.selectedByte 4 1 0 = 1 := by decide
  obtain ⟨b, reached, bdi, preserved, bax⟩ :=
    Result.afterAffine Common.fnCode_subset_programImage sp fr.rdi 4 1 0
      (congrArg (Value.get 64) rsp) (congrArg (Value.get 64) bx) (congrArg (Value.get 64) r15)
      (congrArg (fun v : Value => (v.get 64).setWidth 8) r12) (congrArg (Value.get 1) df)
      (by decide) tag tagFlag stackWindow outputWindow (.inl apartCopy)
  have nonzero : (1 : BitVec 8) ≠ 0 := by decide
  simp only [selected, nonzero, ↓reduceIte] at reached
  rw [selected] at bax
  change Reaches Extracted.programImage .l1064f4 c m .l106565 b n at reached
  have localFrame : RamWriteFrame m n [scratchRegion, outRegion] :=
    Result.resultStore_frame m sp fr.rdi 1
      ⟨scratchRegion, List.mem_cons_self,
        by simp only [InRegion, scratchRegion, spStageNat]; omega⟩
      ⟨scratchRegion, List.mem_cons_self,
        by simp only [InRegion, scratchRegion, spFlagNat]; omega⟩
      (fun _ => ⟨outRegion, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        by simp only [InRegion, outRegion, dstPayloadNat]; omega⟩)
  have saves (off : BitVec 64) (hoff : off.toNat ≤ 32) :
      memLoad n (fr.rsp-off) 64 = memLoad m (fr.rsp-off) 64 := by
    apply localFrame.memLoad_eq
    simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, scratchRegion, outRegion]
    rw [spOffset off (by omega)]
    refine ⟨by omega, ?_⟩
    rintro _ (rfl | rfl)
    · exact .inr (by dsimp only; omega)
    · exact .inl (by dsimp only; omega)
  have retLoad : memLoad n fr.rsp 64 = fr.ret := by
    have h := saves 0 (by decide)
    rw [show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega] at h
    exact h.trans slots.2.2.2.2
  have savedNat : (fr.rsp-32).toNat = fr.rsp.toNat-32 := spOffset 32 (by decide)
  have readSaved : Readable n (fr.rsp-32) 40 := by
    have saveSlots : Readable fr.original (fr.rsp - 32) 32 :=
      stack.readable.of_offsets (addr_sub fr.rsp 32) (addr_sub fr.rsp 1544) (by decide)
    have below := (saveSlots.of_frame frame).of_frame localFrame
    refine ⟨by rw [savedNat]; omega, fun i hi => ?_⟩
    by_cases h : i < 32
    · exact below.present i h
    · rw [show i = 32 + (i - 32) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
        show fr.rsp - 32 + (32#64) = fr.rsp by bv_omega]
      exact (slot.of_frame frame |>.of_frame localFrame).present _ (by omega)
  have apartReturn : RangeApart fr.rdi 8 (fr.rsp-32) 40 := by
    apply RangeApart.of_toNat <;> (try rw [savedNat]) <;> omega
  obtain ⟨out, block, store, retTag, _, outSp, outBx, outR12, outR14, outR15, outKeep⟩ :=
    Frame.returnBlock (sp := fr.rsp) (dst := fr.rdi) (status := 0)
      ((congrArg (Value.get 64) (preserved.reg 4 (by decide))).trans (congrArg (Value.get 64) rsp))
      (congrArg (Value.get 64) bdi) (congrArg (Value.get 64) (bax nonzero))
      ((dst.sub (a := fr.rdi) (n := 8) (by omega) (by omega)).of_frame frame |>.of_frame localFrame)
      (fun x hx => Common.fnCode_subset_programImage x (code_l106565 x hx))
      readSaved apartReturn retLoad retLow
  have run : program.Exec (dialect Extracted.programImage) ⟨⟨.l1064f4,c,m⟩,[]⟩ out :=
    Program.Exec.of_sem (reached.exec (.ret (congrArg (Transfer.next _ []) block)))
  have restored (i : Fin Reg.count) (hi : i.val ∈ [5,13,39,50,51]) :
      out.values[i] = fr.entryValue i.val :=
    (outKeep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
      ((preserved.reg i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
        (kept i hi))
  have initialFrame : RamWriteFrame fr.original m [fr.region, outRegion] := by
    refine ⟨fun x hx => frame.outside x ⟨hx.1, ?_⟩, frame.present⟩
    intro r hr
    exact hx.2 r (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)))
  have wholeFrame : RamWriteFrame fr.original n [fr.region, outRegion] := by
    apply initialFrame.trans localFrame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨fr.region, List.mem_cons_self, by simp only [Activation.region, scratchRegion]; omega⟩
    · exact ⟨outRegion, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨out, run, retTag, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fn106390.doneAt, Atom.All, Atom.Holds]
    refine ⟨outSp, ?_, ?_, restored 5 (by decide), ?_, restored 13 (by decide), ?_, ?_,
      restored 39 (by decide), restored 50 (by decide), restored 51 (by decide), trivial⟩
    · exact (outKeep 22 (by decide)).trans ((preserved.reg 22 (by decide)).trans df)
    · exact outBx.trans (congrArg (Value.mk 64) ((saves 32 (by decide)).trans slots.1))
    · exact outR12.trans (congrArg (Value.mk 64) ((saves 24 (by decide)).trans slots.2.1))
    · exact outR14.trans (congrArg (Value.mk 64) ((saves 16 (by decide)).trans slots.2.2.1))
    · exact outR15.trans (congrArg (Value.mk 64) ((saves 8 (by decide)).trans slots.2.2.2.1))
  · rw [store]
    apply wholeFrame.memStore
    exact ⟨outRegion, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      by simp only [outRegion, InRegion]; omega⟩
  · exact acceptedWidths stackWindow (congrArg (Value.get 64) rsp) (congrArg (Value.get 64) bx)
      (congrArg (fun v : Value => (v.get 64).setWidth 8) r12) (congrArg (Value.get 64) r15)
      (congrArg (Value.get 1) df) tag tagFlag widths run
  · rw [store]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · apply pt.of_copy
    intro off width inside
    rw [store, memLoad_memStore_of_rangeApart]
    · exact Result.resultStore_load nonzero off width inside
    · exact RangeApart.right_sub (RangeApart.of_offsets (addr_self fr.rdi) rfl (by decide) :
        RangeApart fr.rdi 8 (fr.rdi + 8) 88) inside

end K256.Proofs.Verify.Transfer.PublicKey
