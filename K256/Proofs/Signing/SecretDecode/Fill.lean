import K256.Proofs.Signing.SecretDecode.State
import K256.Proofs.Verify.Core.Affine.Call
import K256.Proofs.ParseSignature.Fill
import K256.Proofs.Verify.Transfer.Signature.Relabel
import K256.Proofs.Verify.LIR.Fn127d70.Frame
import K256.Proofs.Common.Tactic
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.SecretDecode

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters

private def fillChild (fr : Activation) (m : Ram) : Activation :=
  { fr with
    original := m, rsp := fr.rsp - 128, ret := 0x106e2d,
    rbx := fr.rdi, rdi := fr.rsi, rsi := 32, rcx := 4, rdx := fr.rsp - 80, r8 := 256 }

private def resumeFill : StackFrame Value Label signature Reg.count :=
  ⟨.l106e2d, #v[], rfl, some ⟨64, 0x106e2d⟩⟩

set_option maxRecDepth 3000 in
private theorem setupFill {fr : Activation} {a : Verify.Core.Registers}
    (entry : Atom.All Extracted.programImage a fr.original (Fn106dd0.frameAt .l106dd0 fr))
    (room : 336 ≤ fr.rsp.toNat) (high : fr.rsp.toNat + 80 < 2^32) :
    ∃ b m, program.runBlock (dialect Extracted.programImage) ⟨.l106dd0, a, fr.original⟩ =
      .call ⟨.l127d70, b, m⟩ resumeFill ∧
      Atom.All Extracted.programImage b m ((Fn127d70.frameAt .l127d70 (fillChild fr m)).take 17) ∧
      RamWriteFrame fr.original m [⟨(fr.rsp - 128).toNat, 128⟩] ∧
      memLoad m (fr.rsp - 128) 64 = 0x106e2d ∧
      ∀ d r, (d, r) ∈ ([(48, 3), (40, 12), (32, 13), (24, 14), (16, 15), (8, 5)] : List (Nat × Nat)) →
        memLoad m (fr.rsp - BitVec.ofNat 64 d) 64 = fr.entryReg r := by
  simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.All, Atom.Holds] at entry
  obtain ⟨sp, df, _, _, bx, bp, si, di, _, r9, r12, r13, r14, r15, mx, ft, fc, _, _, _, stack, _⟩ := entry
  have spVal : a[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have bxVal : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have bpVal : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have siVal : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have diVal : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have r12Val : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have r13Val : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have r14Val : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have r15Val : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  cases fr
  dsimp only at *
  refine ⟨?_, ?_, ?run, ?atoms, ?frame, ?ret, ?saved⟩
  case run =>
    cfg_eval
    simp only [spVal, bxVal, bpVal, siVal, diVal, r12Val, r13Val, r14Val, r15Val]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l106dd0 x hx)))
    rfl
  case atoms =>
    simp only [Fn127d70.frameAt, Fn127d70.frameAtG28, List.take_succ_cons, List.take_zero,
      Atom.All, Atom.Holds, fillChild]
    exact ⟨rfl, df, rfl, rfl, rfl, bp, rfl, rfl, rfl, r9, r12, r13, r14, r15, mx, ft, fc, trivial⟩
  case frame => slot_state region
  case ret => exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  case saved =>
    intro d r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      segment_words [] <;> rfl

private theorem fillBranch {mem : Ram} {a : Verify.Core.Registers} (status : a[0].get 8 = 255) (widths : ParseSignature.ArgumentWidths a) :
    ∃ b : Verify.Core.Registers, Verify.Core.Reaches .l106e2d a mem .l106e35 b mem ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 4, 5, 12, 13, 14, 15, 22, 39, 50, 51] → b[i] = a[i]) ∧
      ParseSignature.ArgumentWidths b := by
  have low : (a[0].get 64).setWidth 8 = 255 := by
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using status
  refine ⟨?next, .single ?step, ?regs, ?w⟩
  case step =>
    change (program.runBlock _ _).next _ [] = _
    cfg_eval [low, cmpSpec_ZF]
    rfl
  case regs =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case w =>
    intro ⟨i, hi⟩ h
    have hw := widths ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

local macro "fill_bounds" : tactic => `(tactic|
  (simp only [fillChild, Activation.region, ParseSignature.buffer, ParseSignature.callStack,
     BitVec.toNat_sub, BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow] at *
   omega))

theorem fillPath {fr : Activation} {a : Verify.Core.Registers}
    (entry : Atom.All Extracted.programImage a fr.original (Fn106dd0.frameAt .l106dd0 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (low : fr.low = fr.rsp - 336) (room : 336 ≤ fr.rsp.toNat)
    (high : fr.rsp.toNat + 80 < 2^32)
    (source : Readable fr.original fr.rsi 32)
    (limit : fr.rsi.toNat + 32 < 2^32)
    (apart : fr.rsi.toNat + 32 ≤ fr.rsp.toNat - 336 ∨ fr.rsp.toNat + 80 ≤ fr.rsi.toNat) :
    ∃ b m, Verify.Core.Reaches .l106dd0 a fr.original .l106e35 b m ∧ Frame .l106e35 fr b m ∧
      ParseSignature.scalarLimbsAt m (fr.rsp - 80) fr.original fr.rsi := by
  have _ := image
  obtain ⟨c, n, call, registers, setup, ret, saved⟩ := setupFill entry room high
  simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.All, Atom.Holds] at entry
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, retRead, retValue, retLow, stack, space, align,
    read1, val1, read2, val2, read3, val3, separate, _⟩ := entry
  let child := fillChild fr n
  have bottom : fr.low.toNat = fr.rsp.toNat - 336 := by
    rw [low, BitVec.toNat_sub_of_le room]
    rfl
  have got {ptr : BitVec 64} (lo : 0x203dd0 ≤ ptr.toNat) (hi : ptr.toNat + 8 ≤ 0x203e28) :
      Outside [⟨(fr.rsp - 128).toNat, 128⟩] ptr 8 := by
    simp only [Outside, List.mem_singleton, forall_eq]
    fill_bounds
  have stack' := stack.of_frame setup
  have childEntry : Atom.All Extracted.programImage c n (Fn127d70.frameAt .l127d70 child) := by
    let atoms := Fn127d70.frameAt .l127d70 child
    change Atom.All _ _ _ atoms
    rw [← List.take_append_drop 17 atoms, Atom.all_append]
    refine ⟨registers, ?_⟩
    change Readable n (fr.rsp - 128) 8 ∧ _
    refine ⟨stack'.readable.sub (by fill_bounds) (by fill_bounds), ret, by change (0x106e2d#64).toNat < 2^32; decide,
      ?_, ?_, ?_, read1.of_frame setup, (setup.memLoad_eq (got (by decide) (by decide))).trans val1,
      read2.of_frame setup, (setup.memLoad_eq (got (by decide) (by decide))).trans val2,
      read3.of_frame setup, (setup.memLoad_eq (got (by decide) (by decide))).trans val3,
      ?_, trivial⟩
    · change Writable _ n (fr.rsp - 128 - 208) 208
      rw [BitVec.sub_sub]
      exact stack'.sub (Nat.le_refl _) (by change (fr.rsp - 336).toNat + 208 ≤ (fr.rsp - 336).toNat + 336; omega)
    · change fr.low.toNat + 208 ≤ (fr.rsp - 128).toNat
      fill_bounds
    · change (fr.rsp - 128).toNat % 16 = 8
      fill_bounds
    · change 0x203ef8 ≤ (fr.rsp - 128).toNat ∨ (fr.rsp - 128).toNat ≤ 0x203dd0
      fill_bounds
  have dst : Writable Extracted.programImage n (fr.rsp - 80) 32 :=
    stack'.sub (by fill_bounds) (by fill_bounds)
  have inSep : Outside [ParseSignature.callStack child] fr.rsi 32 := by
    simp only [Outside, List.mem_singleton, forall_eq, child]
    fill_bounds
  have outSep : Outside [ParseSignature.callStack child] (fr.rsp - 80) 32 := by
    simp only [Outside, List.mem_singleton, forall_eq, child]
    fill_bounds
  have ioSep : Outside [ParseSignature.buffer (fr.rsp - 80) 32] fr.rsi 32 := by
    simp only [Outside, List.mem_singleton, forall_eq]
    fill_bounds
  have slot : Outside [ParseSignature.buffer (fr.rsp - 80) 32] 0x203dd0 8 := by
    simp only [Outside, List.mem_singleton, forall_eq]
    fill_bounds
  obtain ⟨old, exec, tag, done_, writes, widths, status, limbs⟩ :=
    ParseSignature.fill_call Common.fnCode_subset_programImage child rfl rfl rfl
      (source.of_frame setup) dst inSep outSep ioSep slot c childEntry
  obtain ⟨out, run, mem, returned, regs⟩ :=
    Verify.Transfer.Signature.transferAt (y := .l127d70) (by decide +kernel) exec
  have called : Verify.Core.Reaches .l106dd0 a fr.original .l106e2d out.values out.store := by
    refine .step (b := ⟨⟨.l127d70, c, n⟩, [resumeFill]⟩) ?_ ?_
    · change program.step _ _ = _
      simp only [Program.step, call, Transfer.next]
    · exact ParseSignature.exec_reaches_resume run resumeFill [] (by rw [returned, tag]; rfl)
  have widths' : ParseSignature.ArgumentWidths out.values := by
    intro i hi
    rw [regs i (by simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)]
    exact widths i hi
  obtain ⟨b, branch, keep, widthsB⟩ := fillBranch (mem := out.store)
    ((congrArg (Value.get 8) (regs 0 (by decide))).trans status) widths'
  have kept (i : Fin Reg.count) (hi : i.val ∈ [3, 4, 5, 12, 13, 14, 15, 22, 39, 50, 51]) :
      b[i] = old.values[i] := (keep i hi).trans (regs i (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega))
  have doneB : Atom.All Extracted.programImage b out.store (Fn127d70.doneAt child) := by
    change Atom.All _ old.values old.store (Fn127d70.doneAt child) at done_
    simp only [Fn127d70.doneAt, Atom.All, Atom.Holds] at done_ ⊢
    simpa only [kept 4 (by decide), kept 22 (by decide), kept 3 (by decide), kept 5 (by decide),
      kept 12 (by decide), kept 13 (by decide), kept 14 (by decide), kept 15 (by decide),
      kept 39 (by decide), kept 50 (by decide), kept 51 (by decide)] using done_
  simp only [Fn127d70.doneAt, Atom.All, Atom.Holds, child, fillChild] at doneB
  obtain ⟨sp, df, bx, bp, r12, r13, r14, r15, mx, ft, fc, _⟩ := doneB
  rw [show fr.rsp - 128 + 8 = fr.rsp - 120 by bv_omega] at sp
  have childFrame : RamWriteFrame n out.store [child.region, ParseSignature.buffer (fr.rsp - 80) 32] :=
    mem ▸ writes
  have total : RamWriteFrame fr.original out.store [fr.region] := by
    refine ((RamWriteFrame.refl fr.original [fr.region]).trans setup ?_).trans childFrame ?_
    · intro reg hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, by fill_bounds⟩
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rcases hr with rfl | rfl <;> (try dsimp only [child]) <;> fill_bounds
  have savedOut (d r : Nat) (hd : (d, r) ∈ [(48, 3), (40, 12), (32, 13), (24, 14), (16, 15), (8, 5)]) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 d) 64 = fr.entryReg r := by
    refine (childFrame.memLoad_eq ?_).trans (saved d r hd)
    have small : d ≤ 48 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hd
      omega
    have dn : (BitVec.ofNat 64 d).toNat = d := Nat.mod_eq_of_lt (by omega)
    refine ⟨?_, fun reg hr => ?_⟩
    · fill_bounds
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (try dsimp only [child]) <;> fill_bounds
  refine ⟨b, out.store, called.trans branch, ⟨?_, total, widthsB⟩, ?_⟩
  · simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.All, Atom.Holds]
    refine ⟨sp, df, bx, bp, r12, r13, r14, r15, mx, ft, fc, savedOut 48 3 (by decide),
      savedOut 40 12 (by decide), savedOut 32 13 (by decide), savedOut 24 14 (by decide),
      savedOut 16 15 (by decide), savedOut 8 5 (by decide), retRead.of_frame total,
      (total.memLoad_eq ?_).trans retValue, retLow, stack.of_frame total, space, align, trivial⟩
    simp only [Outside, List.mem_singleton, forall_eq]
    fill_bounds
  · intro i hi
    rw [mem]
    refine (limbs i hi).trans ?_
    change Common.scalarWord n fr.rsi i = Common.scalarWord fr.original fr.rsi i
    unfold Common.scalarWord
    apply congrArg bswapSpec
    apply setup.memLoad_eq
    have off : (BitVec.ofNat 64 (8 * (3 - i))).toNat = 8 * (3 - i) := Nat.mod_eq_of_lt (by omega)
    simp only [Outside, List.mem_singleton, forall_eq]
    fill_bounds

end K256.Proofs.Signing.SecretDecode
