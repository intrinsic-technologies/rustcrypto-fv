import K256.Proofs.Sec1.Sqrt.Finish.Compare
import K256.Proofs.Sec1.SqrtChainExecution.Stages
import K256.Proofs.Sec1.Sqrt.Finish.Status

namespace K256.Proofs.Sec1.Sqrt.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field
open K256.Proofs.Sec1.SqrtChainExecution
open K256.Proofs.Sec1.SqrtLaterProducts.Final (ScratchWrites)

private theorem widthBits (v : Value) (h : v.width = 64) : v = ⟨64, v.get 64⟩ := by
  cases v with
  | mk w b =>
    change w = 64 at h
    subst w
    simp only [Value.get, BitVec.setWidth_eq]

private theorem compareOffsets_bound (o : Word) (h : o ∈ compareWriteOffsets) :
    o.toNat ≤ 256 := by
  simp only [compareWriteOffsets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem writeFrame {mem scratch : Ram} (fr : Activation) (sp : Word)
    (hn : sp.toNat + 440 = fr.rsp.toNat) (hbase : 8 ≤ sp.toNat)
    (hlow : fr.rsp.toNat + 8 ≤ 2 ^ 32) (hroom : fr.low.toNat + 552 ≤ fr.rsp.toNat)
    (hm : ScratchWrites mem scratch sp compareWriteOffsets) :
    let edited : MemoryRegion := ⟨(sp - 8).toNat, 272⟩
    RamWriteFrame mem (memStore scratch (sp - 8) (0x11a51c : Word)) [edited] ∧
    RegionsWithin [edited] (fr.region :: footprint fr) := by
  let edited : MemoryRegion := ⟨(sp - 8).toNat, 272⟩
  have h8 : (sp - 8).toNat = sp.toNat - 8 := BitVec.toNat_sub_of_le (by exact hbase)
  have hoff (o : Word) (ho : o.toNat ≤ 256) : (sp + o).toNat = sp.toNat + o.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hs : RamWriteFrame mem scratch [edited] := by
    apply hm
    intro o ho
    have hb := compareOffsets_bound o ho
    refine ⟨edited, List.mem_cons_self, ?_⟩
    change (sp - 8).toNat ≤ (sp + o).toNat ∧
      (sp + o).toNat + 8 ≤ (sp - 8).toNat + 272 ∧ (sp + o).toNat + 8 ≤ 2 ^ 64
    rw [h8, hoff _ hb]
    omega
  refine ⟨hs.memStore _ ?_, ?_⟩
  · refine ⟨edited, List.mem_cons_self, ?_⟩
    change (sp - 8).toNat ≤ (sp - 8).toNat ∧
      (sp - 8).toNat + 8 ≤ (sp - 8).toNat + 272 ∧ (sp - 8).toNat + 8 ≤ 2 ^ 64
    rw [h8]
    omega
  · intro r hr
    have equ : r = edited := List.mem_singleton.mp hr
    subst r
    refine ⟨fr.region, List.mem_cons_self, ?_⟩
    change fr.low.toNat ≤ (sp - 8).toNat ∧
      (sp - 8).toNat + 272 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
    rw [h8]
    omega

noncomputable def comparisonByte (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) : Option (BitVec 8) :=
  match LIR.program.runBlock (Lift.dialect code) ⟨.l11a14c, args, mem⟩ with
  | .call child _ => some ((child.arguments[7]'(show 7 < Reg.count by decide) |>.get 64).setWidth 8)
  | _ => none

set_option maxHeartbeats 1000000 in
theorem compareThenWriteback {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {fr : Activation} (geom : Geometry code fr) (candidate : Limbs)
    (hf : Atom.All code args mem (LIR.Fn115950.frameAt .l11a14c fr))
    (hCandidate : WordsAt mem (fr.rsp - 400) 64 candidate)
    (hDest : Writable code mem fr.rdi 41)
    (hWrites : RamWriteFrame fr.original mem (fr.region :: footprint fr)) :
    ∃ o, ∃ flag : BitVec 8, comparisonByte code args mem = some flag ∧
      LIR.program.Exec (Lift.dialect code) ⟨⟨.l11a14c, args, mem⟩, []⟩ o ∧
      o.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code o.values o.store (LIR.Fn115950.doneAt fr) ∧
      o.values[0] = ⟨64, fr.rdi⟩ ∧ WordsAt o.store fr.rdi 64 candidate ∧
      memLoad o.store (fr.rdi + 40) 8 = flag ∧
      RamWriteFrame fr.original o.store (fr.region :: footprint fr) := by
  simp only [LIR.Fn115950.frameAt, LIR.Fn115950.frameAtG1, Atom.All, Atom.Holds] at hf
  obtain ⟨rsp, df, mxcsr, ftw, fcw, saveOut, saveB, save12, save13, save14, save15, saveBP,
    retRead, retWord, retLow, stack, room, align, _⟩ := hf
  let sp := fr.rsp - 440
  have tn (k : Nat) (hk : k ≤ 552) : (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have hk' : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hk']; omega), hk']
  have hspNat : sp.toNat + 440 = fr.rsp.toNat := by
    change (fr.rsp - BitVec.ofNat 64 440).toNat + 440 = _
    rw [tn 440 (by decide)]
    omega
  have hn : (sp - 8).toNat = fr.rsp.toNat - 448 := by
    rw [show sp - 8 = fr.rsp - BitVec.ofNat 64 448 by change fr.rsp - 440 - 8 = _; bv_omega]
    exact tn 448 (by decide)
  have readBound := retRead.low
  have hspace : 8 ≤ sp.toNat := by omega
  have hsa : Writable code mem (sp - 8) 440 := by
    have hsn := tn 552 (by decide)
    change (fr.rsp - 552).toNat = fr.rsp.toNat - 552 at hsn
    apply stack.sub <;> change _ ≤ _ <;> omega
  have hcode : sp.toNat + 432 ≤ 0x11a14c ∨ 0x11a51c + 8 ≤ sp.toNat := by
    rcases geom.stackCode with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  have hwords : WordsAt mem (sp + 40) 64 candidate := by
    change WordsAt mem (fr.rsp - 440 + 40) 64 _
    rw [show fr.rsp - 440 + 40 = fr.rsp - 400 by bv_omega]
    exact hCandidate
  have valueRsp : args[4].get 64 = sp := congrArg (Value.get 64) rsp
  have hc := compareBlock candidate valueRsp hsa hspace (by omega) hcode hwords
  change CallTo (lifted := LIR.lifted) (CallsBarrier args mem sp candidate)
    (LIR.program.runBlock (Lift.dialect code) ⟨.l11a14c, args, mem⟩) at hc
  generalize hrun : LIR.program.runBlock (Lift.dialect code) ⟨.l11a14c, args, mem⟩ = tr at hc
  cases tr with
  | call child cont =>
    obtain ⟨regs, scratch, rfl, rfl, rr, limb0, limb1, limb2, hm⟩ := hc
    let updated := memStore scratch (sp - 8) (0x11a51c : Word)
    obtain ⟨frame, within⟩ := writeFrame fr sp hspNat hspace readBound room hm
    have hf := hWrites.trans frame within
    have saved (off : Nat) (ho : off ≤ 56) :
        memLoad updated (fr.rsp - BitVec.ofNat 64 off) 64 =
        memLoad mem (fr.rsp - BitVec.ofNat 64 off) 64 := by
      apply frame.memLoad_eq
      have hnat := tn off (by omega)
      refine ⟨by omega, fun r hr => ?_⟩
      have equ := List.mem_singleton.mp hr
      subst r
      exact .inr (by change (sp - 8).toNat + 272 ≤ _; omega)
    have retEq : memLoad updated fr.rsp 64 = fr.ret := by
      have eq := saved 0 (by decide)
      change memLoad updated (fr.rsp - 0#64) 64 = memLoad mem (fr.rsp - 0#64) 64 at eq
      rw [BitVec.sub_zero] at eq
      exact eq.trans retWord
    have pushEq : memLoad updated (fr.rsp - 448) 64 = 0x11a51c := by
      change memLoad (memStore scratch (sp - 8) (0x11a51c : Word)) (fr.rsp - 448) 64 = _
      rw [show fr.rsp - 448 = sp - 8 by change _ = fr.rsp - 440 - 8; bv_omega]
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    have stays (o : Word) (ho : o.toNat ≤ 256) :
        memLoad updated (sp + o) 64 = memLoad scratch (sp + o) 64 := by
      apply memLoad_memStore_of_rangeApart
      apply RangeApart.of_toNat
      · omega
      · have hap : (sp + o).toNat = sp.toNat + o.toNat := by
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        omega
      · have hap : (sp + o).toNat = sp.toNat + o.toNat := by
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        exact .inl (by omega)
    let payload : Writeback := ⟨candidate[0], candidate[1], candidate[2],
      candidate[3], candidate[4], regs[7].get 64⟩
    have entry : Atom.All code regs updated (barrierInputs fr payload) := by
      have restrsp : regs[4] = ⟨64, fr.rsp - 448⟩ := rr.rsp.trans
        (congrArg (Value.mk 64) (by change fr.rsp - 440 - 8 = fr.rsp - 448; bv_omega))
      simp only [barrierInputs, LIR.Fn115950.frameAt, LIR.Fn115950.frameAtG1, List.tail_cons,
        inputs, List.cons_append, List.nil_append, Atom.All, Atom.Holds]
      refine ⟨restrsp, widthBits _ rr.rdiWidth, pushEq, ?_,
        rr.df.trans df, rr.mxcsr.trans mxcsr, rr.ftw.trans ftw, rr.fcw.trans fcw,
        (saved 56 (by decide)).trans saveOut, (saved 48 (by decide)).trans saveB,
        (saved 40 (by decide)).trans save12, (saved 32 (by decide)).trans save13,
        (saved 24 (by decide)).trans save14, (saved 16 (by decide)).trans save15,
        (saved 8 (by decide)).trans saveBP, retRead.of_frame frame, retEq, retLow,
        stack.of_frame frame, room, align, (widthBits _ rr.r14Width).trans (congrArg (Value.mk 64) rr.limb3),
        (widthBits _ rr.rbxWidth).trans (congrArg (Value.mk 64) rr.limb4),
        ?_, ?_, ?_, hDest.of_frame frame, geom.destStack, ?_, trivial⟩
      · rcases geom.stackCode with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)
      · rw [show fr.rsp - 264 = sp + 0xb0 by change _ = fr.rsp - 440 + 176; bv_omega]
        exact (stays _ (by decide)).trans limb0
      · rw [show fr.rsp - 272 = sp + 0xa8 by change _ = fr.rsp - 440 + 168; bv_omega]
        exact (stays _ (by decide)).trans limb1
      · rw [show fr.rsp - 184 = sp + 0x100 by change _ = fr.rsp - 440 + 256; bv_omega]
        exact (stays _ (by decide)).trans limb2
      · rcases geom.destCode with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)
    obtain ⟨o, run, tags, done, rax, data, status, writes⟩ := barrierThenWriteback fr payload entry hf
    refine ⟨o, payload.status, ?_, Program.Exec.next ?_ run, tags, done, rax, ?_, status, writes⟩
    · simp only [comparisonByte, hrun]
      rfl
    · change (LIR.program.runBlock (Lift.dialect code) ⟨.l11a14c, args, mem⟩).next _ [] = _
      rw [hrun]
      rfl
    · have he : payload.limbs = candidate := by
        apply Vector.ext
        intro i hi
        obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        all_goals rfl
      exact he ▸ data
  | jump _ | returned _ | stuck => exact hc.elim

theorem finishProductWithComparisonByte {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {fr : Activation} {a : Limbs} (geom : Geometry code fr)
    (pre : ProductState code fr a 13 args mem) :
    ∃ o, ∃ flag : BitVec 8, comparisonByte code args mem = some flag ∧
      LIR.program.Exec (Lift.dialect code) ⟨⟨.l11a14c, args, mem⟩, []⟩ o ∧
      o.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code o.values o.store (LIR.Fn115950.doneAt fr) ∧
      o.values[0] = ⟨64, fr.rdi⟩ ∧ WordsAt o.store fr.rdi 64 (words a 27) ∧
      memLoad o.store (fr.rdi + 40) 8 = flag ∧
      RamWriteFrame fr.original o.store (fr.region :: footprint fr) :=
  compareThenWriteback geom (words a 27) pre.frame pre.squared pre.destWrite pre.writes

theorem finishProduct {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {fr : Activation} {a : Limbs} (geom : Geometry code fr)
    (pre : ProductState code fr a 13 args mem) :
    ∃ o, ∃ flag : BitVec 8,
      LIR.program.Exec (Lift.dialect code) ⟨⟨.l11a14c, args, mem⟩, []⟩ o ∧
      o.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code o.values o.store (LIR.Fn115950.doneAt fr) ∧
      o.values[0] = ⟨64, fr.rdi⟩ ∧ WordsAt o.store fr.rdi 64 (words a 27) ∧
      memLoad o.store (fr.rdi + 40) 8 = flag ∧
      RamWriteFrame fr.original o.store (fr.region :: footprint fr) := by
  obtain ⟨o, flag, _, post⟩ := finishProductWithComparisonByte geom pre
  exact ⟨o, flag, post⟩

theorem finishProductStatus {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {fr : Activation} {a : Limbs} (geom : Geometry code fr)
    (pre : ProductState code fr a 13 args mem)
    (check : comparisonByte code args mem = some ((comparisonStatus (words a 27) a).setWidth 8)) :
    ∃ o, LIR.program.Exec (Lift.dialect code) ⟨⟨.l11a14c, args, mem⟩, []⟩ o ∧
      o.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code o.values o.store (LIR.Fn115950.doneAt fr) ∧
      o.values[0] = ⟨64, fr.rdi⟩ ∧ WordsAt o.store fr.rdi 64 (words a 27) ∧
      memLoad o.store (fr.rdi + 40) 8 = (comparisonStatus (words a 27) a).setWidth 8 ∧
      RamWriteFrame fr.original o.store (fr.region :: footprint fr) := by
  obtain ⟨o, flag, hflag, run, htag, done, rax, data, byte, writes⟩ := finishProductWithComparisonByte geom pre
  exact ⟨o, run, htag, done, rax, data, byte.trans (Option.some.inj (hflag.symm.trans check)), writes⟩

end K256.Proofs.Sec1.Sqrt.Finish
