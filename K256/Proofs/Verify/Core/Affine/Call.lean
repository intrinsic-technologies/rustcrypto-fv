import K256.Proofs.Verify.LIR.Fn10fe50.Frame
import K256.Proofs.Verify.Core.Affine.Execution
import K256.Proofs.Verify.Core.Affine.Transfer
import K256.Proofs.Verify.Core.Affine.State
import K256.Proofs.Verify.Core.Memory
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Verify.Core.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.ECC
open Generate.Generator.Multiply (scalarWords)

theorem coreText : ∀ x ∈ Verify.LIR.fnCode, x ∈ Extracted.programImage := by
  intro x hx
  apply List.mem_flatMap.mpr
  refine ⟨Verify.LIR.textSection, by simp [Extracted.programSections, Verify.LIR.textSection], ?_⟩
  simpa only [Verify.LIR.fnCode, Verify.LIR.sections, ImageSections.toCodeMap, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] using hx

theorem coreSub {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s d : Nat} (e : Entry fr a p digest r s) (h : d ≤ 12456) :
    (fr.rsp - BitVec.ofNat 64 d).toNat = fr.rsp.toNat - d := by
  have wd : (BitVec.ofNat 64 d).toNat = d := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [wd]; have := e.stackRoom; omega)), wd]

theorem coreWindow {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s d len : Nat} {m : Ram} (e : Entry fr a p digest r s)
    (f : RamWriteFrame fr.original m [fr.region]) (hd : d ≤ 12456) (fit : len ≤ d) :
    Writable Extracted.programImage m (fr.rsp - BitVec.ofNat 64 d) len := by
  have room := e.stackRoom
  apply (e.stack.of_frame f).sub
  · rw [e.low_toNat, coreSub e hd]
    omega
  · rw [e.low_toNat, coreSub e hd]
    omega

theorem resumeCoreCall {caller callee : Location Value Ram Label signature}
    {resume : Label} {ret : BitVec 64} {out : Output Value Ram Reg.count}
    (push : program.runBlock (dialect Extracted.programImage) caller =
      .call callee ⟨resume, #v[], rfl, some ⟨64, ret⟩⟩)
    (run : program.Exec (dialect Extracted.programImage) ⟨callee, []⟩ out)
    (tag : out.tag = some ⟨64, ret⟩) :
    (program.sem (dialect Extracted.programImage)).Reaches ⟨caller, []⟩
      ⟨⟨resume, out.values, out.store⟩, []⟩ := by
  let frame : StackFrame Value Label signature Reg.count := ⟨resume, #v[], rfl, some ⟨64, ret⟩⟩
  refine .step (b := ⟨callee, [frame]⟩) ?_ ?_
  · change (program.runBlock _ _).next _ _ = _
    rw [push]
    rfl
  · exact ParseSignature.exec_reaches_resume run frame [] (by
      rw [tag]
      exact decide_eq_true (rfl : Value.mk 64 ret = Value.mk 64 ret))

private abbrev returnSlot (fr : Activation) := fr.rsp - 496

private abbrev pushed (fr : Activation) (m : Ram) := memStore m (returnSlot fr) (0x10527f : BitVec 64)

private def activation (fr : Activation) (b : Registers) (m : Ram) : Activation :=
  { fr with
    original := pushed fr m
    rsp := returnSlot fr
    ret := 0x10527f
    low := fr.rsp - 1472
    rbx := fr.rdi
    rsi := localSp fr + 8
    rdi := localSp fr + 136
    r12 := b[12].get 64
    r13 := localSp fr + 8
    r14 := localSp fr + 136
    r15 := b[15].get 64 }

private theorem widthValue (v : Value) (h : v.width = 64) : v = ⟨64, v.get 64⟩ := by
  cases v
  cases h
  rw [Value.get_mk]

private theorem callBlock {fr : Activation} {b : Registers} {m : Ram} {point : Curve.Point} {r : Nat}
    (h : PointResult fr b m point r)
    (store : StoreOk Extracted.programImage m (returnSlot fr) 8 0x10527a 5) :
    ∃ c, program.runBlock (dialect Extracted.programImage) ⟨.l10526c,b,m⟩ =
      .call ⟨.l10fe50,c,pushed fr m⟩ ⟨.l10527f,#v[],rfl,some ⟨64,0x10527f⟩⟩ ∧
      c[4] = ⟨64, returnSlot fr⟩ ∧ c[6] = ⟨64, localSp fr + 8⟩ ∧
      c[7] = ⟨64, localSp fr + 136⟩ ∧ c[14] = ⟨64, localSp fr + 136⟩ ∧
      c[3] = b[3] ∧ c[5] = b[5] ∧ c[12] = b[12] ∧ c[13] = b[13] ∧ c[15] = b[15] ∧
      c[22] = b[22] ∧ c[39] = b[39] ∧ c[50] = b[50] ∧ c[51] = b[51] := by
  have sp := (congrArg (Value.get 64) h.sp).trans (Value.get_mk _ _)
  have ptr := (congrArg (Value.get 64) h.ptr).trans (Value.get_mk _ _)
  have slot : localSp fr - 8 = returnSlot fr := by unfold localSp; bv_omega
  refine ⟨?regs, ?run, ?post⟩
  case run =>
    cfg_eval [sp, ptr]
    rw [slot, ite_eq_left store]
  case post =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem affinePath {fr : Activation} {a b : Registers} {p point : Curve.Point}
    {digest : ByteArray} {r s : Nat} {m : Ram}
    (e : Entry fr a p digest r s) (h : PointResult fr b m point r) :
    ∃ c n, Reaches .l10526c b m .l10527f c n ∧ Phase fr c n ∧
      c[14] = ⟨64, localSp fr + 136⟩ ∧
      Ecdh.Affine.XAt n (localSp fr + 136) point ∧
      WordsAt n (localSp fr + 256) 64 (scalarWords r) := by
  let child := activation fr b m
  have offsets (d : Nat) (hd : d ≤ 12456) := coreSub e hd
  have room := e.stackRoom
  have upper := e.low
  have low := e.low_toNat
  have sp : child.rsp.toNat = fr.rsp.toNat - 496 := offsets 496 (by decide)
  have bottom : child.low.toNat = fr.rsp.toNat - 1472 := offsets 1472 (by decide)
  have srcAddr : child.rsi = fr.rsp - 480 := by change fr.rsp - 488 + 8 = _; bv_omega
  have dstAddr : child.rdi = fr.rsp - 352 := by change fr.rsp - 488 + 136 = _; bv_omega
  have rAddr : localSp fr + 256 = fr.rsp - 232 := by unfold localSp; bv_omega
  have dstN : child.rdi.toNat = fr.rsp.toNat - 352 := by
    rw [dstAddr]; exact offsets 352 (by decide)
  have rN : (localSp fr + 256).toNat = fr.rsp.toNat - 232 := by
    rw [rAddr]; exact offsets 232 (by decide)
  have pushedFrame : RamWriteFrame m (pushed fr m) [⟨child.rsp.toNat, 8⟩] := by
    apply (RamWriteFrame.refl m _).memStore
    exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, by change child.rsp.toNat + 8 ≤ _; omega⟩
  have combined := h.frame.trans pushedFrame (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
    · change fr.low.toNat ≤ child.rsp.toNat; omega
    · change child.rsp.toNat + 8 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      omega)
  have src : Generate.Generator.Affine.ProjectiveAt child.original child.rsi point := by
    obtain ⟨x, y, z, xl, yl, zl, wx, wy, wz, rx, ry, rz, same⟩ := h.pointAt
    refine ⟨x, y, z, xl, yl, zl, wx.write_apart _ _ ?_, wy.write_apart _ _ ?_,
      wz.write_apart _ _ ?_, rx, ry, rz, same⟩
    all_goals
      apply RangeApart.of_diff
      change 8 ≤ (_ - (fr.rsp - 496)).toNat ∧ 40 ≤ ((fr.rsp - 496) - _).toNat
      constructor <;> simp only [localSp] <;> bv_omega
  have slotWrite : Writable Extracted.programImage m (returnSlot fr) 8 :=
    coreWindow e h.frame (by decide : 496 ≤ 12456) (by decide)
  have store : StoreOk Extracted.programImage m (returnSlot fr) 8 0x10527a 5 :=
    ParseSignature.storeOk_of_codeRange (off := 14) slotWrite
      (fun x hx => coreText x (code_l10526c x hx)) (by decide)
  obtain ⟨c, push, reg4, reg6, reg7, reg14, reg3, reg5, reg12, reg13, reg15,
    reg22, reg39, reg50, reg51⟩ := callBlock h store
  have input := e.atoms
  simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at input
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, align,
    _, _, _, _, _, _, apart, _⟩ := input
  have got := Verify.LIR.Fn10fe50.callSlots_loaded
    (sections := Extracted.programSections) (by simp [Verify.LIR.rodataSection, Extracted.programSections])
    (e.loaded_of_frame combined)
  obtain ⟨read₁, load₁⟩ := got (0x203de0, 0x129770) (by decide)
  obtain ⟨read₂, load₂⟩ := got (0x203e20, 0x100a20) (by decide)
  have win : Writable Extracted.programImage child.original (child.rsp - 976) 976 := by
    rw [show child.rsp - 976 = fr.rsp - 1472 by change fr.rsp - 496 - 976 = _; bv_omega]
    exact coreWindow e combined (by decide : 1472 ≤ 12456) (by decide)
  have source : Readable child.original child.rsi 120 := by
    rw [srcAddr]
    exact (coreWindow e combined (by decide : 480 ≤ 12456) (by decide : 120 ≤ 480)).readable
  have dest : Writable Extracted.programImage child.original child.rdi 88 := by
    rw [dstAddr]
    exact coreWindow e combined (by decide : 352 ≤ 12456) (by decide)
  have srcOffset : child.rsi = child.rsp + 16 := by
    change fr.rsp - 488 + 8 = fr.rsp - 496 + 16
    bv_omega
  have dstOffset : child.rdi = child.rsp + 144 := by
    change fr.rsp - 488 + 136 = fr.rsp - 496 + 144
    bv_omega
  have childRead : Readable child.original child.rsp 8 := (slotWrite.of_frame pushedFrame).readable
  have childRet : memLoad child.original child.rsp 64 = child.ret :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  change fr.rsp.toNat % 16 = 8 at align
  change 0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 at apart
  have state : CallState .l10fe50 child c child.original := by
    refine ⟨?_, e.loaded_of_frame combined, source, dest, srcOffset, dstOffset, by omega,
      RamWriteFrame.refl _ _⟩
    exact ⟨reg4, reg22.trans h.df, trivial, trivial, reg3.trans h.dst, reg5.trans h.rbp,
      reg6, reg7, trivial, trivial, reg12.trans (widthValue _ h.width12), reg13.trans h.ptr, reg14,
      reg15.trans (widthValue _ h.width15), reg39.trans h.mxcsr, reg50.trans h.ftw, reg51.trans h.fcw,
      childRead, childRet, by change (0x10527f : Nat) < 2^32; decide, win,
      by change child.low.toNat + 976 ≤ child.rsp.toNat; omega,
      by change child.rsp.toNat % 16 = 8; omega, read₁, load₁, read₂, load₂,
      by change 0x2041f8 ≤ child.rsp.toNat ∨ child.rsp.toNat ≤ 0x203de0; omega, trivial⟩
  obtain ⟨out, run, tag, done, written, xAt⟩ := execution state src
  have reached := resumeCoreCall push (transfer run) tag
  change Atom.All _ _ _ (Generate.LIR.Fn10fe50.doneAt child) at done
  obtain ⟨rsp, df, bx, bp, _, _, xPtr, _, mx, fw, cw, _⟩ := done
  have pop : child.rsp + 8 = localSp fr := by change fr.rsp - 496 + 8 = fr.rsp - 488; bv_omega
  have finalFrame := combined.trans written (by
    intro reg hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
      · change fr.low.toNat ≤ child.low.toNat; omega
      · change child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤
          fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
        omega
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
      · change fr.low.toNat ≤ child.rdi.toNat; omega
      · change child.rdi.toNat + 88 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
        omega)
  have untouched {addr : BitVec 64} {len : Nat}
      (lo : fr.rsp.toNat - 232 ≤ addr.toNat) (hi : addr.toNat + len ≤ 2^64) :
      Outside [⟨child.rsp.toNat, 8⟩] addr len ∧
        Outside (Generate.Generator.Affine.writes child) addr len := by
    refine ⟨⟨hi, ?_⟩, ⟨hi, ?_⟩⟩
    · intro reg hr
      obtain rfl := List.mem_singleton.mp hr
      right
      change child.rsp.toNat + 8 ≤ _
      omega
    · intro reg hr
      rcases List.mem_cons.mp hr with rfl | hr
      · right
        change child.low.toNat + (child.rsp.toNat - child.low.toNat) ≤ _
        omega
      · obtain rfl := List.mem_singleton.mp hr
        exact Or.inr (by change child.rdi.toNat + 88 ≤ _; omega)
  have restore (d : Nat) (hd : d ≤ 40) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 d) 64 =
        memLoad m (fr.rsp - BitVec.ofNat 64 d) 64 := by
    have address := offsets d (by omega)
    obtain ⟨before, after⟩ := untouched (addr := fr.rsp - BitVec.ofNat 64 d) (len := 8)
      (by omega) (by omega)
    exact (written.memLoad_eq after).trans (pushedFrame.memLoad_eq before)
  obtain ⟨before, after⟩ := untouched (addr := localSp fr + 256) (len := 32) (by omega) (by omega)
  have rout := (h.rAt.of_frame pushedFrame (by decide) before).of_frame written (by decide) after
  rw [pop] at rsp
  exact ⟨out.values, out.store, reached, ⟨⟨rsp, bx, bp, df, mx, fw, cw,
    (restore 40 (by decide)).trans h.rbx, (restore 32 (by decide)).trans h.r12,
    (restore 24 (by decide)).trans h.r13, (restore 16 (by decide)).trans h.r14,
    (restore 8 (by decide)).trans h.r15⟩, finalFrame⟩, xPtr, xAt, rout⟩

end K256.Proofs.Verify.Core.Affine
