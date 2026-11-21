import K256.Proofs.Verify.Core.Lincomb.PeerPath.State
import K256.Proofs.Verify.Core.Lincomb.GeneratorPath.Prepare
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Verify.Core.Lincomb.Prepare
import K256.Proofs.Verify.Core.Lincomb.Recode.Memory

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)

variable {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram}

private theorem peerPrepareSetup {d : Registers} {n : Ram}
    (sp : d[4].get 64 = workSp fr) (regs : PreparesPeer fr d 8)
    (guard : StoreOk Extracted.programImage n (workSp fr - 8) 8 0x10fc0e 5) :
    ∃ x, program.runBlock (dialect Extracted.programImage) ⟨.l10fbfa, d, n⟩ =
        .call ⟨.l10f150, x, memStore n (workSp fr - 8) (0x10fc13 : BitVec 64)⟩
          (callResume .l10fc13 0x10fc13) ∧
      x[4] = ⟨64, workSp fr - 8⟩ ∧ x[7] = ⟨64, fr.rsi⟩ ∧
      x[6] = ⟨64, localSp fr + 416⟩ ∧ x[2] = ⟨64, slot fr 0x1568⟩ ∧
      x[1] = ⟨64, slot fr 8⟩ ∧ x[13] = ⟨64, slot fr 0x1568⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,14,15,22,39,50,51] → x[i] = d[i] := by
  have peer : d[15].get 64 = fr.rsi := congrArg (Value.get 64) regs.2.2.2.1
  have scalar : d[14].get 64 = localSp fr + 416 := congrArg (Value.get 64) regs.2.2.1
  have digits : d[5].get 64 = slot fr 8 := congrArg (Value.get 64) regs.2.2.2.2
  refine ⟨?_, ?call, ?post⟩
  case call =>
    cfg_eval [sp, peer, scalar, digits, guard]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ live
    simp only [List.mem_cons, List.not_mem_nil, or_false] at live
    rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem preparePeer (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) (hv : v < domain.n) {d n}
    (saved : CallerFrame fr c d m n) (generator : GeneratorCopy fr n u) (regs : PreparesPeer fr d 8)
    (zero : DigitBytes n (slot fr 8 + 8) [] ∧ DigitBytes n (slot fr 8 + 0x118) []) :
    ∃ f t, Reaches .l10fbfa d n .l10fc13 f t ∧ CallerFrame fr c f m t ∧ PeerPrepared fr f t p u v := by
  let sp := workSp fr - 8
  let pushed := memStore n sp (0x10fc13 : BitVec 64)
  let tables := slot fr 0x1568
  let digits := slot fr 8
  let scalar := localSp fr + 416
  have whole := h.frame.trans saved.frame (frameBounds e).1
  have guard : StoreOk Extracted.programImage n sp 8 0x10fc0e 5 :=
    Recode.storeGuard (off := 20) (belowWrite e whole (depth := 8) (by decide)) code_l10fbfa (by decide)
  obtain ⟨x, call, rsp, di, si, dx, cx, tableReg, keep⟩ :=
    peerPrepareSetup (congrArg (Value.get 64) saved.sp) regs guard
  have room := e.stackRoom
  have high := e.low
  have base := workNat e
  have pushNat : sp.toNat = (workSp fr).toNat - 8 := belowWorkNat e (depth := 8) (by decide)
  have low := e.low_toNat
  have tableNat : tables.toNat = fr.rsp.toNat - 10952 + 0x1568 := slotNat e (by decide)
  have digitsNat : digits.toNat = fr.rsp.toNat - 10952 + 8 := slotNat e (by decide)
  have scalarNat : scalar.toNat = fr.rsp.toNat - 488 + 416 :=
    ScalarProduct.slotNat e (off := 416) (by decide)
  have pointNat : fr.rsi.toNat = fr.rsp.toNat + 16 := by
    rw [e.key, BitVec.toNat_add, Nat.mod_eq_of_lt (by change _ + 16 < _; omega)]
    rfl
  have pushFrame : RamWriteFrame n pushed [scratch (workSp fr) 8] := preparePushFrame e 0x10fc13
  have wholePush : RamWriteFrame fr.original pushed [fr.region] := whole.trans pushFrame (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, by simp only [scratch, Activation.region]; omega⟩)
  have pushOutside {ptr : BitVec 64} {len : Nat} (lo : (workSp fr).toNat ≤ ptr.toNat)
      (hi : ptr.toNat + len ≤ 2^64) : Outside [scratch (workSp fr) 8] ptr len := by
    refine ⟨hi, fun reg hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    dsimp only [scratch]
    omega
  have ret : memLoad pushed sp 64 = 0x10fc13 := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have control (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : x[i] = d[i] :=
    keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)
  have fixed (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : x[i] = b[i] :=
    ((control i hi).trans (saved.fixedRegs i hi)).trans
      (args.keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
  have widths (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) : x[i].width = 64 := by
    by_cases h13 : i.val = 13
    · obtain rfl : i = 13 := Fin.ext h13
      exact congrArg Value.width tableReg
    · rw [keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)]
      exact saved.widths i hi
  have entry : RoutineEntry x pushed sp 0x558 :=
    routineEntry e wholePush (by decide) rsp widths ((fixed 22 (by decide)).trans h.df)
      (congrArg Value.width ((fixed 39 (by decide)).trans h.mxcsr))
      (congrArg Value.width ((fixed 50 (by decide)).trans h.ftw))
      (congrArg Value.width ((fixed 51 (by decide)).trans h.fcw))
      (by rw [ret]; decide)
  obtain ⟨q, point, valid, value⟩ := e.peer_of_frame wholePush
  have words : WordsAt pushed scalar 64 (scalarWords v) :=
    (h.vAt.of_frame saved.frame (by decide) ((frameBounds e).2 416 32 (by decide) (by decide))).of_frame
      pushFrame (by decide) (pushOutside (ptr := scalar) (len := 32) (by omega) (by omega))
  have pointRead : Readable pushed fr.rsi 120 :=
    (e.upper.of_frame wholePush).readable.of_offsets (x := fr.rsp) (c := 16) (d := 8) e.key rfl (by decide)
  have zeroPush (off : Nat) (fits : off + 257 ≤ 544)
      (clear : DigitBytes n (digits + BitVec.ofNat 64 off) []) :
      DigitBytes pushed (digits + BitVec.ofNat 64 off) [] := by
    have addr := toNat_add_ofNat digits off (by omega)
    exact Recode.digitBytes_of_frame pushFrame (pushOutside (by omega) (by omega)) clear
  obtain ⟨out, run, post, peer⟩ := prepare (sp := sp) (src := fr.rsi) (scalar := scalar)
    (tables := tables) (digits := digits) entry di si dx cx hv valid point words pointRead
    (ScalarProduct.writeSlot e (off := 416) wholePush (by decide)).readable
    (by simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      scratch]; omega)
    (by simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      scratch]; omega)
    (workWrite e wholePush (k := 0x1568) (by decide))
    (workWrite e wholePush (k := 8) (by decide))
    (by simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      scratch]; omega)
    (by simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      scratch]; omega)
    ⟨zeroPush 8 (by decide) zero.1, zeroPush 0x118 (by decide) zero.2⟩
  obtain ⟨frame, written⟩ := CallerFrame.afterPrepare e saved control widths (by decide) (by decide) post
  have copy {off len : Nat} (fits : off + len ≤ 0x1568) (lower : 8 + 544 ≤ off) :
      Copied n (slot fr off) out.store (slot fr off) len := by
    apply Copied.of_frame written
    have addr := slotNat e (k := off) (by omega)
    change (slot fr 0x1568).toNat = _ at tableNat
    change (slot fr 8).toNat = _ at digitsNat
    simp only [prepareWrites, Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, scratch]
    omega
  have reach := reachesCall call run (post.tag.trans (congrArg (fun x => some (Value.mk 64 x)) ret))
  refine ⟨_, _, reach, frame, generator.of_copy (copy (by decide) (by decide)) (copy (by decide) (by decide)),
    value ▸ peer, (post.saved 12 (by decide)).trans ((keep 12 (by decide)).trans regs.2.1),
    (post.saved 13 (by decide)).trans tableReg,
    (post.saved 5 (by decide)).trans ((keep 5 (by decide)).trans regs.2.2.2.2)⟩

end K256.Proofs.Verify.Core.Lincomb
