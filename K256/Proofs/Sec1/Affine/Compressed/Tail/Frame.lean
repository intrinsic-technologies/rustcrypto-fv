import K256.Proofs.Sec1.Affine.Compressed.Tail.Stages

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

theorem bodyAt_selectWrites {code : CodeMap} {fr : Activation} {args next : Values Value Reg.count}
    {mem m : Ram} {xs : Limbs} {xOK : Bool} {want : BitVec 8}
    (body : BodyAt code fr args mem xs xOK want)
    (rsp : next[4] = ⟨64,workSP fr⟩)
    (kept : ∀ i : Fin 53, i.val ∈ [22,39,50,51] → next[i] = args[i])
    (frame : RamWriteFrame mem m (selectWrites (workSP fr))) :
    BodyAt code fr next m xs xOK want ∧ RamWriteFrame mem m [fr.region] := by
  obtain ⟨atoms, output, x, valid, parity⟩ := body
  simp only [Fn1205b0.frameAt, Fn1205b0.frameAtG2, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, df, mx, ft, fc, di, bx, r12, r13, r14, r15, bp, read, ret,
    retLow, stack, room, align, _⟩ := atoms
  have low := read.low
  have sub (off : Nat) (bound : off ≤ 1048) :
      (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
    have hn : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le, hn]
    rw [BitVec.le_def, hn]
    omega
  have sp : (workSP fr).toNat = fr.rsp.toNat - 488 := sub 488 (by decide)
  have plus (off : Nat) (bound : off ≤ 488) :
      (workSP fr + BitVec.ofNat 64 off).toNat = fr.rsp.toNat - 488 + off := by
    rw [BitVec.toNat_add, sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have below : (workSP fr - 121).toNat = fr.rsp.toNat - 609 := by
    rw [workSP, BitVec.sub_sub]
    exact sub 609 (by decide)
  have spans : selectWrites (workSP fr) =
      [⟨fr.rsp.toNat-609,121⟩,⟨fr.rsp.toNat-488+8,16⟩,⟨fr.rsp.toNat-488+32,16⟩,
       ⟨fr.rsp.toNat-488+96,8⟩,⟨fr.rsp.toNat-488+184,248⟩] := by
    unfold selectWrites
    erw [below, plus 8 (by decide), plus 32 (by decide), plus 96 (by decide), plus 184 (by decide)]
  rw [spans] at frame
  have load {addr : Word} {w : Nat} (h : Outside
      [⟨fr.rsp.toNat-609,121⟩,⟨fr.rsp.toNat-488+8,16⟩,⟨fr.rsp.toNat-488+32,16⟩,
       ⟨fr.rsp.toNat-488+96,8⟩,⟨fr.rsp.toNat-488+184,248⟩] addr (w/8)) :=
    frame.memLoad_eq h
  have preserved {addr : Word} {w : Nat} {off : Nat}
      (ha : addr.toNat = fr.rsp.toNat-488+off)
      (safe : (48 ≤ off ∧ off+w/8 ≤ 96) ∨ (104 ≤ off ∧ off+w/8 ≤ 184) ∨
        (432 ≤ off ∧ off+w/8 ≤ 496)) : memLoad m addr w = memLoad mem addr w := by
    apply load
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> omega
  have keptSlot (n : Nat) (hn : n ≤ 48 ∨ n = 352) :
      memLoad m (fr.rsp - BitVec.ofNat 64 n) 64 = memLoad mem (fr.rsp - BitVec.ofNat 64 n) 64 :=
    preserved (off := 488-n) (by rw [sub n (by omega)]; omega) (by rcases hn with hn|rfl <;> omega)
  have kret := keptSlot 0 (by decide)
  have sameRet : memLoad m fr.rsp 64 = memLoad mem fr.rsp 64 := by
    simpa only [BitVec.sub_zero] using kret
  have bodyAtoms : Atom.All code next m (Fn1205b0.frameAt .l120d03 fr) := by
    exact ⟨rsp, (kept 22 (by decide)).trans df, (kept 39 (by decide)).trans mx,
      (kept 50 (by decide)).trans ft, (kept 51 (by decide)).trans fc,
      (keptSlot 352 (by decide)).trans di, (keptSlot 48 (by decide)).trans bx,
      (keptSlot 40 (by decide)).trans r12, (keptSlot 32 (by decide)).trans r13,
      (keptSlot 24 (by decide)).trans r14, (keptSlot 16 (by decide)).trans r15,
      (keptSlot 8 (by decide)).trans bp, read.of_frame frame, sameRet.trans ret,
      retLow, stack.of_frame frame, room, align, trivial⟩
  have limb (off : Nat) (safe : 48 ≤ off ∧ off+8 ≤ 96) :
      memLoad m (workSP fr+BitVec.ofNat 64 off) 64 = memLoad mem (workSP fr+BitVec.ofNat 64 off) 64 :=
    preserved (plus off (by omega)) (.inl safe)
  refine ⟨⟨bodyAtoms, output.of_frame frame, ?_,
      (preserved (w := 64) (plus 128 (by decide)) (by decide)).trans valid,
      (preserved (w := 8) (plus 108 (by decide)) (by decide)).trans parity⟩,
    (RamWriteFrame.refl mem [fr.region]).trans frame ?_⟩
  · refine Eq.trans ?_ x
    have vectorEq {a b c d e a' b' c' d' e' : Word}
        (p : a = a') (q : b = b') (r : c = c') (s : d = d') (t : e = e') :
        #v[a,b,c,d,e] = #v[a',b',c',d',e'] := by
      cases p
      cases q
      cases r
      cases s
      cases t
      rfl
    exact vectorEq (limb 80 (by decide)) (limb 88 (by decide)) (limb 64 (by decide))
      (limb 48 (by decide)) (limb 72 (by decide))
  · intro r hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> dsimp only [Activation.region] <;> omega

end K256.Proofs.Sec1.Affine.Compressed
