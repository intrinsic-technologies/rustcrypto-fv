import K256.Proofs.Sec1.SqrtCounted.Types

namespace K256.Proofs.Sec1.SqrtCounted

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine LIR
open Sqrt Common.Field

abbrev LoopFrame (code : CodeMap) (a : Values Value Reg.count) (m : Ram) (fr : Activation) :=
  Atom.All code a m (Fn115950.frameAt .l118040 fr)

theorem headFrame (site : SquareLoop) (fr : Activation) :
    Fn115950.frameAt site.head fr = Fn115950.frameAt .l118040 fr := by cases site <;> rfl

theorem exitFrame (site : SquareLoop) (fr : Activation) :
    Fn115950.frameAt site.exit fr = Fn115950.frameAt .l118040 fr := by cases site <;> rfl

theorem loopFrame_of_frame {code : CodeMap} {a b : Values Value Reg.count} {m m' : Ram}
    {fr : Activation} {base : Word} (hbase : base = fr.rsp - 440)
    (h : LoopFrame code a m fr)
    (saved : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i])
    (frame : RamWriteFrame m m' [roundStack base]) : LoopFrame code b m' fr := by
  obtain ⟨rsp, df, mx, ftw, fcw, o, bx, r12, r13, r14, r15, bp, rd, ret, low, wr, room, al, _⟩ := h
  change Readable m fr.rsp 8 at rd
  change Writable code m (fr.rsp - 552) 552 at wr
  change fr.low.toNat + 552 ≤ fr.rsp.toNat at room
  have bound := rd.low
  have hb : (base - 112).toNat = fr.rsp.toNat - 552 := by
    rw [hbase, BitVec.sub_sub, show (440 : Word) + 112 = 552 by decide]
    exact BitVec.toNat_sub_of_le (by change 552 ≤ fr.rsp.toNat; omega)
  have slot (k : Word) (hk : k.toNat ≤ 56) :
      memLoad m' (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    apply frame.memLoad_eq
    have hs := BitVec.toNat_sub_of_le (x := fr.rsp) (y := k) (by rw [BitVec.le_def]; omega)
    refine ⟨by rw [hs]; omega, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    right
    change (base - 112).toNat + 192 ≤ (fr.rsp - k).toNat
    rw [hb, hs]
    omega
  have hret : memLoad m' fr.rsp 64 = memLoad m fr.rsp 64 := by
    simpa only [show fr.rsp - (0 : Word) = fr.rsp by bv_omega] using slot 0 (by decide)
  exact ⟨(saved 4 (by decide)).trans rsp, (saved 22 (by decide)).trans df,
    (saved 39 (by decide)).trans mx, (saved 50 (by decide)).trans ftw, (saved 51 (by decide)).trans fcw,
    (slot 56 (by decide)).trans o, (slot 48 (by decide)).trans bx, (slot 40 (by decide)).trans r12,
    (slot 32 (by decide)).trans r13, (slot 24 (by decide)).trans r14, (slot 16 (by decide)).trans r15,
    (slot 8 (by decide)).trans bp, rd.of_frame frame, hret.trans ret, low,
    wr.of_frame frame, room, al, trivial⟩

theorem loopGeometry {code : CodeMap} {a : Values Value Reg.count} {m : Ram}
    {fr : Activation} {base : Word} (hbase : base = fr.rsp - 440)
    (h : LoopFrame code a m fr) :
    a[4] = ⟨64, base⟩ ∧ a[22] = ⟨1, 0⟩ ∧ a[39].width = 32 ∧
    a[50].width = 16 ∧ a[51].width = 16 ∧
    Writable code m (base - 112) 192 ∧ 112 ≤ base.toNat ∧ base.toNat % 16 = 0 := by
  obtain ⟨rsp, df, mx, ftw, fcw, _, _, _, _, _, _, _, _, _, _, wr, room, al, _⟩ := h
  change Writable code m (fr.rsp - 552) 552 at wr
  change fr.low.toNat + 552 ≤ fr.rsp.toNat at room
  change fr.rsp.toNat % 16 = 8 at al
  have addr : base - 112 = fr.rsp - 552 := by rw [hbase, BitVec.sub_sub]; rfl
  have hnat : base.toNat = fr.rsp.toNat - 440 := by
    rw [hbase, BitVec.toNat_sub_of_le (by change 440 ≤ fr.rsp.toNat; omega)]
    rfl
  refine ⟨hbase ▸ rsp, df, congrArg Value.width mx, congrArg Value.width ftw, congrArg Value.width fcw,
    ?_, by omega, by omega⟩
  rw [addr]
  exact wr.sub (Nat.le_refl _) (by omega)

end K256.Proofs.Sec1.SqrtCounted
