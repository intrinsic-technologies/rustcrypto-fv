import K256.Proofs.Sec1.Square.Contract
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude

theorem squareEntry {code : CodeMap} (s : RamState) (slot : BitVec 64) (w : Square.Store)
    (hsi : s.regValue .rsi = stackPtr s + (8 : BitVec 64))
    (hdi : s.regValue .rdi = stackPtr s + (48 : BitVec 64))
    (hdf : RFLAGS.DirectionFlagClear s.RFLAGS)
    (hr : Readable s.external (stackPtr s) 8) (hslot : stackTop s = slot)
    (hret : slot.toNat < 2^32)
    (hwin : Writable code s.external (stackPtr s - 104) 104)
    (hroom : 104 ≤ (stackPtr s).toNat) (hbound : (stackPtr s).toNat + 88 ≤ 2 ^ 32)
    (halign : (stackPtr s).toNat % 16 = 8)
    (hap : (stackPtr s).toNat + 88 ≤ 0x1145f0 ∨ 0x1148c4 + 104 ≤ (stackPtr s).toNat)
    (hin : WordsAt s.external (s.regValue .rsi) 64 w.1)
    (hinread : Readable s.external (s.regValue .rsi) 40)
    (hout : WordsAt s.external (s.regValue .rdi) 64 w.2)
    (houtwrite : Writable code s.external (s.regValue .rdi) 40) :
    Square.layout.Rel code (Activation.ofEntry s 104 slot, ()) ⟨.entry, #v[], w⟩
      (LIR.lifted.locationOf .l1145f0 s) := by
  let fr := Activation.ofEntry s 104 slot
  have hlow : fr.low.toNat = (stackPtr s).toNat - 104 := Activation.ofEntry_low_toNat
  have hd : fr.rdi.toNat = (stackPtr s).toNat + 48 := by
    change (s.regValue .rdi).toNat = _
    rw [hdi, BitVec.toNat_add]
    change (_ + 48) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hi : fr.rsi.toNat = (stackPtr s).toNat + 8 := by
    change (s.regValue .rsi).toNat = _
    rw [hsi, BitVec.toNat_add]
    change (_ + 8) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hs : fr.rsp = stackPtr s := rfl
  have hsn := congrArg BitVec.toNat hs
  refine ⟨rfl, ⟨w, rfl, rfl, (Atom.all_append _ _).2 ⟨?_, ?_⟩⟩, RamWriteFrame.refl _ _⟩
  · change Atom.All code (LIR.lifted.locationOf .l1145f0 s).arguments s.external
      (LIR.Fn1145f0.frameAtG0 .l1145f0 fr)
    simp only [LIR.Fn1145f0.frameAtG0, Atom.All, Atom.Holds, Atom.gpr, Lifted.locationOf,
      Fin.getElem_fin, Vector.getElem_ofFn]
    refine ⟨rfl, Reg.read_df_iff.2 hdf, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hr, hslot, hret, hwin, ?_,
      halign, trivial⟩
    change fr.low.toNat + 104 ≤ fr.rsp.toNat
    rw [hs, hlow]
    omega
  · change Atom.All code (LIR.lifted.locationOf .l1145f0 s).arguments s.external
      (Square.core.atoms .entry () fr w)
    refine ⟨hin, hinread, hout, houtwrite, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · change fr.rdi.toNat % 8 = 0
      omega
    · change fr.rdi.toNat + 40 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 40 ≤ fr.rdi.toNat
      omega
    · change fr.rsi.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rsi.toNat
      omega
    · change fr.rdi.toNat + 40 ≤ 0x1145f0 ∨ 0x1148c4 ≤ fr.rdi.toNat
      omega
    · change fr.rsp.toNat + 8 ≤ 0x1145f0 ∨ 0x1148c4 ≤ fr.low.toNat
      omega
    · change fr.rdi.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat
      omega

private theorem advances_of_anyReturn [Bindings] {b : ReturnBoundary} {s t : RamState}
    (he : (machineAnyReturn b).Exec s t) (ht : t.RIP ≠ b.rip) :
    ∃ n, Advances b n s t := by
  obtain ⟨u, hu, k, hk⟩ := Semantics.exec_iff.mp he
  have reaches {x y : (machineAnyReturn b).State} (h : (machineAnyReturn b).Reaches x y) :
      ∃ n, Advances b n x y := by
    induction h with
    | refl => exact ⟨0, (advances_zero ..).2 rfl⟩
    | step hs _ ih =>
      obtain ⟨n, hn⟩ := hs
      obtain ⟨m, hm⟩ := ih
      exact ⟨n+m, hn.trans hm⟩
  obtain ⟨n, hn⟩ := reaches hu
  rcases hk with hk | hk
  · exact ⟨_, hn.trans hk.1⟩
  · exact False.elim (ht hk.atBoundary.1)

theorem squareSegment [inst : Bindings] {code : CodeMap} {s : RamState} {fr : Activation}
    {b : ReturnBoundary} (w : Square.Store)
    (stride : UnitStringStride inst) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (he : EntryReady code s) (hip : s.RIP = 0x1145f0) (hfs : s.FS = fr.fs)
    (hb : ReturnOutside b code) (hret : fr.ret ≠ b.rip)
    (hr : Square.layout.Rel code (fr, ()) ⟨.entry, #v[], w⟩
      (LIR.lifted.locationOf .l1145f0 s)) :
    ∃ n t, Advances b n s t ∧ EntryReady code t ∧
      LIR.Fn1145f0.Post fr (Square.core.footprint () fr) t ∧
      WordsAt t.external fr.rsi 64 w.1 ∧ WordsAt t.external fr.rdi 64 (Common.Field.squareWords w.1) := by
  obtain ⟨lo, hexec, hout, hdone⟩ :=
    Square.call code fr w _ hr
  obtain ⟨t, ht, hm⟩ := (Lifted.simulationFixed (LIR.blocks stride code hcode) hb s).exec hexec.sem
    ⟨Rel.locationOf he hip, rfl⟩
  have hpc : t.RIP = fr.ret := (Value.eq_bits (Option.some.inj (hout.tag.symm.trans hm.rel.rip))).symm
  obtain ⟨n, hn⟩ := advances_of_anyReturn ht (fun h => hret (hpc.symm.trans h))
  obtain ⟨hsp, hdf, hpres, hmx, hftw, hfcw⟩ := doneAtoms_retRel hm.rel hdone rfl (by decide)
  obtain ⟨r, hresult, ha⟩ := hout.result
  have hres := congrArg CFG.Output.store hresult
  change (w.1, Common.Field.squareWords w.1) = r at hres
  subst r
  have hatoms := (Atom.all_append _ _).1 ha
  obtain ⟨_, hin, hval, _⟩ := hatoms.2
  exact ⟨n, t, hn, ⟨hm.rel.ready, hm.rel.sse, hm.rel.code⟩,
    ⟨hpc, hsp, hpres, hdf, by rw [hmx]; rfl, hftw, hfcw,
      (congrArg (·.FS) hm.fixed).trans hfs, hm.rel.store ▸ hout.frame⟩,
    hm.rel.store ▸ hin, hm.rel.store ▸ hval⟩

end K256.Proofs.Sec1.Sqrt
