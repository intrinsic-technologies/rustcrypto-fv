import K256.Proofs.Verify.Hash.Update.Copy
import K256.Proofs.Common.SignatureRun
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Signing.UpdateV.Prepare.Append.Memory

namespace K256.Proofs.Signing.UpdateV

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2 K256.Proofs.Verify.Hash

local macro "append_values " b:ident c:ident d:ident : tactic =>
  `(tactic| (try unfold $d:ident
             try unfold $c:ident
             try unfold $b:ident
             simp only [Append.branchArgs, Append.valueArgs, Append.copyArgs,
              Fin.getElem_fin, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
             try rfl))

set_option maxHeartbeats 900000 in
set_option maxRecDepth 2000 in
theorem appendValue {fr : Activation} {a : Values Value Reg.count} {key value : ByteArray} {m : Ram}
    (entry : Atom.All Extracted.programImage a m (Fn104970.frameAt .l104b63 fr))
    (writes : RamWriteFrame fr.original m [fr.region])
    (low : fr.low = fr.rsp - 1200) (depth : 1200 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 8 < 2^32)
    (dataLow : fr.rdi.toNat + 64 < 2^32)
    (apart : fr.rdi.toNat + 64 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (writable : Writable Extracted.programImage fr.original fr.rdi 64)
    (v : (⟨fr.rdi.toNat + 32, 32⟩ : MemoryRegion).HasBytes fr.original value)
    (buf : a[14] = ⟨64, fr.rsp - 488 + 168⟩)
    (state : HmacStateAt m (fr.rsp - 488 + 104) key ByteArray.empty) :
    ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l104b63, a, m⟩, []⟩ ⟨⟨.l104c21, b, t⟩, []⟩ ∧
      Frame .l104c21 fr b t ∧ b[14] = ⟨64, fr.rsp - 488 + 272⟩ ∧
      HmacStateAt t (fr.rsp - 488 + 272) key value := by
  let sp := fr.rsp - 488
  let src := fr.rdi + 32
  let dst := sp + 168
  let area : List MemoryRegion := [⟨sp.toNat - 8,448⟩]
  have sn : sp.toNat = fr.rsp.toNat - 488 :=
    BitVec.toNat_sub_of_le (by change 488 ≤ fr.rsp.toNat; omega)
  have ln : fr.low.toNat = fr.rsp.toNat - 1200 := by
    rw [low]
    exact BitVec.toNat_sub_of_le depth
  have srcNat : src.toNat = fr.rdi.toNat + 32 := by
    dsimp only [src]
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rdi.toNat + 32 < 2^64; omega)]
    rfl
  have addr (i : Nat) (hi : i ≤ 488) : (sp + BitVec.ofNat 64 i).toNat = sp.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have pn : (sp-8).toNat = sp.toNat-8 := BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
  have data := writable.readable.of_frame writes
  have srcRead : Readable m src 32 := data.sub (by rw [srcNat]; omega) (by rw [srcNat]; omega)
  have input : (⟨src.toNat,32⟩ : MemoryRegion).HasBytes m value := by
    rw [srcNat]
    refine ⟨v.1, fun i => ?_⟩
    have len : value.size = 32 := v.1
    have hi := i.isLt
    have va : (BitVec.ofNat 64 (fr.rdi.toNat+32+i.val)).toNat = fr.rdi.toNat+32+i.val :=
      Nat.mod_eq_of_lt (by omega)
    refine (writes.outside _ ⟨by rw [va]; omega, ?_⟩).trans (v.2 i)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [va]
    change _ ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
    omega
  simp only [Fn104970.frameAt, Fn104970.frameAtG5, Atom.All, Atom.Holds] at entry
  obtain ⟨rsp,df,bx,bp,r12,r13,_,mx,ft,fc,sbx,s12,s13,s14,s15,sbp,rr,ret,rl,stack,room,
    align,gr1,g1,gr2,g2,sep,_⟩ := entry
  have work : Writable Extracted.programImage m (sp-8) 448 := stack.sub
    (by rw [←low,ln,pn]; omega) (by rw [←low,ln,pn]; omega)
  have within {p : BitVec 64} {n : Nat} (lo : sp.toNat-8 ≤ p.toNat)
      (hi : p.toNat+n ≤ sp.toNat+440) : InRegions area p n := by
    refine ⟨_,List.mem_cons_self,lo,?_,by omega⟩
    change _ ≤ sp.toNat-8+448
    omega
  have extend {t : Ram} (w : RamWriteFrame m t area) {p : BitVec 64} {k : Nat} (x : BitVec k)
      (lo : sp.toNat-8 ≤ p.toNat) (hi : p.toNat+k/8 ≤ sp.toNat+440) :=
    w.memStore x (within lo hi)
  have withinData (i : Nat) (hi : i+8 ≤ 32) :
      Outside area (src + BitVec.ofNat 64 i) 8 := by
    have h := Ecdh.Output.outputOffset srcRead.low (i := i) (by omega)
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ sp.toNat-8 ∨ sp.toNat-8+448 ≤ _
    omega
  let m₁ := memStore m (dst+24) (memLoad m (src+24) 64)
  let m₂ := memStore m₁ (dst+16) (memLoad m (src+16) 64)
  let m₃ := memStore m₂ (dst+8) (memLoad m (src+8) 64)
  let m₄ := Append.stored m dst src
  let t := Append.marked m sp src
  let u := Append.pushed m sp src
  have d24 : (dst+24).toNat = sp.toNat+192 := by
    simpa only [dst,BitVec.add_assoc,BitVec.reduceAdd] using addr 192 (by decide)
  have d16 : (dst+16).toNat = sp.toNat+184 := by
    simpa only [dst,BitVec.add_assoc,BitVec.reduceAdd] using addr 184 (by decide)
  have d8 : (dst+8).toNat = sp.toNat+176 := by
    simpa only [dst,BitVec.add_assoc,BitVec.reduceAdd] using addr 176 (by decide)
  have d0 : dst.toNat = sp.toNat+168 := addr 168 (by decide)
  have usedN : (sp+231).toNat = sp.toNat+231 := addr 231 (by decide)
  have fromN : (sp+104).toNat = sp.toNat+104 := addr 104 (by decide)
  have toN : (sp+272).toNat = sp.toNat+272 := addr 272 (by decide)
  have w₀ := RamWriteFrame.refl m area
  have w₁ : RamWriteFrame m m₁ area := extend w₀ _ (by omega) (by change _+8 ≤ _; omega)
  have w₂ : RamWriteFrame m m₂ area := extend w₁ _ (by omega) (by change _+8 ≤ _; omega)
  have w₃ : RamWriteFrame m m₃ area := extend w₂ _ (by omega) (by change _+8 ≤ _; omega)
  have w₄ : RamWriteFrame m m₄ area := extend w₃ _ (by omega) (by change _+8 ≤ _; omega)
  have wt : RamWriteFrame m t area := extend w₄ _ (by omega) (by change _+1 ≤ _; omega)
  have wu : RamWriteFrame m u area := extend wt _ (by omega) (by change _+8 ≤ _; omega)
  have finalFrame : RamWriteFrame m (memCopy u (sp+272) (sp+104) 168) area :=
    Sec1.Wrapper.Copy.memCopy_frame wu (within (by omega) (by omega))
  have stackAt {p : BitVec 64} {n : Nat} {ram : Ram} (w : RamWriteFrame m ram area)
      (lo : sp.toNat-8 ≤ p.toNat) (hi : p.toNat+n ≤ sp.toNat+440) :
      Writable Extracted.programImage ram p n :=
    (work.of_frame w).sub (by omega) (by omega)
  have store {p : BitVec 64} {n : Nat} {ram : Ram} (w : RamWriteFrame m ram area)
      (lo : sp.toNat-8 ≤ p.toNat) (hi : p.toNat+n ≤ sp.toNat+440) (off len : Nat)
      (fits : off+len ≤ bytes_l104b76.length) :
      StoreOk Extracted.programImage ram p n (0x104b76 + BitVec.ofNat 64 off) len :=
    ParseSignature.storeOk_of_codeRange (stackAt w lo hi)
      (fun x hx => Common.fnCode_subset_programImage x (code_l104b76 x hx)) fits
  have rd {ram : Ram} (w : RamWriteFrame m ram area) (i : Nat) (hi : i+8 ≤ 32) :
      LoadOk ram (src+BitVec.ofNat 64 i) 8 :=
    LoadOk.of_region (srcRead.of_frame w)
      (by rw [Ecdh.Output.outputOffset srcRead.low (by omega)]; omega)
      (by rw [Ecdh.Output.outputOffset srcRead.low (by omega)]; omega)
  have got {ram : Ram} (w : RamWriteFrame m ram area) {p : BitVec 64}
      (lo : 0x203dd0 ≤ p.toNat) (hi : p.toNat+8 ≤ 0x203e18) :
      memLoad ram p 64 = memLoad m p 64 := by
    apply w.memLoad_eq
    refine ⟨by change p.toNat+8 ≤ 2^64; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change p.toNat+8 ≤ sp.toNat-8 ∨ sp.toNat-8+448 ≤ p.toNat
    omega
  let b := Append.branchArgs a fr.rdi
  let c := Append.valueArgs b m src
  let d := Append.copyArgs c sp
  have used : memLoad m (sp+231) 8 = 0 := by
    have h := state.used
    change memLoad m (sp+104+127) 8 = 0 at h
    rwa [show sp+104+127 = sp+231 by bv_omega] at h
  have start := Append.branch (sp := sp) (src := fr.rdi) (code := Extracted.programImage) (congrArg (Value.get 64) rsp)
    (congrArg (Value.get 64) bx) (LoadOk.of_region work.readable (by omega) (by omega)) used
  have stores := Append.valueStores (a := b) (sp := sp) (src := src) (dst := dst)
    (code := Extracted.programImage) (m := m)
    (by append_values b c d; exact congrArg (Value.get 64) rsp) (by append_values b c d)
    (by append_values b c d; exact congrArg (Value.get 64) buf) (by append_values b c d)
    (rd w₀ 24 (by decide)) (store w₀ (by omega) (by omega) 4 5 (by decide))
    (rd w₁ 16 (by decide)) (w₁.memLoad_eq (withinData 16 (by decide)))
    (store w₁ (by omega) (by omega) 13 5 (by decide))
    (by simpa only [BitVec.add_zero] using rd w₂ 0 (by decide)) (rd w₂ 8 (by decide))
    (by simpa only [BitVec.add_zero] using w₂.memLoad_eq (k := 64) (withinData 0 (by decide)))
    (w₂.memLoad_eq (withinData 8 (by decide))) (store w₂ (by omega) (by omega) 25 5 (by decide))
    (store w₃ (by omega) (by omega) 30 4 (by decide))
    (store w₄ (by omega) (by omega) 38 8 (by decide))
  have call := Append.copyCall (a := c) (m := t) (sp := sp) (code := Extracted.programImage)
    (by append_values b c d; exact congrArg (Value.get 64) rsp)
    (ParseSignature.storeOk_of_codeRange (off := 21) (stackAt wt (by omega) (by omega))
      (fun x hx => Common.fnCode_subset_programImage x (code_l104c06 x hx)) (by decide))
    (LoadOk.of_region (gr1.of_frame wt) (Nat.le_refl _) (Nat.le_refl _))
    ((got wt (by decide) (by decide)).trans g1)
  have returnWord : memLoad u (sp-8) 64 = 0x104c21 := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have retRd := (stackAt (p := sp-8) (n := 8) wu (by omega) (by omega)).readable
  obtain ⟨out,run,copy,tag,_,rsp',kept⟩ := Verify.Hash.Update.memcpy (args := d) (mem := u)
    (dst := sp+272) (src := sp+104) (count := 168) (rsp := sp-8)
    (by append_values b c d) (by append_values b c d) (by append_values b c d) (by append_values b c d)
    (by append_values b c d; exact congrArg (Value.get 1) df)
    (stackAt wu (by omega) (by change _+168 ≤ _; omega)).readable
    (stackAt wu (by omega) (by change _+168 ≤ _; omega))
    (.inl (by change _+168 ≤ _; omega))
    (by apply RangeApart.of_offsets rfl (addr_sub _ _); decide)
    retRd (by rw [returnWord]; decide)
  have bxEnd : out.values[3] = d[3] := kept 3 (by decide)
  have bpEnd : out.values[5] = d[5] := kept 5 (by decide)
  have r12End : out.values[12] = d[12] := kept 12 (by decide)
  have r13End : out.values[13] = d[13] := kept 13 (by decide)
  have ctxEnd : out.values[14] = d[14] := kept 14 (by decide)
  have dfEnd : out.values[22] = d[22] := kept 22 (by decide)
  have mxEnd : out.values[39] = d[39] := kept 39 (by decide)
  have ftEnd : out.values[50] = d[50] := kept 50 (by decide)
  have fcEnd : out.values[51] = d[51] := kept 51 (by decide)
  simp only [b, c, d, Append.branchArgs, Append.valueArgs, Append.copyArgs, Vector.getElem_set,
    Nat.reduceEqDiff, ↓reduceIte] at bxEnd bpEnd r12End r13End ctxEnd dfEnd mxEnd ftEnd fcEnd
  have localFrame : RamWriteFrame m out.store area := by rw [copy]; exact finalFrame
  have total := writes.trans localFrame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,(by change fr.low.toNat ≤ sp.toNat-8; omega),
      (by change sp.toNat-8+448 ≤ fr.low.toNat+(fr.rsp.toNat-fr.low.toNat); omega)⟩)
  have high {off : Nat} (h : off ≤ 48) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 off) 64 =
      memLoad m (fr.rsp - BitVec.ofNat 64 off) 64 := by
    have sub : (fr.rsp-BitVec.ofNat 64 off).toNat = fr.rsp.toNat-off := by
      have n : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 off).toNat ≤ fr.rsp.toNat; omega),n]
    apply localFrame.memLoad_eq
    refine ⟨by change _+8 ≤ 2^64; omega,fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by change sp.toNat-8+448 ≤ _; omega)
  have rret : memLoad out.store fr.rsp 64 = fr.ret := by
    simpa only [BitVec.sub_zero] using (high (off := 0) (by decide)).trans (by simpa only [BitVec.sub_zero] using ret)
  have first : (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l104b63,a,m⟩,[]⟩ ⟨⟨.l104b76,b,m⟩,[]⟩ := .single (by
    change (program.runBlock _ _).next _ _ = _
    rw [start]
    rfl)
  have appended : (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l104b76,b,m⟩,[]⟩ ⟨⟨.l104c06,c,t⟩,[]⟩ := .single (by
    change (program.runBlock _ _).next _ _ = _
    rw [stores]
    rfl)
  have returned : out.tag = some ⟨64,0x104c21⟩ := returnWord ▸ tag
  refine ⟨out.values,out.store,first.trans (appended.trans (Verify.reachesOfCall call run returned)),
    ⟨?atoms,total,bxEnd,?widths⟩,ctxEnd,?state⟩
  case atoms =>
    simp only [Fn104970.frameAt,Fn104970.frameAtG5,Atom.All,Atom.Holds]
    exact ⟨by simp only [BitVec.sub_add_cancel] at rsp'; exact rsp', dfEnd.trans df,
      mxEnd.trans mx,ftEnd.trans ft,fcEnd.trans fc,
      (high (off := 48) (by decide)).trans sbx,(high (off := 40) (by decide)).trans s12,
      (high (off := 32) (by decide)).trans s13,(high (off := 24) (by decide)).trans s14,
      (high (off := 16) (by decide)).trans s15,(high (off := 8) (by decide)).trans sbp,
      rr.of_frame localFrame,rret,rl,stack.of_frame localFrame,room,align,gr2.of_frame localFrame,
      (got localFrame (by decide) (by decide)).trans g2, by omega,trivial⟩
  case widths =>
    intro _ ⟨i,hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact congrArg Value.width (bpEnd.trans bp)
    · exact congrArg Value.width (r12End.trans r12)
    · exact congrArg Value.width (r13End.trans r13)
  case state =>
    rw [copy]
    exact (Append.pushedState (sp := sp) state input (stackAt (p := dst) w₀ (by omega) (by omega)).readable).memCopy

end K256.Proofs.Signing.UpdateV
