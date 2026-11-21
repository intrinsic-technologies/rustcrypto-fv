import K256.Proofs.Sec1.Affine.Compressed.Emit.Block
import K256.Proofs.Sec1.Affine.Compressed.Return
import K256.Proofs.Sec1.Affine.Compressed.Choice

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR K256.Proofs.Common.Field K256.Proofs.Sec1.Serialize.Coordinates

theorem emitCall {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code) : EmitCall code := by
  intro fr args mem xs xOK sqrtOK want x y env body sel hx
  let sp := workSP fr
  let dst := fr.rdi
  let flag := BitVec.ofNat 8 (xOK && sqrtOK).toNat
  let st := stagePoint mem sp (savedX mem sp)
  let cp := memCopy st dst (sp+352) 88
  let w := memStore cp (sp-8) (0x120f13 : Word)
  let slot : MemoryRegion := ⟨(sp-9).toNat, 9⟩
  let payload : MemoryRegion := ⟨(sp+352).toNat, 81⟩
  let dest : MemoryRegion := ⟨dst.toNat, 89⟩
  let regions := [slot, payload, dest]
  have atoms := body.atoms
  simp only [Fn1205b0.frameAt, Fn1205b0.frameAtG2, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, mx, ft, fc, hd, hb, h12, h13, h14, h15, h5, hr, hret, hlow, stack, room, align, _⟩ := atoms
  have subN (k : Nat) (h : k ≤ 1048) : (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have hk : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le, hk]
    rw [BitVec.le_def, hk]
    omega
  have spN : sp.toNat = fr.rsp.toNat - 488 := subN 488 (by decide)
  have addr (k : Nat) (h : k ≤ 488) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt]
    have := fr.rsp.isLt
    omega
  have n9 : (sp-9).toNat = fr.rsp.toNat - 497 := by
    rw [show sp-9 = fr.rsp - 497 by dsimp only [sp,workSP]; bv_omega]
    exact subN 497 (by decide)
  have n8 : (sp-8).toNat = fr.rsp.toNat - 496 := by
    rw [show sp-8 = fr.rsp - 496 by dsimp only [sp,workSP]; bv_omega]
    exact subN 496 (by decide)
  have n352 : (sp+352).toNat = sp.toNat+352 := addr 352 (by decide)
  have sLow := hr.low
  have dLow := body.output.readable.low
  change dst.toNat + 89 ≤ 2^32 at dLow
  have nd : (dst+88).toNat = dst.toNat+88 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change dst.toNat+88 < 2^64; omega)]
    rfl
  have apart := env.apart
  change dst.toNat + 89 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ dst.toNat at apart
  have regionStart : (fr.rsp-1048).toNat = fr.rsp.toNat-1048 := subN 1048 (by decide)
  have win : Writable code mem (sp-8) 448 := stack.sub (by omega) (by omega)
  have dstSlot : memLoad mem (sp + 136) 64 = dst := by
    rw [show sp + 136 = fr.rsp - 352 by dsimp only [sp,workSP]; bv_omega]
    exact hd
  obtain ⟨next, call, csp, cb, cv, cdf, cmx, cft, cfc⟩ := outputCall code args mem sp dst
    (congrArg (Value.get 64) rsp) (congrArg (Value.get 1) df) dstSlot win body.output (by omega)
    (fun e h => cover e (code_l120e9b e h))
  have inside (k len : Nat) (h : 352 ≤ k) (h' : k + len ≤ 433) :
      InRegions regions (sp + BitVec.ofNat 64 k) len := by
    refine ⟨payload, by simp [regions], ?_⟩
    change (sp+352).toNat ≤ _ ∧ _ ≤ (sp+352).toNat + 81 ∧ _
    have := addr k (by omega)
    omega
  have sf : RamWriteFrame mem st regions := by
    dsimp only [st, stagePoint]
    iterate 6
      apply RamWriteFrame.memStore
      case hin => exact inside _ _ (by decide) (by decide)
    exact RamWriteFrame.refl _ _
  have cpf : RamWriteFrame mem cp regions :=
    sf.memStore _ ⟨dest, by simp [regions], Nat.le_refl _, by change dst.toNat + 88 ≤ dst.toNat + 89; omega, by change dst.toNat + 88 ≤ 2^64; omega⟩
  have slotIn : InRegion slot (sp-8) 8 := by
    change (sp-9).toNat ≤ _ ∧ _ ≤ (sp-9).toNat+9 ∧ _
    omega
  have wf : RamWriteFrame mem w regions := cpf.memStore _ ⟨slot, List.mem_cons_self, slotIn⟩
  have psh : RamWriteFrame cp w [slot] := (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_cons_self, slotIn⟩
  have one : sp-8-1 = sp-9 := by bv_omega
  have scratch : Writable code w (sp-8-1) 1 := by
    rw [one]
    exact (stack.sub (by omega) (by omega)).of_frame wf
  have t : memLoad w (sp-8) 64 = 0x120f13 := memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨o, ch, tag, osp, ax, writes, keep⟩ := Serialize.choiceBlock (sp := sp-8)
    (fun e h => cover e (code_l127d50 e h)) (congrArg (Value.get 64) csp) scratch
    ((win.readable.sub (Nat.le_refl _) (by omega)).of_frame wf) (by rw [t]; decide)
  rw [one] at writes
  have cf : RamWriteFrame cp o.store [slot] := psh.trans writes (by
    intro r hr'
    rcases List.mem_singleton.mp hr' with rfl
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, by change (sp-9).toNat + 1 ≤ (sp-9).toNat + 9; omega⟩)
  have ofr := cpf.trans cf (by
    intro r hr'
    rcases List.mem_singleton.mp hr' with rfl
    exact ⟨slot, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩)
  have same (k : Nat) (hk : k ≤ 48 ∨ k = 352) :
      memLoad o.store (fr.rsp - BitVec.ofNat 64 k) 64 = memLoad mem (fr.rsp - BitVec.ofNat 64 k) 64 := by
    apply ofr.memLoad_eq
    have nk := subN k (by omega)
    refine ⟨by change _ + 8 ≤ 2^64; omega, ?_⟩
    intro r h
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl
    · change _ + 8 ≤ (sp-9).toNat ∨ (sp-9).toNat + 9 ≤ _
      omega
    · change _ + 8 ≤ (sp+352).toNat ∨ (sp+352).toNat + 81 ≤ _
      omega
    · change _ + 8 ≤ dst.toNat ∨ dst.toNat + 89 ≤ _
      omega
  have sameRet := same 0 (by decide)
  change memLoad o.store (fr.rsp-0) 64 = memLoad mem (fr.rsp-0) 64 at sameRet
  rw [show fr.rsp - 0 = fr.rsp from BitVec.sub_zero _] at sameRet
  rw [BitVec.sub_add_cancel] at osp
  have finAtoms : Atom.All code o.values o.store (Fn1205b0.frameAt .l120f13 fr) :=
    ⟨osp, (keep 22 (by decide)).trans (cdf.trans df), (keep 3 (by decide)).trans cb,
      (keep 39 (by decide)).trans (cmx.trans mx), (keep 50 (by decide)).trans (cft.trans ft),
      (keep 51 (by decide)).trans (cfc.trans fc), (same 352 (by decide)).trans hd,
      (same 48 (by decide)).trans hb, (same 40 (by decide)).trans h12, (same 32 (by decide)).trans h13,
      (same 24 (by decide)).trans h14, (same 16 (by decide)).trans h15, (same 8 (by decide)).trans h5,
      hr.of_frame ofr, sameRet.trans hret, hlow, stack.of_frame ofr, room, align, trivial⟩
  have outFlag : (o.values[0].get 64).setWidth 8 = flag := by
    rw [ax, Value.get_mk, cv]
    dsimp only [sp]
    rw [body.valid, sel.flag]
    cases xOK <;> cases sqrtOK <;> rfl
  obtain ⟨out, e, ot, oa, orax, os, valid⟩ := finish fr _ _ flag (fun e h => cover e (code_l120f13 e h))
    finAtoms outFlag (body.output.of_frame ofr) apart
  have run : program.Exec (dialect code) ⟨⟨.l127d50,next,w⟩,[]⟩ o :=
    .done (by simp only [Program.step, ch, Transfer.next])
  have path := reaches_call call run (tag.trans (congrArg (fun v => some (Value.mk 64 v)) t))
  refine ⟨out, Program.Exec.of_sem (path.exec e.sem), ot, oa, orax, ?_, valid, ?_⟩
  · rw [os]
    apply RamWriteFrame.memStore
    · apply (RamWriteFrame.refl _ _).trans ofr
      intro r h
      simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl|rfl|rfl
      · refine ⟨fr.region, List.mem_cons_self, ?_, ?_⟩
        change fr.low.toNat ≤ (sp-9).toNat
        omega
        change (sp-9).toNat+9 ≤ fr.low.toNat + (fr.rsp.toNat-fr.low.toNat)
        omega
      · refine ⟨fr.region, List.mem_cons_self, ?_, ?_⟩
        change fr.low.toNat ≤ (sp+352).toNat
        omega
        change (sp+352).toNat+81 ≤ fr.low.toNat + (fr.rsp.toNat-fr.low.toNat)
        omega
      · exact ⟨dest, by simp [dest,dst], Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨dest, by simp [dest,dst], ?_⟩
      change dst.toNat ≤ (dst+88).toNat ∧ (dst+88).toNat+1 ≤ dst.toNat+89 ∧ (dst+88).toNat+1 ≤ 2^64
      omega
  · intro ok
    obtain ⟨xtrue,ytrue⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨ys, hy, yr⟩ := sel.repr ytrue
    have staged := stagedAffine mem sp _ ys x y 8 (body.x ▸ hx xtrue) yr hy
    apply (copiedAffine (dst := dst) staged).of_copy
    intro off width inside'
    rw [os]
    have hn : (dst+BitVec.ofNat 64 off).toNat = dst.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
    change memLoad (memStore o.store (dst+88) flag) (dst+BitVec.ofNat 64 off) width = memLoad cp _ width
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_toNat (by change _ + 1 ≤ 2^64; omega) (by omega) (Or.inr (by omega)))]
    apply cf.memLoad_eq
    refine ⟨by omega, ?_⟩
    intro r hr'
    rcases List.mem_singleton.mp hr' with rfl
    change _ ≤ (sp-9).toNat ∨ (sp-9).toNat + 9 ≤ _
    omega

end K256.Proofs.Sec1.Affine.Compressed
