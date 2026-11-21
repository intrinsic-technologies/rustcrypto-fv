import K256.Proofs.Sec1.LIR.Fn1205b0.Frame
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Sec1.Affine.Compressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR

theorem returnBlock (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp dst : BitVec 64) (flag : BitVec 8)
    (hsp : Value.get 64 args[4] = sp - 0x1e8)
    (hdst : Value.get 64 args[3] = dst)
    (hflag : (Value.get 64 args[0]).setWidth 8 = flag)
    (hwrite : StoreOk code mem (dst + 88) 1 0x120f13 3)
    (hread : ∀ off : Nat, off ≤ 48 → (off = 0 ∨ 8 ≤ off) → LoadOk (memStore mem (dst + 88) flag) (sp - BitVec.ofNat 64 off) 8)
    (htarget : (memLoad (memStore mem (dst + 88) flag) sp 64).toNat < 2^32) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l120f13, args, mem⟩, []⟩ out ∧
      out.store = memStore mem (dst + 88) flag ∧
      out.tag = some ⟨64, memLoad out.store sp 64⟩ ∧
      out.values[0] = ⟨64, dst⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
      out.values[3] = ⟨64, memLoad out.store (sp - 48) 64⟩ ∧
      out.values[12] = ⟨64, memLoad out.store (sp - 40) 64⟩ ∧
      out.values[13] = ⟨64, memLoad out.store (sp - 32) 64⟩ ∧
      out.values[14] = ⟨64, memLoad out.store (sp - 24) 64⟩ ∧
      out.values[15] = ⟨64, memLoad out.store (sp - 16) 64⟩ ∧
      out.values[5] = ⟨64, memLoad out.store (sp - 8) 64⟩ ∧
      out.values[22] = args[22] ∧ out.values[39] = args[39] ∧
      out.values[50] = args[50] ∧ out.values[51] = args[51] := by
  let m := memStore mem (dst + 88) flag
  change (memLoad m sp 64).toNat < 2^32 at htarget
  have hmem : memStore mem (dst + 88) flag = m := rfl
  have addr440 : sp - 0x1e8 + 440 = sp - 48 := by bv_omega
  have r48 : LoadOk m (sp - 48) 8 := hread 48 (by decide) (by decide)
  have addr448 : sp - 0x1e8 + 448 = sp - 40 := by bv_omega
  have r40 : LoadOk m (sp - 40) 8 := hread 40 (by decide) (by decide)
  have addr456 : sp - 0x1e8 + 456 = sp - 32 := by bv_omega
  have r32 : LoadOk m (sp - 32) 8 := hread 32 (by decide) (by decide)
  have addr464 : sp - 0x1e8 + 464 = sp - 24 := by bv_omega
  have r24 : LoadOk m (sp - 24) 8 := hread 24 (by decide) (by decide)
  have addr472 : sp - 0x1e8 + 472 = sp - 16 := by bv_omega
  have r16 : LoadOk m (sp - 16) 8 := hread 16 (by decide) (by decide)
  have addr480 : sp - 0x1e8 + 480 = sp - 8 := by bv_omega
  have r8 : LoadOk m (sp - 8) 8 := hread 8 (by decide) (by decide)
  have addr488 : sp - 0x1e8 + 488 = sp := by bv_omega
  have r0 : LoadOk m (sp) 8 := by
    have h := hread 0 (by decide) (by decide)
    change LoadOk m (sp - 0) 8 at h
    exact (show sp - (0 : BitVec 64) = sp from BitVec.sub_zero _) ▸ h
  have addr496 : sp - 0x1e8 + 496 = sp + 8 := by bv_omega
  refine ⟨?_, Program.Exec.done ?eval, ?rest⟩
  case eval =>
    unfold Program.step
    cfg_eval
    simp only [hdst, hsp, hflag, hwrite, hmem, addr440, addr448, addr456, addr464, addr472, addr480, addr488, addr496, r48, r40, r32, r24, r16, r8, r0, htarget, and_self, ↓reduceIte]
    rfl
  case rest => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem finish {code : CodeMap} (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (flag : BitVec 8) (hcode : ∀ x ∈ codeRange 0x120f13 bytes_l120f13, x ∈ code)
    (hframe : Atom.All code args mem (Fn1205b0.frameAt .l120f13 fr))
    (hflag : (Value.get 64 args[0]).setWidth 8 = flag)
    (hw : Writable code mem fr.rdi 89)
    (hap : fr.rdi.toNat + 89 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l120f13, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn1205b0.doneAt fr) ∧
      out.values[0] = ⟨64, fr.rdi⟩ ∧
      out.store = memStore mem (fr.rdi + 88) flag ∧ memLoad out.store (fr.rdi + 88) 8 = flag := by
  simp only [Fn1205b0.frameAt, Fn1205b0.frameAtG2, Atom.All, Atom.Holds] at hframe
  obtain ⟨hsp, hdf, hdi, hmx, hft, hfc, _, h3, h12, h13, h14, h15, h5, hslot,
    hret, hlow, hstack, hroom, _, _⟩ := hframe
  let m := memStore mem (fr.rdi + 88) flag
  have dn : (fr.rdi + 88).toNat = fr.rdi.toNat + 88 := by
    have := hw.readable.low
    rw [BitVec.toNat_add]
    change (_ + 88) % 2^64 = _
    omega
  have guard : StoreOk code mem (fr.rdi + 88) 1 0x120f13 3 :=
    ParseSignature.storeOk_of_codeRange (off := 0) (hw.sub (by omega) (by omega)) hcode (by decide)
  have sn (off : Nat) (bound : off ≤ 0x418) :
      (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
    have hn : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le, hn]
    rw [BitVec.le_def, hn]
    omega
  have preserved (off : Nat) (bound : off ≤ 48) :
      memLoad m (fr.rsp - BitVec.ofNat 64 off) 64 = memLoad mem (fr.rsp - BitVec.ofNat 64 off) 64 := by
    apply memLoad_memStore_of_rangeApart
    apply RangeApart.of_toNat <;> have := hw.readable.low <;> have := sn off (by omega) <;> have := hslot.low <;> omega
  have ret : memLoad m fr.rsp 64 = fr.ret := by
    have e := preserved 0 (by decide)
    change memLoad m (fr.rsp - 0) 64 = memLoad mem (fr.rsp - 0) 64 at e
    rw [show fr.rsp - 0 = fr.rsp from BitVec.sub_zero _] at e
    exact e.trans hret
  have rs (off : Nat) (bound : off ≤ 48) (h : off = 0 ∨ 8 ≤ off) :
      LoadOk m (fr.rsp - BitVec.ofNat 64 off) 8 := by
    rcases h with rfl | h
    · change LoadOk m (fr.rsp - 0) 8
      rw [show fr.rsp - 0 = fr.rsp from BitVec.sub_zero _]
      have r := hslot.memStore (fr.rdi + 88) flag
      exact ⟨r.low, r.present⟩
    · have hsn := sn off (by omega)
      have hsb := sn 0x418 (by decide)
      apply LoadOk.of_region (hstack.readable.memStore (fr.rdi + 88) flag)
      · change (fr.rsp - BitVec.ofNat 64 0x418).toNat ≤ _
        omega
      · change _ ≤ (fr.rsp - BitVec.ofNat 64 0x418).toNat + 0x418
        omega
  obtain ⟨out, he, hs, ht, ha, hrsp, hb, hr12, hr13, hr14, hr15, hbp, z, mx, ft, fc⟩ :=
    returnBlock code args mem fr.rsp fr.rdi flag (congrArg (Value.get 64) hsp)
      (congrArg (Value.get 64) hdi) hflag guard rs (ret ▸ hlow)
  change out.store = m at hs
  rw [hs] at ht hb hr12 hr13 hr14 hr15 hbp
  have saved (off : Nat) (bound : off ≤ 48) (v : BitVec 64)
      (h : memLoad mem (fr.rsp - BitVec.ofNat 64 off) 64 = v) :
      (⟨64, memLoad m (fr.rsp - BitVec.ofNat 64 off) 64⟩ : Value) = ⟨64,v⟩ :=
    congrArg (Value.mk 64) ((preserved off bound).trans h)
  refine ⟨out, he, ht.trans (congrArg (fun x => some (Value.mk 64 x)) ret), ?_,
    ha, hs, hs ▸ memLoad_memStore_same _ _ _ (by decide) (by decide)⟩
  exact ⟨hrsp, z.trans hdf, hb.trans (saved 48 (by decide) _ h3),
    hbp.trans (saved 8 (by decide) _ h5), hr12.trans (saved 40 (by decide) _ h12),
    hr13.trans (saved 32 (by decide) _ h13), hr14.trans (saved 24 (by decide) _ h14),
    hr15.trans (saved 16 (by decide) _ h15), mx.trans hmx, ft.trans hft, fc.trans hfc, trivial⟩

end K256.Proofs.Sec1.Affine.Compressed
