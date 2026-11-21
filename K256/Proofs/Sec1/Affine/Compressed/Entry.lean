import K256.Proofs.Sec1.Affine.Uncompressed.Coordinate
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Sec1.LIR.Program
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

open K256.Proofs.Common.Field

def entrySaved (mem : Ram) (sp : Word) (args : Values Value Reg.count) : Ram :=
  let m1 := memStore mem (sp - 8) (Value.get 64 args[5])
  let m2 := memStore m1 (sp - 16) (Value.get 64 args[15])
  let m3 := memStore m2 (sp - 24) (Value.get 64 args[14])
  let m4 := memStore m3 (sp - 32) (Value.get 64 args[13])
  let m5 := memStore m4 (sp - 40) (Value.get 64 args[12])
  let m6 := memStore m5 (sp - 48) (Value.get 64 args[3])
  let m7 := memStore m6 (sp - 380) ((Value.get 64 args[2]).setWidth 32)
  let m8 := memStore m7 (sp - 352) (Value.get 64 args[7])
  m8

private theorem stackGuard {code : CodeMap} {m : Ram} {sp delta pc : Word} {n len : Nat}
    (hw : Writable code m (sp - 496) 496)
    (h : ((0 - delta) - (0 - 496)).toNat + n ≤ 496)
    (hc : ∀ x ∈ codeRange 0x1205b0 bytes_l1205b0, x ∈ code)
    (hp : (pc - 0x1205b0).toNat + len ≤ bytes_l1205b0.length) :
    StoreOk code m (sp - delta) n pc len := by
  have e := ParseSignature.storeOk_of_codeRange (hw.of_offsets (addr_sub _ _) (addr_sub _ _) h) hc hp
  have epc : 0x1205b0 + BitVec.ofNat 64 (pc - 0x1205b0).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rwa [epc] at e

private theorem coordRead {m : Ram} {p off : Word} (h : Readable m p 32)
    (b : off.toNat + 8 ≤ 32) : LoadOk m (p + off) 8 :=
  LoadOk.of_offsets h rfl (addr_self p) (by simpa only [show off - 0 = off from BitVec.sub_zero _] using b)

set_option maxHeartbeats 1500000 in
theorem entryCall (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp src : Word) (hsp : Value.get 64 args[4] = sp) (hsrc : Value.get 64 args[6] = src)
    (hcode : ∀ x ∈ codeRange 0x1205b0 bytes_l1205b0, x ∈ code)
    (hw : Writable code mem (sp - 496) 496) (hr : Readable mem src 32) :
    let saved := entrySaved mem sp args
    let a := bswapSpec (memLoad saved src 64)
    let b := bswapSpec (memLoad saved (src + 8) 64)
    let c := bswapSpec (memLoad saved (src + 16) 64)
    let d := bswapSpec (memLoad saved (src + 24) 64)
    ∃ callee, program.runBlock (dialect code) ⟨.l1205b0, args, mem⟩ =
      .call ⟨.l127d50, callee, memStore saved (sp - 496) (0x120653 : Word)⟩
        ⟨.l120653, #v[], rfl, some ⟨64, 0x120653⟩⟩ ∧
      callee[4] = ⟨64, sp - 496⟩ ∧ callee[7].get 64 = BitVec.ofNat 64 (Uncompressed.invalid a b c d).toNat ∧
      callee[12] = ⟨64, d &&& 0xfffffffffffff⟩ ∧
      callee[13] = ⟨64, shldResult 12 c d &&& 0xfffffffffffff⟩ ∧
      callee[14] = ⟨64, shldResult 24 b c⟩ ∧ callee[3] = ⟨64, shldResult 36 a b⟩ ∧
      callee[15] = ⟨64, a >>> 16⟩ ∧ callee[5] = ⟨64, 0xfffffffffffff⟩ ∧
      callee[22] = args[22] ∧ callee[39] = args[39] ∧ callee[50] = args[50] ∧ callee[51] = args[51] := by
  dsimp only
  refine ⟨?_, ?eval, ?post⟩
  case eval =>
    cfg_eval [hsp, hsrc]
    repeat' (
      refine Eq.trans (ite_eq_left ?_) ?_
      first
        | refine stackGuard (sp := sp) ?_ (by decide) hcode (by decide +kernel)
          repeat' apply Writable.memStore
          exact hw
        | apply LoadOk.of_region (b := src) (len := 32) _ (Nat.le_refl _) (by omega)
          repeat' apply Readable.memStore
          exact hr
        | apply coordRead (p := src) _ (by decide)
          repeat' apply Readable.memStore
          exact hr)
    rfl
  case post =>
    refine ⟨rfl, ?_, rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    change BitVec.setWidth 64 (BitVec.setWidth 8 (mergeGPR 8 _ _)) = _
    simp only [setWidth_mergeGPR8, Uncompressed.cmpAbove, orFlags, Option.getD_some, beq_iff_eq,
      decide_eq_true_eq, Uncompressed.invalid, entrySaved]
    exact Uncompressed.flagByte _ _

theorem entrySaved_frame (mem : Ram) (sp : Word) (args : Values Value Reg.count)
    (room : 496 ≤ sp.toNat) :
    RamWriteFrame mem (entrySaved mem sp args) [⟨(sp - 496).toNat, 496⟩] := by
  have slot (off : Word) (n : Nat) (h : n ≤ off.toNat ∧ off.toNat ≤ 496) :
      InRegions [⟨(sp - 496).toNat, 496⟩] (sp - off) n := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (sp - 496).toNat ≤ (sp - off).toNat ∧
      (sp - off).toNat + n ≤ (sp - 496).toNat + 496 ∧ (sp - off).toNat + n ≤ 2^64
    bv_omega
  unfold entrySaved
  repeat' (refine RamWriteFrame.memStore ?_ _ (slot _ _ (by decide)))
  exact RamWriteFrame.refl _ _

theorem entrySaved_load {mem : Ram} (sp src : Word) (args : Values Value Reg.count)
    (room : 496 ≤ sp.toNat) (hr : Readable mem src 32)
    (hap : src.toNat + 32 ≤ (sp - 496).toNat ∨ (sp - 496).toNat + 496 ≤ src.toNat)
    (off : Word) (bound : off.toNat + 8 ≤ 32) :
    memLoad (entrySaved mem sp args) (src + off) 64 = memLoad mem (src + off) 64 := by
  have hs := toNat_of_offsets (a := src + off) rfl (addr_self src) hr.low
    (n := 8) (by simpa only [show off - 0 = off from BitVec.sub_zero _] using bound)
  rw [show off - 0 = off from BitVec.sub_zero _] at hs
  apply (entrySaved_frame mem sp args room).memLoad_eq
  have hl := hr.low
  refine ⟨by omega, fun r h => ?_⟩
  rcases List.mem_singleton.mp h with rfl
  change _ ≤ (sp-496).toNat ∨ (sp-496).toNat + 496 ≤ _
  omega

end K256.Proofs.Sec1.Affine.Compressed
