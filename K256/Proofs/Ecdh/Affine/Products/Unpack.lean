import K256.Proofs.Common.Tactic
import K256.Proofs.Ecdh.Affine.Products.Input
import K256.Proofs.Ecdh.Affine.Memory
import K256.Proofs.Sec1.Affine.Uncompressed.Coordinate

namespace K256.Proofs.Ecdh.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator.Affine
open Standards.SECG.ECC

open K256.Proofs.Common.Tactic
open K256.Proofs.Sec1.Affine.Uncompressed (unpack unpack_value unpack_repr)

set_option maxHeartbeats 800000 in
theorem unpackLoadedInverse {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (s : CallState .l10eda1 fr a m) (h : Coordinates m fr.rsi x y z) (hi : LoadedInverse a z) :
    ∃ b m', program.runBlock (dialect Extracted.programImage) ⟨.l10eda1, a, m⟩ =
      .call ⟨.l10e4c0, b, m'⟩ productReturn ∧ ProductCallInput fr b m' x y z := by
  have before := s.atoms
  obtain ⟨sp, _, _, src, _, _, _, _, _, _, _, _, _, _, _, _, win, room, _, _⟩ := s.atoms
  change a[14] = ⟨64, fr.rsi⟩ at src
  change Writable Extracted.programImage m (fr.rsp - 976) 976 at win
  change fr.low.toNat + 976 ≤ fr.rsp.toNat at room
  obtain ⟨t, h0, h1, h2, h3, ht⟩ := hi.words
  have flag := hi.flag
  let q := fr.rsp - (232 : Word)
  change a[4] = ⟨64, q⟩ at sp
  have start : q - 8 = fr.rsp + (0 - 240) := by dsimp only [q]; bv_omega
  have window : Writable Extracted.programImage m (q - 8) 48 :=
    win.of_offsets start (addr_sub fr.rsp 976) (by decide)
  have qNat : q.toNat = fr.rsp.toNat - 232 := sub_toNat (by omega) 232 (by decide)
  have startNat : (q - 8).toNat = fr.rsp.toNat - 240 := by
    rw [show q - 8 = fr.rsp - 240 by dsimp only [q]; bv_omega]
    exact sub_toNat (by omega) 240 (by decide)
  have high := s.high
  have getSp : a[4].get 64 = q := congrArg (Value.get 64) sp
  have getSrc : a[14].get 64 = fr.rsi := congrArg (Value.get 64) src
  have get0 : a[15].get 64 = t[0] := congrArg (Value.get 64) h0
  have get1 : a[12].get 64 = t[1] := congrArg (Value.get 64) h1
  have get2 : a[13].get 64 = t[2] := congrArg (Value.get 64) h2
  have get3 : a[5].get 64 = t[3] := congrArg (Value.get 64) h3
  let f := choiceBit z
  have getFlag : a[0].get 64 = f := congrArg (Value.get 64) flag
  have fWidth : BitVec.setWidth 64 (BitVec.setWidth 8 f) = f := by
    by_cases hz : z.val = 0 <;> simp only [f, choiceBit, hz, ite_true, ite_false] <;> rfl
  let byte := f.setWidth 8
  let selected (i : Fin 4) :=
    if (byte == 0) = false then t[i] else 0
  let mask := -(byte.setWidth 64)
  let lowMask := (0xfffffffffffff : Word) &&& mask
  let w : Limbs := #v[selected 0 &&& lowMask, shldResult 12 (selected 1) (selected 0) &&& lowMask,
    shldResult 24 (selected 2) (selected 1) &&& lowMask,
    lowMask &&& shldResult 36 (selected 3) (selected 2),
    mask &&& (selected 3 >>> 16)]
  let out :=
    let scratch := memStore m q byte
    let scratch := memStore scratch q w[0]
    let scratch := memStore scratch (q + 8) w[1]
    let scratch := memStore scratch (q + 16) w[2]
    let scratch := memStore scratch (q + 24) w[3]
    let scratch := memStore scratch (q + 32) w[4]
    memStore scratch (q - 8) (0x10ee37 : Word)
  refine ⟨?resultRegs, out, ?block, ?input⟩
  case block =>
    generate_block [getSp, getSrc, get0, get1, get2, get3, getFlag, src]
    segment_words [getSp, getSrc, get0, get1, get2, get3, getFlag, src, testFlags]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using code_l10eda1 | assumption)
    rfl
  case input =>
    let areas : List MemoryRegion := [⟨(q - 8).toNat, 48⟩]
    have bounds : ProductScratch fr areas := by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      change fr.rsp.toNat - 976 ≤ (q - 8).toNat ∧
        (q - 8).toNat + 48 ≤ fr.rsp.toNat - 48
      omega
    have frame : RamWriteFrame m out areas := by
      dsimp only [out, areas]
      slot_state region
    have spEq : q - 8 = fr.rsp - 240 := by dsimp only [q]; bv_omega
    have dstEq : q + 88 = fr.rsp - 144 := by dsimp only [q]; bv_omega
    refine ⟨?_, ?_, rfl, ?_, rfl, ?_, congrArg (Value.mk 64) fWidth, ?_,
      coordinatesAfterScratch h frame bounds s.srcAddr high, ?_⟩
    · refine s.afterProductScratch (l' := .l10ee37) before rfl frame bounds ?_
      intro ⟨i, _⟩ hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact sp.symm | exact src.symm
    · exact congrArg (fun p => Value.mk 64 p) spEq
    · exact congrArg (fun p => Value.mk 64 p) dstEq
    · exact congrArg (fun p => Value.mk 64 p) dstEq
    · rw [← spEq]
      dsimp only [out]
      certify_product reads [] model []
    · refine ⟨w, ?_, ?_⟩
      · change WordsAt out q 64 w
        dsimp only [out]
        certify_product reads [] model []
      · intro hz
        have chosen (i : Fin 4) : selected i = t[i] := by
          simp only [selected, byte, f, choiceBit, hz, ite_false]
          rfl
        have maskSet : mask = BitVec.allOnes 64 := by
          simp only [mask, byte, f, choiceBit, hz, ite_false]
          rfl
        have packed : w = unpack t[3] t[2] t[1] t[0] := by
          have maskComm (v : Word) : (0xfffffffffffff : Word) &&& v = v &&& 0xfffffffffffff :=
            BitVec.and_comm _ _
          simp only [w, lowMask, chosen, maskSet, BitVec.allOnes_and,
            unpack, maskComm] <;> rfl
        rw [packed]
        exact unpack_repr _ _ _ _ (inverse z) ((unpack_value _ _ _ _).trans (ht hz)) (by decide)

end K256.Proofs.Ecdh.Affine
