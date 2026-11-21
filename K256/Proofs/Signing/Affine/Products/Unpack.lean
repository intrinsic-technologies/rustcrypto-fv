import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Affine.Memory
import K256.Proofs.Signing.Affine.Products.Frame
import K256.Proofs.Signing.Affine.Products.Input
import K256.Proofs.Sec1.Affine.Uncompressed.Coordinate

namespace K256.Proofs.Signing.Affine

open K256.Proofs.Generate.Generator.Affine
open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC
open K256.Proofs.Common.Tactic
open K256.Proofs.Sec1.Affine.Uncompressed (unpack unpack_value unpack_repr)

set_option maxHeartbeats 800000 in
theorem unpackInverse {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (s : CallState .l10eda1 fr a m) (h : Coordinates m fr.rsi x y z) (hi : InverseRegisters a z) :
    ∃ b m', program.runBlock (dialect Extracted.programImage) ⟨.l10eda1, a, m⟩ =
      .call ⟨.l10e4c0, b, m'⟩ productReturn ∧ ProductInput fr b m' x y z := by
  have before : Atom.All Extracted.programImage a m (Fn10fe50.frameAt .l10eda1 fr) := s.atoms
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
  have getSp : a[4].get 64 = q := congrArg (Value.get 64) sp
  have getSrc : a[14].get 64 = fr.rsi := congrArg (Value.get 64) src
  have get0 : a[15].get 64 = t[0] := congrArg (Value.get 64) h0
  have get1 : a[12].get 64 = t[1] := congrArg (Value.get 64) h1
  have get2 : a[13].get 64 = t[2] := congrArg (Value.get 64) h2
  have get3 : a[5].get 64 = t[3] := congrArg (Value.get 64) h3
  have getFlag : a[0].get 64 = 1 := congrArg (Value.get 64) flag
  have flagSet : (!(1 : BitVec 8) == 0) = true := rfl
  have oneMask (x : Word) : 18446744073709551615 &&& x = x :=
    BitVec.allOnes_and
  let w := unpack t[3] t[2] t[1] t[0]
  let out :=
    let scratch := memStore m q (1 : BitVec 8)
    let scratch := memStore scratch q w[0]
    let scratch := memStore scratch (q + 8) w[1]
    let scratch := memStore scratch (q + 16) w[2]
    let scratch := memStore scratch (q + 24) ((0xfffffffffffff : Word) &&& shldResult 36 t[3] t[2])
    let scratch := memStore scratch (q + 32) w[4]
    memStore scratch (q - 8) (0x10ee37 : Word)
  refine ⟨?resultRegs, ?resultRam, ?block, ?input⟩
  case block =>
    arithmetic_segment using code_l10eda1 [getSp, getSrc, get0, get1, get2, get3,
      getFlag, src, testFlags, flagSet, oneMask, ite_true]
  case input =>
    change ProductInput fr _ out x y z
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
    refine ⟨?_, ?_, rfl, ?_, rfl, ?_, rfl, ?_, coordinatesAfterProductScratch h frame bounds s.srcAbove s.source, ?_⟩
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
    · refine ⟨w, ?_, unpack_repr _ _ _ _ (inverse z) ((unpack_value _ _ _ _).trans ht) (by decide)⟩
      change WordsAt out q 64 w
      dsimp only [out]
      lifted_word_reads []
      all_goals first | lifted_word_eq [] | exact BitVec.and_comm _ _

end K256.Proofs.Signing.Affine
