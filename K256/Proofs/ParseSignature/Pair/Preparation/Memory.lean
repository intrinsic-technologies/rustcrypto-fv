import K256.Proofs.ParseSignature.Pair.Frame
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.ParseSignature.Pair

open K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

variable {fr : Activation}

abbrev topWrites (fr : Activation) := [buffer (fr.rsp - 192) 192]

theorem topWritesWithin (room : fr.low.toNat + 560 ≤ fr.rsp.toNat) :
    RegionsWithin (topWrites fr) [fr.region] := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  change fr.low.toNat ≤ (fr.rsp - 192).toNat ∧
    (fr.rsp - 192).toNat + 192 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
  rw [show (fr.rsp - 192).toNat = _ from stackSub_toNat room 192 (by decide)]
  omega

theorem topWordFrame {old m : Ram} (room : fr.low.toNat + 560 ≤ fr.rsp.toNat)
    (frame : RamWriteFrame old m (topWrites fr)) (off : Nat) (v : BitVec 64)
    (ho : off ≤ 192) (hw : 8 ≤ off) :
    RamWriteFrame old (memStore m (fr.rsp - BitVec.ofNat 64 off) v) (topWrites fr) := by
  apply frame.memStore
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  change (fr.rsp - 192).toNat ≤ _ ∧ _ + 8 ≤ (fr.rsp - 192).toNat + 192 ∧ _ + 8 ≤ 2^64
  rw [stackSub_toNat room off (by omega), show (fr.rsp - 192).toNat = _ from stackSub_toNat room 192 (by decide)]
  have := fr.rsp.isLt
  omega

theorem stackWordWritable {code : CodeMap} {m : Ram}
    (win : Writable code m (fr.rsp - 560) 560) (off : Nat) (ho : off ≤ 560) (hw : 8 ≤ off) :
    Writable code m (fr.rsp - BitVec.ofNat 64 off) 8 := by
  apply win.of_offsets (addr_sub _ _) (addr_sub _ _)
  change ((0 - BitVec.ofNat 64 off) - (0 - 560) : BitVec 64).toNat + 8 ≤ 560
  rw [show (0 - BitVec.ofNat 64 off) - (0 - 560) = (560 : BitVec 64) - BitVec.ofNat 64 off by bv_omega]
  have h : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h]; exact ho), h]
  change 560 - off + 8 ≤ 560
  omega

theorem inputWord {m : Ram} (room : fr.low.toNat + 560 ≤ fr.rsp.toNat)
    (hr : Readable fr.original fr.rsi 64) (hin : Outside [callStack fr] fr.rsi 64)
    (frame : RamWriteFrame fr.original m [fr.region]) (off : Nat) (ho : off + 8 ≤ 64) :
    let a := fr.rsi + BitVec.ofNat 64 off
    LoadOk m a 8 ∧ memLoad m a 64 = memLoad fr.original a 64 := by
  intro a
  have low := hr.low
  have ha : a.toNat = fr.rsi.toNat + off := by
    dsimp only [a]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨LoadOk.of_region (hr.of_frame frame) (by rw [ha]; omega) (by rw [ha]; omega),
    frame.memLoad_eq ?_⟩
  have apart := hin.2 _ (List.mem_singleton_self _)
  change fr.rsi.toNat + 64 ≤ fr.low.toNat ∨ fr.low.toNat +
    (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rsi.toNat at apart
  refine ⟨by rw [ha]; omega, fun r h => ?_⟩
  obtain rfl := List.mem_singleton.mp h
  change a.toNat + 8 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ a.toNat
  rw [ha]
  omega

abbrev putScalar (fr : Activation) (m : Ram) (src ret : BitVec 64) : Ram :=
  let m := memStore m (fr.rsp - 88) (memLoad fr.original (src + 24) 64)
  let m := memStore m (fr.rsp - 96) (memLoad fr.original (src + 16) 64)
  let m := memStore m (fr.rsp - 104) (memLoad fr.original (src + 8) 64)
  let m := memStore m (fr.rsp - 112) (memLoad fr.original src 64)
  memStore m (fr.rsp - 192) ret

theorem stackWordKeep (fr : Activation)
    (m : Ram) (off target : Nat) (v : BitVec 64) (ho : off ≤ 560) (ht : target ≤ 560)
    (hd : target + 8 ≤ off ∨ off + 8 ≤ target) :
    memLoad (memStore m (fr.rsp - BitVec.ofNat 64 off) v) (fr.rsp - BitVec.ofNat 64 target) 64 =
      memLoad m (fr.rsp - BitVec.ofNat 64 target) 64 := by
  apply memLoad_memStore_of_rangeApart
  apply RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _)
  have diff (a b : Nat) (ha : a ≤ 560) (hb : b ≤ 560) (gap : a + 8 ≤ b ∨ b + 8 ≤ a) :
      8 ≤ ((-BitVec.ofNat 64 a) - (-BitVec.ofNat 64 b)).toNat := by
    rw [show -BitVec.ofNat 64 a - -BitVec.ofNat 64 b = BitVec.ofNat 64 b - BitVec.ofNat 64 a by bv_omega]
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega)]
    omega
  exact ⟨diff target off ht ho hd, diff off target ho ht hd.symm⟩

theorem putScalar_keep (fr : Activation) (m : Ram)
    (src ret : BitVec 64) (off : Nat) (ho : off ≤ 560)
    (hcopy : off + 8 ≤ 88 ∨ 112 + 8 ≤ off)
    (hret : off + 8 ≤ 192 ∨ 192 + 8 ≤ off) :
    memLoad (putScalar fr m src ret) (fr.rsp - BitVec.ofNat 64 off) 64 =
      memLoad m (fr.rsp - BitVec.ofNat 64 off) 64 := by
  simp (disch := omega) only [putScalar, stackWordKeep fr, BitVec.ofNat_eq_ofNat]

theorem putScalar_words (fr : Activation) (m : Ram)
    (src ret : BitVec 64) (i : Nat) (hi : i < 4) :
    scalarWord (putScalar fr m src ret) (sp fr + 72) i = scalarWord fr.original src i := by
  have same (m : Ram) (a v : BitVec 64) : memLoad (memStore m a v) a 64 = v :=
    memLoad_memStore_same m a v (by decide) (by decide)
  have values : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have at24 : sp fr + 72 + 24 = fr.rsp - 88 := by change fr.rsp - 184 + 72 + 24 = _; bv_omega
  have at16 : sp fr + 72 + 16 = fr.rsp - 96 := by change fr.rsp - 184 + 72 + 16 = _; bv_omega
  have at8 : sp fr + 72 + 8 = fr.rsp - 104 := by change fr.rsp - 184 + 72 + 8 = _; bv_omega
  have at0 : sp fr + 72 = fr.rsp - 112 := by change fr.rsp - 184 + 72 = _; bv_omega
  simp only [BitVec.ofNat_eq_ofNat] at at24 at16 at8 at0
  rcases values with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [scalarWord, Nat.reduceSub, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, at24, at16, at8, putScalar, stackWordKeep fr, same]
  · rw [at0]
    simp (disch := decide) only [stackWordKeep fr, same]

theorem putScalar_top {old m : Ram} (room : fr.low.toNat + 560 ≤ fr.rsp.toNat)
    (frame : RamWriteFrame old m (topWrites fr)) (src ret : BitVec 64) :
    RamWriteFrame old (putScalar fr m src ret) (topWrites fr) := by
  unfold putScalar
  iterate 5 first | apply topWordFrame room _ _ _ (by decide) (by decide)
  exact frame

end K256.Proofs.ParseSignature.Pair
