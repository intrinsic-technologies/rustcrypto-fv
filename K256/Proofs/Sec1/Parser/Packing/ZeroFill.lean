import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.ParseSignature.Fill.Blocks

namespace K256.Proofs.Sec1.Parser.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.ParseSignature (buffer)
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

private theorem replicate_zero_value (w count : Nat) : (0 : BitVec w).replicate count = 0 := by
  change (0#w).replicate count = 0#(w * count)
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_replicate, BitVec.getLsbD_zero, Bool.and_false]

private theorem memFill_zero_fold (m : Ram) (dst : BitVec 64) (w count : Nat)
    (hw : w % 8 = 0) :
    memFill m dst (0 : BitVec w) count =
      (List.range (w / 8 * count)).foldl
        (fun mem i => mem.insert (dst + BitVec.ofNat 64 i) 0) m := by
  rw [memFill, memStore_eq_foldl, replicate_zero_value]
  have hlen : w * count / 8 = w / 8 * count := by
    rw [Nat.mul_comm w count, Nat.mul_div_assoc count (Nat.dvd_of_mod_eq_zero hw), Nat.mul_comm]
  have hz : (0 : BitVec (w * count)).toNat = 0 := rfl
  simp only [hlen, hz, Nat.zero_shiftRight]
  rfl

private theorem memFill_zero_append (m : Ram) (dst : BitVec 64) (head w count : Nat)
    (hw : w % 8 = 0) :
    memFill (memFill m dst (0 : BitVec 8) head) (dst + BitVec.ofNat 64 head) (0 : BitVec w) count =
      memFill m dst (0 : BitVec 8) (head + w / 8 * count) := by
  simp only [memFill_zero_fold, hw, Nat.reduceMod, Nat.reduceDiv, Nat.one_mul]
  rw [List.range_add (n := head) (m := w / 8 * count), List.foldl_append, List.foldl_map]
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

private theorem memFill_zero_frame (m : Ram) (dst : BitVec 64) (len : Nat)
    (hlow : dst.toNat + len ≤ 2 ^ 32) :
    RamWriteFrame m (memFill m dst (0 : BitVec 8) len) [buffer dst len] := by
  have hlen : (8 * len) / 8 = len := Nat.mul_div_cancel_left _ (by decide)
  exact (RamWriteFrame.refl _ _).memStore _ (by
    rw [hlen]
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by omega⟩)

private theorem memFill_zero_byte (m : Ram) (dst : BitVec 64) {len i : Nat}
    (hi : i < len) (hlen : len ≤ 2 ^ 64) :
    memByte (memFill m dst (0 : BitVec 8) len) (dst + BitVec.ofNat 64 i) = 0 := by
  have hw : (8 * len) / 8 = len := Nat.mul_div_cancel_left _ (by decide)
  rw [memByte, memFill, replicate_zero_value]
  change ((memStore m dst (0 : BitVec (8 * len)))[dst + BitVec.ofNat 64 i]?).getD 0 = 0
  rw [memStore_getElem?_self_of_le _ _ _ (hw.symm ▸ hlen) i (hw.symm ▸ hi)]
  have hz : (0 : BitVec (8 * len)).toNat = 0 := rfl
  simp only [Option.getD_some, storedByte, hz, Nat.zero_shiftRight]
  rfl

private theorem stosGuard {code : CodeMap} {mem : Ram} {dst : BitVec 64}
    {len off instrOff instrLen width : Nat} {count : BitVec 64}
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (hw : Writable code mem dst len)
    (hwithin : off + width * count.toNat ≤ len)
    (hinstr : instrOff + instrLen ≤ bytes_l12a700.length) :
    RepStosOk code mem 0 (dst + BitVec.ofNat 64 off) count width
      (0x12a700 + BitVec.ofNat 64 instrOff) instrLen := by
  have hb := hw.readable.low
  have haddr := toNat_add_ofNat dst off (by omega)
  have hwrite := hw.sub (a := dst + BitVec.ofNat 64 off) (n := width * count.toNat)
    (by rw [haddr]; omega) (by rw [haddr]; omega)
  have hg := ParseSignature.storeOk_of_codeRange hwrite
    (fun x hx => hcode x (code_l12a700 x hx)) hinstr
  exact ⟨rfl, hg.low, hg.present, hg.tables, hg.apart, hg.notCode⟩

private theorem memsetPrefix (sp n : BitVec 64) (halign : sp.toNat % 16 = 0)
    (hn : n = 1 ∨ n = 33 ∨ n = 65) :
    (-(BitVec.setWidth 32 (sp + 160 + n)) &&& 7 : BitVec 32) = 7 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_neg, BitVec.toNat_setWidth, BitVec.toNat_add]
  change (((2 ^ 32 - (((sp.toNat + 160) % (2 ^ 64) + n.toNat) % (2 ^ 64)) % (2 ^ 32)) %
    (2 ^ 32)) &&& (2 ^ 3 - 1)) = 7
  rw [Nat.and_two_pow_sub_one_eq_mod _ 3]
  rcases hn with rfl | rfl | rfl <;> simp only [BitVec.reduceToNat, Nat.reducePow] <;> omega

theorem memsetBlock {code : CodeMap} {a : Values Value Reg.count} {m : Ram} {sp n : BitVec 64}
    (hcode : ∀ x ∈ fnCode, x ∈ code) (hsizes : n = 1 ∨ n = 33 ∨ n = 65)
    (halign : sp.toNat % 16 = 0)
    (hsp : a[4] = ⟨64, sp - 8⟩) (hn : a[2] = ⟨64, 65 - n⟩) (hbyte : a[6] = ⟨64, 0⟩)
    (hdst : a[7] = ⟨64, sp + 160 + n⟩) (hdf : a[22].get 1 = 0)
    (hw : Writable code m (sp + 160 + n) (65 - n).toNat)
    (hret : LoadOk m (sp - 8) 8) (hword : memLoad m (sp - 8) 64 = 0x106409)
    (hapart : Outside [buffer (sp + 160 + n) (65 - n).toNat] (sp - 8) 8) :
    ∃ out, program.runBlock (dialect code) ⟨.l12a700, a, m⟩ = .returned out ∧
      out.tag = some ⟨64, 0x106409⟩ ∧ out.values[4] = ⟨64, sp⟩ ∧
      (∀ r ∈ [3, 5, 9, 10, 11, 12, 13, 14, 15, 22, 39, 50, 51],
        ∀ hr : r < Reg.count, out.values[r] = a[r]) ∧
      RamWriteFrame m out.store [buffer (sp + 160 + n) (65 - n).toNat] ∧
      (∀ i < (65 - n).toNat, memByte out.store (sp + 160 + n + BitVec.ofNat 64 i) = 0) := by
  let dst := sp + 160 + n
  let len := (65 - n).toNat
  let head : BitVec 64 := if (cmpSpec (65 - n) 7).CF = true then 65 - n else 7
  let body : BitVec 64 := (65 - n - head) >>> 3
  let tail : BitVec 64 := ((65 - n - head).setWidth 32 &&& 7).setWidth 64
  have hlen : head.toNat + 8 * body.toNat + tail.toNat = len := by
    rcases hsizes with rfl | rfl | rfl <;> decide +kernel
  let m₁ := memFill m dst (0 : BitVec 8) head.toNat
  let dst₂ := dst + BitVec.ofNat 64 head.toNat
  let m₂ := memFill m₁ dst₂ (0 : BitVec 64) body.toNat
  let dst₃ := dst₂ + BitVec.ofNat 64 (8 * body.toNat)
  have g₁ : RepStosOk code m 0 dst head 1 0x12a734 2 := by
    have guard := stosGuard (off := 0) (instrOff := 52) (count := head) hcode hw
      (by rw [Nat.zero_add, Nat.one_mul]; omega)
      (by decide : 52 + 2 ≤ bytes_l12a700.length)
    change RepStosOk code m 0 (dst + 0#64) head 1 0x12a734 2 at guard
    rwa [BitVec.add_zero] at guard
  have hw₁ : Writable code m₁ dst len := hw.memStore _ _
  have g₂ : RepStosOk code m₁ 0 dst₂ body 8 0x12a739 3 :=
    stosGuard (instrOff := 57) hcode hw₁ (by omega) (by decide)
  have hw₂ : Writable code m₂ dst len := hw₁.memStore _ _
  have g₃ : RepStosOk code m₂ 0 dst₃ tail 1 0x12a73f 2 := by
    rw [show dst₃ = dst + BitVec.ofNat 64 (head.toNat + 8 * body.toNat) by
      simp only [dst₃, dst₂, BitVec.ofNat_add, BitVec.add_assoc]]
    exact stosGuard (instrOff := 63) hcode hw₂ (by rw [Nat.one_mul]; omega) (by decide)
  have hstore : memFill m₂ dst₃ (0 : BitVec 8) tail.toNat = memFill m dst (0 : BitVec 8) len := by
    dsimp only [m₂, m₁, dst₃, dst₂]
    rw [memFill_zero_append _ _ _ _ _ (by decide)]
    rw [show (64 : Nat) / 8 = 8 by decide, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [memFill_zero_append _ _ _ _ _ (by decide)]
    simp only [Nat.reduceDiv, Nat.one_mul, hlen]
  have hframe := memFill_zero_frame m dst len hw.readable.low
  have hload : LoadOk (memFill m dst (0 : BitVec 8) len) (sp - 8) 8 :=
    ⟨hret.low, fun i hi => hframe.present _ (hret.present i hi)⟩
  have htag : memLoad (memFill m dst (0 : BitVec 8) len) (sp - 8) 64 = 0x106409 :=
    (hframe.memLoad_eq hapart).trans hword
  have htargetLow : (0x106409 : BitVec 64).toNat < 2 ^ 32 := by decide
  have hprefix : (-(dst.setWidth 32) &&& 7 : BitVec 32) = 7 := memsetPrefix sp n halign hsizes
  refine ⟨?out, ?run, ?post⟩
  case run =>
    cfg_eval
    simp only [ParseSignature.Fill.get64 hsp, ParseSignature.Fill.get64 hn,
      ParseSignature.Fill.get64 hbyte, ParseSignature.Fill.get64 hdst, hdf,
      hprefix, BitVec.reduceSetWidth, BitVec.setWidth_zero,
      BitVec.mul_zero, ← show dst = sp + 160 + n from rfl]
    change (if head = 0 ∨ RepStosOk code m 0 dst head 1 0x12a734 2 then _ else _) = _
    simp only [g₁, or_true, ite_true]
    change (if body = 0 ∨ RepStosOk code m₁ 0 dst₂ body 8 0x12a739 3 then _ else _) = _
    simp only [g₂, or_true, ite_true]
    change (if tail = 0 ∨ RepStosOk code m₂ 0 dst₃ tail 1 0x12a73f 2 then _ else _) = _
    simp only [g₃, or_true, ite_true, BitVec.sub_add_cancel]
    let filled := memFill m₂ dst₃ (0 : BitVec 8) tail.toNat
    change (if LoadOk filled (sp - 8) 8 ∧ (memLoad filled (sp - 8) 64).toNat < 2 ^ 32 then
      Transfer.returned (⟨_, some ⟨64, memLoad filled (sp - 8) 64⟩, filled⟩ :
        Output Value Ram Reg.count)
      else Transfer.stuck) = _
    dsimp only [filled]
    simp only [hstore, hload, htag, htargetLow, and_self, ite_true]
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_, hframe, ?_⟩
    · intro r hr _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · intro i hi
      exact memFill_zero_byte m dst hi (by have := hw.readable.low; omega)

end K256.Proofs.Sec1.Parser.Packing
