import K256.Proofs.Sec1.Serialize.Choice
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall
import K256.Proofs.Sec1.Serialize.Output

namespace K256.Proofs.Sec1.Serialize

open Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters

theorem assembleChoice {code : CodeMap} {caller : Location Value Ram Label signature}
    {next : Values Value Reg.count} {written : Ram} {base : BitVec 64}
    {a b : Limbs} {x y : Fin modulus} {m : Nat}
    (cover : ∀ entry ∈ fnCode, entry ∈ code)
    (call : program.runBlock (dialect code) caller = .call ⟨.l127d50, next, written⟩
      (Coordinates.callFrame .l121831 0x121831))
    (rsp : next[4] = ⟨64, base - 8⟩) (arg : next[7].get 8 = 0)
    (scratch : Writable code written (base - 9) 1) (slot : Readable written (base - 8) 8)
    (ret : memLoad written (base - 8) 64 = 0x121831)
    (hx : FieldRepr a x m) (hy : FieldRepr b y m) (bound : m ≤ 2047)
    (tag : written[base + 215]? = some 4)
    (xs : WordsAt written (base + 216) 64 (packWords (Normalize.normalize a)))
    (ys : WordsAt written (base + 248) 64 (packWords (Normalize.normalize b)))
    (readable : Readable written (base + 215) 65) :
    ∃ (regs : Values Value Reg.count) (mem : Ram),
      (program.sem (dialect code)).Reaches ⟨caller, []⟩ ⟨⟨.l121831, regs, mem⟩, []⟩ ∧
      regs[4] = ⟨64, base⟩ ∧ regs[0].get 8 = 0 ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] →
        regs[i] = next[i]) ∧
      RamWriteFrame written mem [⟨(base - 9).toNat, 1⟩] ∧
      (⟨(base + 215).toNat, 65⟩ : MemoryRegion).HasBytes mem
        (Points.encodePoint Secp256k1.domain false (.affine x.val y.val)) := by
  have offset : base - 8 - 1 = base - 9 := by bv_omega
  obtain ⟨out, step, returnTag, newSp, newAx, frame, saved⟩ :=
    choiceBlock (fun e he => cover e (code_l127d50 e he))
      (show next[4].get 64 = base - 8 by rw [rsp, Value.get_mk])
      (offset ▸ scratch) slot (by rw [ret]; decide)
  rw [offset] at frame
  have run : program.Exec (dialect code) ⟨⟨.l127d50, next, written⟩, []⟩ out :=
    .done (by simp only [Program.step, step, Transfer.next])
  have encoded := normalizedPoint_hasBytes hx hy bound tag
    (by rw [show base + 215 + 1 = base + 216 by bv_omega]; exact xs)
    (by rw [show base + 215 + 33 = base + 248 by bv_omega]; exact ys) readable
  refine ⟨out.values, out.store, Coordinates.reaches_call call run (ret ▸ returnTag),
    ?_, ?_, saved, frame, encoded.1, ?_⟩
  · simpa only [BitVec.sub_add_cancel] using newSp
  · rw [newAx]
    have h : (next[7].get 64).setWidth 8 = 0 := by
      simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using arg
    rw [h]
    rfl
  · intro i
    apply Eq.trans (frame.outside _ ?_) (encoded.2 i)
    have size : (Points.encodePoint Secp256k1.domain false (.affine x.val y.val)).size = 65 :=
      encoded.1
    have hi : i.val < 65 := size ▸ i.isLt
    have low := readable.low
    have ha : (BitVec.ofNat 64 ((base + 215).toNat + i.val)).toNat =
        (base + 215).toNat + i.val := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hs := scratch.readable.low
    have hd : (base + 215).toNat = (base - 9).toNat + 224 := by
      rw [show base + 215 = (base - 9) + 224 by bv_omega, BitVec.toNat_add]
      change (_ + 224) % 2^64 = _
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨?_, fun r hr => ?_⟩
    · change (BitVec.ofNat 64 ((base + 215).toNat + i.val)).toNat + 1 ≤ 2^64
      rw [ha]
      omega
    · obtain rfl := List.mem_singleton.mp hr
      right
      change (base - 9).toNat + 1 ≤ (BitVec.ofNat 64 ((base + 215).toNat + i.val)).toNat
      rw [ha, hd]
      omega

end K256.Proofs.Sec1.Serialize
