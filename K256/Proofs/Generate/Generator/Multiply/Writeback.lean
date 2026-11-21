import K256.Proofs.Generate.LIR.Fn11c880.Frame
import K256.Proofs.Generate.Generator.Affine.Repr
import K256.Proofs.ParseSignature.BlackBox
import K256.Proofs.Sec1.Parser.Result.Copy
import K256.Proofs.Sec1.LIR.Generated.Values

namespace K256.Proofs.Generate.Generator.Multiply

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Generate.LIR Standards.SECG.ECC

theorem projectiveAt_copy {mem : Ram} {src dst : BitVec 64} {point : Curve.Point}
    (source : Affine.ProjectiveAt mem src point) :
    Affine.ProjectiveAt (memCopy mem dst src 120) dst point := by
  obtain ⟨x, y, z, xl, yl, zl, hx, hy, hz, repr⟩ := source
  have coords {offset : Nat} (h : offset + 40 ≤ 120) {limbs : Common.Field.Limbs}
      (words : WordsAt mem (src + BitVec.ofNat 64 offset) 64 limbs) :
      WordsAt (memCopy mem dst src 120) (dst + BitVec.ofNat 64 offset) 64 limbs := by
    intro i hi
    have c := Sec1.Parser.Result.memLoad_memCopy (off := offset + 8*i) (width := 64)
      mem dst src (by decide : 120 ≤ 2^64) (by omega)
    simpa only [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add] using c.trans (by
      simpa only [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add] using words i hi)
  exact ⟨x, y, z, xl, yl, zl, by simpa using coords (offset := 0) (by decide) (by simpa using hx),
    coords (offset := 40) (by decide) hy, coords (offset := 80) (by decide) hz, repr⟩

set_option maxHeartbeats 600000 in
theorem writeback {code : CodeMap} (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    {point : Curve.Point} (atoms : Atom.All code args mem (Fn11c880.frameAt .l11f6c4 fr))
    (included : ∀ x ∈ codeRange 0x11f6c4 bytes_l11f6c4, x ∈ code)
    (ptr : memLoad mem (fr.rsp - 0xa70) 64 = fr.rdi)
    (acc : Affine.ProjectiveAt mem (fr.rsp - 0xb90) point)
    (dst : Writable code mem fr.rdi 120)
    (apart : fr.rdi.toNat + 120 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.runBlock (dialect code) ⟨.l11f6c4, args, mem⟩ = .returned out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn11c880.doneAt fr) ∧
      out.values[0] = ⟨64, fr.rdi⟩ ∧ Affine.ProjectiveAt out.store fr.rdi point ∧
      RamWriteFrame mem out.store [⟨fr.rdi.toNat, 120⟩] ∧
      (∀ i : Fin Reg.count, i.val ∈ [2,8,9] → out.values[i] = args[i]) ∧
      out.values[1] = ⟨64, 0⟩ := by
  simp only [Fn11c880.frameAt, Fn11c880.frameAtG2, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, mx, ft, fc, bx, r12, r13, r14, r15, bp, retRead, retVal, retLow,
    stack, room, _, _⟩ := atoms
  have sp := congrArg (Value.get 64) rsp
  change args[4].get 64 = fr.rsp - 0xcb8 at sp
  have df0 : args[22].get 1 = 0 := congrArg (Value.get 1) df
  have sn (off : Nat) (h : off ≤ 0xed8) :
      (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
    have val : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, val]; omega), val]
  let src : BitVec 64 := fr.rsp - 0xb90
  let copied := memCopy mem fr.rdi src 120
  have srcRead : Readable mem src 120 :=
    stack.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have readPtr : LoadOk mem (fr.rsp - 0xa70) 8 :=
    LoadOk.of_offsets stack.readable (addr_sub _ _) (addr_sub _ _) (by decide)
  have guard := ParseSignature.storeOk_of_codeRange (off := 24) (len := 3) dst included (by decide)
  have other : src.toNat + 120 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 120 ≤ src.toNat := by
    change (fr.rsp - BitVec.ofNat 64 0xb90).toNat + _ ≤ _ ∨ _ ≤ (fr.rsp - BitVec.ofNat 64 0xb90).toNat
    rw [sn _ (by decide)]
    omega
  have copyOk : RepMovsOk code mem 0 src fr.rdi 15 8 0x11f6dc 3 :=
    ⟨rfl, srcRead.low, guard.low, srcRead.present, guard.present, other, guard.tables,
      guard.apart, guard.notCode⟩
  have low := dst.readable.low
  have writes : RamWriteFrame mem copied [⟨fr.rdi.toNat, 120⟩] :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_singleton_self _, Nat.le_refl _,
      Nat.le_refl _, by omega⟩
  have saved (off : Nat) (h : off ≤ 48) :
      memLoad copied (fr.rsp - BitVec.ofNat 64 off) 64 = memLoad mem (fr.rsp - BitVec.ofNat 64 off) 64 := by
    apply writes.memLoad_eq
    have hr := retRead.low
    refine ⟨by rw [sn _ (by omega)]; omega, ?_⟩
    intro r hr
    cases List.mem_singleton.mp hr
    change _ ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 120 ≤ _
    rw [sn _ (by omega)]
    omega
  have sameRet : memLoad copied fr.rsp 64 = fr.ret := by
    simpa using (saved 0 (by decide)).trans (by simpa using retVal)
  have readSlot (off : BitVec 64)
      (fits : ((0 - off) - (0 - 0xed8) : BitVec 64).toNat + 8 ≤ 0xed8) :
      LoadOk copied (fr.rsp - off) 8 :=
    LoadOk.of_offsets (stack.readable.of_frame writes) (addr_sub _ _) (addr_sub _ _) fits
  have retOk : LoadOk copied fr.rsp 8 :=
    ⟨retRead.low, (retRead.of_frame writes).present⟩
  have addr584 : fr.rsp - 0xcb8 + 584 = fr.rsp - 2672 := by bv_omega
  have addr296 : fr.rsp - 0xcb8 + 296 = fr.rsp - 2960 := by bv_omega
  have addr3208 : fr.rsp - 0xcb8 + 3208 = fr.rsp - 48 := by bv_omega
  have addr3216 : fr.rsp - 0xcb8 + 3216 = fr.rsp - 40 := by bv_omega
  have addr3224 : fr.rsp - 0xcb8 + 3224 = fr.rsp - 32 := by bv_omega
  have addr3232 : fr.rsp - 0xcb8 + 3232 = fr.rsp - 24 := by bv_omega
  have addr3240 : fr.rsp - 0xcb8 + 3240 = fr.rsp - 16 := by bv_omega
  have addr3248 : fr.rsp - 0xcb8 + 3248 = fr.rsp - 8 := by bv_omega
  have addr3256 : fr.rsp - 0xcb8 + 3256 = fr.rsp := by bv_omega
  have addr3264 : fr.rsp - 0xcb8 + 3264 = fr.rsp + 8 := by bv_omega
  refine ⟨?out, ?exec, ?tag, ?done_, ?result, ?point, ?frame, ?kept, ?cx⟩
  case exec =>
    cfg_eval
    simp only [sp, df0, addr584, readPtr, ptr, addr296, show fr.rsp - 2960 = src from rfl,
      copyOk, or_true, ↓reduceIte]
    simp only [← show copied = memCopy mem fr.rdi src 120 from rfl, addr3208, addr3216, addr3224,
      addr3232, addr3240, addr3248, addr3256, addr3264, readSlot 48 (by decide),
      readSlot 40 (by decide), readSlot 32 (by decide), readSlot 24 (by decide),
      readSlot 16 (by decide), readSlot 8 (by decide), retOk, sameRet, retLow, and_self, ↓reduceIte]
    rfl
  case tag => rfl
  case done_ =>
    refine ⟨rfl, df, ?_, ?_, ?_, ?_, ?_, ?_, mx, ft, fc, trivial⟩
    · exact congrArg (Value.mk 64) ((saved 48 (by decide)).trans bx)
    · exact congrArg (Value.mk 64) ((saved 8 (by decide)).trans bp)
    · exact congrArg (Value.mk 64) ((saved 40 (by decide)).trans r12)
    · exact congrArg (Value.mk 64) ((saved 32 (by decide)).trans r13)
    · exact congrArg (Value.mk 64) ((saved 24 (by decide)).trans r14)
    · exact congrArg (Value.mk 64) ((saved 16 (by decide)).trans r15)
  case result => rfl
  case point => exact projectiveAt_copy acc
  case frame => exact writes
  case kept =>
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> rfl
  case cx => rfl

end K256.Proofs.Generate.Generator.Multiply
