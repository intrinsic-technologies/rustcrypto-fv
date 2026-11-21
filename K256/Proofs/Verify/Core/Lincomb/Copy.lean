import K256.Proofs.Verify.Core.Lincomb.Interface

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve


def Copied (m : Ram) (src : BitVec 64) (n : Ram) (dst : BitVec 64) (len : Nat) : Prop :=
  ∀ off width : Nat, 0 < width / 8 → off + width / 8 ≤ len →
    memLoad n (dst + BitVec.ofNat 64 off) width = memLoad m (src + BitVec.ofNat 64 off) width

theorem Copied.of_frame {m n : Ram} {a : BitVec 64} {len : Nat} {rs : List MemoryRegion}
    (frame : RamWriteFrame m n rs) (apart : Outside rs a len) : Copied m a n a len := by
  intro off width hpos hlen
  apply frame.memLoad_eq
  have low := apart.1
  have eq := toNat_add_ofNat a off (by omega)
  exact Generate.Generator.Affine.outside_subregion apart (by omega) (by omega)

theorem Copied.memCopy {m : Ram} {dst src : BitVec 64} {len : Nat} (low : len ≤ 2^64) :
    Copied m src (memCopy m dst src len) dst len := by
  intro off width _ h
  exact Sec1.Parser.Result.memLoad_memCopy m dst src low h

theorem Copied.sub {m n : Ram} {src dst : BitVec 64} {size off len : Nat}
    (copy : Copied m src n dst size) (within : off + len ≤ size) :
    Copied m (src + BitVec.ofNat 64 off) n (dst + BitVec.ofNat 64 off) len := by
  intro k width hp hk
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact copy (off + k) width hp (by omega)

theorem Prepared.of_copy {m n : Ram} {tables digits tables' digits' : BitVec 64}
    {p : Curve.Point} {scalar : Nat} (prepared : Prepared m tables digits p scalar)
    (tableCopy : Copied m tables n tables' 1920) (digitCopy : Copied m digits n digits' 544) :
    Prepared n tables' digits' p scalar := by
  intro j
  obtain ⟨len, bytes, points⟩ := prepared j
  have hj := j.isLt
  refine ⟨(digitCopy (0x110 * j.val) 64 (by decide) (by omega)).trans len, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    have eq := digitCopy (0x110 * j.val + 8 + i.val) 8 (by decide) (by omega)
    simp only [BitVec.ofNat_add, ← BitVec.add_assoc] at eq
    exact eq.trans (bytes i)
  · intro k
    obtain ⟨q, valid, value, stored⟩ := points k
    refine ⟨q, valid, value, stored.of_word_copy ?_⟩
    intro i
    have hi := i.isLt
    have hk := k.isLt
    have eq := tableCopy (120 * (8 * j.val + k.val) + 8 * i.val) 64 (by decide) (by omega)
    simpa only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, ← BitVec.add_assoc] using eq

end K256.Proofs.Verify.Core.Lincomb
