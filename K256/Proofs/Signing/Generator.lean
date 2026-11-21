import K256.Proofs.Signing.Generator.Caller
import K256.Spec.Program
import K256.Proofs.Generate.Curve
import K256.Proofs.Generate.Generator.Affine.Repr
import K256.Proofs.Generate.LIR.Fn10ee80.Frame

namespace K256.Proofs.Signing.Generator

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  K256.Proofs.Generate K256.Proofs.Generate.Generator Standards.SECG.DomainParameters

private theorem offsetAtLeast {sp ptr off : BitVec 64} {total min : Nat}
    (high : sp.toNat + total ≤ 2^32) (pointer : ptr = sp + off)
    (fits : off.toNat ≤ total) (lower : min ≤ off.toNat) : sp.toNat + min ≤ ptr.toNat := by
  rw [pointer, BitVec.toNat_add_of_lt (by omega)]
  exact Nat.add_le_add_left lower _

theorem execution {fr : Activation} {a : Values Value Reg.count} {d : Nat}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (high : fr.rsp.toNat + 352 ≤ 2^32)
    (src : fr.rsi = fr.rsp + 8) (dst : fr.rdi = fr.rsp + 208)
    (source : Readable fr.original fr.rsi 32)
    (destination : Writable Extracted.programImage fr.original fr.rdi 120)
    (words : WordsAt fr.original fr.rsi 64
      (Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2^(64*i.val))))
    (pos : 0 < d) (bound : d < Secp256k1.domain.n) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10ee80, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn10ee80.doneAt fr) ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → out.values[i].width = 64) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat, 120⟩] ∧
      K256.Proofs.Generate.Generator.Affine.ProjectiveAt out.store fr.rdi (Curve.generatorWindow d) := by
  exact executionOfRegions atoms image room low high
    (offsetAtLeast (min := 0) high src (by decide) (by decide))
    (offsetAtLeast high dst (by decide) (by decide)) source destination words pos bound

theorem nonceExecution {fr : Activation} {a : Values Value Reg.count} {d : Nat}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (high : fr.rsp.toNat + 664 ≤ 2^32)
    (src : fr.rsi = fr.rsp + 632) (dst : fr.rdi = fr.rsp + 16)
    (source : Readable fr.original fr.rsi 32)
    (destination : Writable Extracted.programImage fr.original fr.rdi 120)
    (words : WordsAt fr.original fr.rsi 64
      (Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2^(64*i.val))))
    (pos : 0 < d) (bound : d < Secp256k1.domain.n) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10ee80, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn10ee80.doneAt fr) ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → out.values[i].width = 64) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat, 120⟩] ∧
      K256.Proofs.Generate.Generator.Affine.ProjectiveAt out.store fr.rdi (Curve.generatorWindow d) := by
  exact executionOfRegions atoms image room low (by omega)
    (offsetAtLeast (min := 0) high src (by decide) (by decide))
    (offsetAtLeast high dst (by decide) (by decide)) source destination words pos bound

end K256.Proofs.Signing.Generator
