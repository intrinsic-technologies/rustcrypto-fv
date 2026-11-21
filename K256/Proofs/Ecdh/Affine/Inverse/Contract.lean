import K256.Proofs.Generate.Generator.Affine.Invert.Contract

namespace K256.Proofs.Ecdh.Affine.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

open K256.Proofs.Generate.Generator.Affine

def ZeroCoreExecution : Prop :=
  ∀ (a : Registers) (m : Ram) (sp : Word) (w : Vector Word 4),
    a[4] = ⟨64, sp⟩ → a[1] = ⟨64, 0x27c7f6e22ddacacf⟩ →
    a[2] = ⟨64, 0x2021e0⟩ → a[6] = ⟨64, sp + 8⟩ → a[7] = ⟨64, sp + 96⟩ →
    a[8] = ⟨64, 0x202180⟩ → a[22] = ⟨1, 0⟩ →
    (∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15] → a[i].width = 64) →
    (∀ b ∈ Extracted.programImage, m[b.1]? = some b.2) →
    736 ≤ sp.toNat → sp.toNat + 129 ≤ 2^32 → sp.toNat % 16 = 8 →
    Readable m 0x203de0 8 → memLoad m 0x203de0 64 = 0x129770 →
    Readable m 0x203e20 8 → memLoad m 0x203e20 64 = 0x100a20 →
    (0x204108 ≤ sp.toNat ∨ sp.toNat ≤ 0x203de0) →
    Writable Extracted.programImage m (sp - 736) 736 →
    Readable m sp 40 → Writable Extracted.programImage m (sp + 96) 33 →
    memLoad m sp 64 = 0x10ed84 → WordsAt m (sp + 8) 64 w → Invert.value w = 0 →
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l108e30, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, 0x10ed84⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        out.values[i] = a[i]) ∧
      RamWriteFrame m out.store [⟨(sp - 736).toNat, 736⟩, ⟨(sp + 96).toNat, 33⟩] ∧
      memLoad out.store (sp + 128) 8 = 0

end K256.Proofs.Ecdh.Affine.Inverse
