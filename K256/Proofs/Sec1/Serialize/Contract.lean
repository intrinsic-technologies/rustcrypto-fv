import K256.Spec.Program
import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.Parser.Affine

namespace K256.Proofs.Sec1.Serialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters

def SerializerExecution : Prop :=
  ∀ {args : Vector Value Reg.count} {mem : Ram} {sp src dst ret : BitVec 64} {point : Curve.Point},
    args[4] = ⟨64, sp⟩ → args[6] = ⟨64, src⟩ → args[7] = ⟨64, dst⟩ →
    args[2].get 64 = 0 → args[22] = ⟨1, 0⟩ →
    (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → args[i].width = 64) →
    Parser.PublicKeyAt mem src point →
    Readable mem src 88 → Writable Extracted.programImage mem dst 65 →
    Writable Extracted.programImage mem (sp - 448) 456 →
    memLoad mem sp 64 = ret → ret.toNat < 2^32 →
    sp.toNat % 16 = 8 → 448 ≤ sp.toNat → sp.toNat + 8 ≤ dst.toNat →
    dst.toNat + 65 ≤ src.toNat →
    LoadOk mem 0x203dd0 8 → memLoad mem 0x203dd0 64 = 0x12a820 →
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1215e0, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = args[i]) ∧
      RamWriteFrame mem out.store [⟨(sp - 448).toNat, 448⟩, ⟨dst.toNat, 65⟩] ∧
      memLoad out.store dst 8 = 4 ∧
      (⟨dst.toNat, 65⟩ : MemoryRegion).HasBytes out.store (Points.encodePoint Secp256k1.domain false point)

end K256.Proofs.Sec1.Serialize
