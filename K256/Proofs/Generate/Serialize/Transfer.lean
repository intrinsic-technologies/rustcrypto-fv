import K256.Proofs.Generate.Serialize.Transfer.Blocks
import K256.Proofs.Sec1.Serialize.Execution
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Generate.Serialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters

def SerializerExecution : Prop :=
  ∀ {args : Vector Value Reg.count} {mem : Ram} {sp src dst ret : BitVec 64} {point : Curve.Point},
    args[4] = ⟨64, sp⟩ → args[6] = ⟨64, src⟩ → args[7] = ⟨64, dst⟩ →
    args[2].get 64 = 0 → args[22] = ⟨1, 0⟩ →
    (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → args[i].width = 64) →
    Sec1.Parser.PublicKeyAt mem src point →
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

theorem serializerExecution : SerializerExecution := by
  intro args mem sp src dst ret point rsp rsi rdi compress df width pointAt source dest
    window retSlot retLow align room destAbove pointAbove gotRead gotTarget
  obtain ⟨out, run, post⟩ := Sec1.Serialize.serializerExecution rsp rsi rdi compress df width
    pointAt source dest window retSlot retLow align room destAbove pointAbove gotRead gotTarget
  exact ⟨out, Relabel.exec matches_blocks run rfl, post⟩

theorem memcpy {args : Values Value Reg.count} {mem : Ram} {dst src count rsp : BitVec 64}
    (hdst : args[7].get 64 = dst) (hsrc : args[6].get 64 = src)
    (hc : args[2].get 64 = count) (hsp : args[4].get 64 = rsp) (hdf : args[22].get 1 = 0)
    (hr : Readable mem src count.toNat) (hw : Writable Extracted.programImage mem dst count.toNat)
    (hdisjoint : src.toNat + count.toNat ≤ dst.toNat ∨ dst.toNat + count.toNat ≤ src.toNat)
    (hapret : RangeApart dst count.toNat rsp 8)
    (hreturnRead : Readable mem rsp 8) (hretlow : (memLoad mem rsp 64).toNat < 2 ^ 32) :
    ∃ output, program.Exec (dialect Extracted.programImage) ⟨⟨.l12a820, args, mem⟩, []⟩ output ∧
      output.store = memCopy mem dst src count.toNat ∧
      output.tag = some ⟨64, memLoad mem rsp 64⟩ ∧
      output.values[0] = ⟨64, dst⟩ ∧ output.values[4] = ⟨64, rsp + 8⟩ ∧
      (∀ i : Fin 53, i.val ∈ [3,5,9,10,11,12,13,14,15,22,39,50,51] → output.values[i] = args[i]) := by
  obtain ⟨out, run, post⟩ := Sec1.Wrapper.Copy.memcpy hdst hsrc hc hsp hdf hr hw
    hdisjoint hapret hreturnRead hretlow
  exact ⟨out, Relabel.exec matches_blocks run rfl, post⟩

end K256.Proofs.Generate.Serialize
