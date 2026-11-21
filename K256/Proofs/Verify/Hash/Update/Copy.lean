import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Verify.Hash.Update

open K256.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

open K256.Proofs.Generate.Serialize

private def memcpyTarget : Sec1.LIR.Label → Option LIR.Label
  | .l12a820 => some .l12a820
  | _ => none

private theorem memcpy_blocks (a : Sec1.LIR.Label) (b : LIR.Label) (h : memcpyTarget a = some b) :
    Relabel.block memcpyTarget (Sec1.LIR.program.blocks a) =
      Relabel.block some (program.blocks b) := by
  unfold memcpyTarget at h
  split at h
  · cases h
    rfl
  · cases h

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
  obtain ⟨output, run, post⟩ := Sec1.Wrapper.Copy.memcpy hdst hsrc hc hsp hdf hr hw
    hdisjoint hapret hreturnRead hretlow
  exact ⟨output, Relabel.exec memcpy_blocks run rfl, post⟩

end K256.Proofs.Verify.Hash.Update
