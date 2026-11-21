import P256.Proofs.Common.Memory.Fill.Stos.Spec
import P256.Proofs.Common.Memory.Fill.Stos.After
import P256.Proofs.Common.Memory.Fill.Stos.Loop
import P256.Proofs.Common.Memory.Fill.Stos.Execution
import P256.Proofs.Common.Memory.Fill.Stos.LowLevel

namespace P256.Proofs.Common.Memory.Fill.Stos

open X86Proofs X86 X86.Machine X86.UserProcess

theorem rep_stosb_zero_fill [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (p : BitVec 64) (s : RamState) (count : Nat)
    (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, 0xaa]) s)
    (hrip : s.RIP = p) (hc : rcx.read s = BitVec.ofNat 64 count)
    (hdf : DirectionFlagClear s.RFLAGS) (hz : (Operand.reg 0 : Operand 8).read s = 0)
    (hdst : (rdi.read s).toNat + count ≤ 2^32)
    (hmem : ∀ i < count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome)
    (htables : 0 < count → (rdi.read s).toNat + count ≤ 0x1000 ∨ 0x3000 ≤ (rdi.read s).toNat)
    (hapart : RangeApart (rdi.read s) count p 2)
    (hstart : p ≠ boundary.rip) (hend : p + 2#64 ≠ boundary.rip) :
    ∃ t, Advances boundary (max count 1) s t ∧ ReadyToStep t ∧ t.RIP = p + 2#64 ∧
      rdi.read t = rdi.read s + BitVec.ofNat 64 count ∧ rcx.read t = 0 ∧
      (∀ i < count, t.external[rdi.read s + BitVec.ofNat 64 i]? = some 0) ∧
      AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) count, .rip] s t := by
  have hrun := rep_stos_zero_fill (rep_stosb_instruction hstride) boundary p s count
  simp only [Nat.one_mul] at hrun
  exact hrun h hcode hrip hc hdf hz hdst hmem htables hapart (by intro; omega) hstart hend

theorem rep_stosq_zero_fill [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (p : BitVec 64) (s : RamState) (count : Nat)
    (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, 0x48, 0xab]) s)
    (hrip : s.RIP = p) (hc : rcx.read s = BitVec.ofNat 64 count)
    (hdf : DirectionFlagClear s.RFLAGS) (hz : (Operand.reg 0 : Operand 64).read s = 0)
    (hdst : (rdi.read s).toNat + 8 * count ≤ 2^32)
    (hmem : ∀ i < 8 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome)
    (htables : 0 < count → (rdi.read s).toNat + 8 * count ≤ 0x1000 ∨ 0x3000 ≤ (rdi.read s).toNat)
    (hapart : RangeApart (rdi.read s) (8 * count) p 3)
    (halign : 0 < count → (rdi.read s).toNat % 8 = 0)
    (hstart : p ≠ boundary.rip) (hend : p + 3#64 ≠ boundary.rip) :
    ∃ t, Advances boundary (max count 1) s t ∧ ReadyToStep t ∧ t.RIP = p + 3#64 ∧
      rdi.read t = rdi.read s + BitVec.ofNat 64 (8 * count) ∧ rcx.read t = 0 ∧
      (∀ i < 8 * count, t.external[rdi.read s + BitVec.ofNat 64 i]? = some 0) ∧
      AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (8 * count), .rip] s t := by
  exact rep_stos_zero_fill (rep_stosq_instruction hstride) boundary p s count h hcode hrip hc
    hdf hz hdst hmem htables hapart halign hstart hend

end P256.Proofs.Common.Memory.Fill.Stos
