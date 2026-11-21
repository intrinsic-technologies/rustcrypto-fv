import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem static_code_apart (off offset len : Nat) (ho : off + 8 ≤ 40)
    (hl : offset + len ≤ 118431) :
    RangeApart (0x300000 + BitVec.ofNat 64 off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  simpa only [Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
    (RangeApart.offsets (0x100000 : BitVec 64) (a := 0x200000 + off) (b := offset)
      (len := 8) (count := len) (by omega) (by omega) (by omega))

theorem memLoad_after (e : Effect) (s : RamState) (b : Bool) (a : BitVec 64) (n : Nat) :
    memLoad (e.after s b).external a n =
      (Operand.mem a : Operand n).read (applyWrites s e.writes) :=
  e.read_after s b (.mem a)

theorem memLoad_memStore_constants (mem : Ram) (a b : BitVec 64) (v : BitVec 64)
    (h : OffsetsApart a 8 b 8) :
    memLoad (memStore mem a v) b 64 = memLoad mem b 64 := by
  have he := memLoad_memStore_apart mem (0 : BitVec 64) a b v 64 h (by decide) (by decide)
  simpa using he

end P256.Proofs.Program
