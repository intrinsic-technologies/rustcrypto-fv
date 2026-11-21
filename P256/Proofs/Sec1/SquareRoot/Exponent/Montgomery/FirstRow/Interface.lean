import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstRow.Memory
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure FirstRowInput (s : RamState) (a b : Vector (BitVec 64) 4) : Prop where
  left : ∀ i : Fin 4,
    (Operand.mem (s.regValue .rsi+BitVec.ofNat 64 (8*i.val)) : Operand 64).read s = a[i]
  right : ∀ i : Fin 4,
    (Operand.mem (s.regValue .rdx+BitVec.ofNat 64 (8*i.val)) : Operand 64).read s = b[i]
  modulus : ∀ i : Fin 4,
    (Operand.mem (s.regValue .rcx+BitVec.ofNat 64 (8*i.val)) : Operand 64).read s =
      (#v[0xffffffffffffffff#64, 0xffffffff#64, 0#64, 0xffffffff00000001#64])[i]
  inverse : s.regValue .r8 = 1#64

structure FirstRowTrace (entry : BitVec 64) (s t : RamState) where
  initialized : RamState
  products : RamState
  carry : RamState
  middle : RamState
  high : RamState
  initializeEffect : (Montgomery.initializeEffect (entry+14#64) s).Holds s initialized
  productsEffect : (firstProductsEffect (entry+58#64) initialized).Holds initialized products
  carryEffect : (firstCarryEffect (entry+98#64) products).Holds products carry
  middleEffect : (firstMiddleEffect (entry+144#64) carry).Holds carry middle
  highEffect : (firstHighEffect (entry+224#64) middle).Holds middle high
  topEffect : (firstTopEffect (entry+281#64) high).Holds high t

end P256.Proofs.Sec1.SquareRoot.Montgomery
