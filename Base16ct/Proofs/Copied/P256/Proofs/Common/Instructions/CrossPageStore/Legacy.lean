import Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore.Store
import X86Proofs.Instructions.MovStore.Triple
set_option autoImplicit false

namespace Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def movM32R32LegacyEffect (p : BitVec 64) (src : BitVec 5) (am : AddrMode) : RamState → Effect :=
  storeEffect p (2 + am.tail.length) (storeAddrAt p am (2 + am.tail.length))
    fun s => (Operand.reg src : Operand 32).read s

end Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore
