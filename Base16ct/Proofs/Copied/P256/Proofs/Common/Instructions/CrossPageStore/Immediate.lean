import Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore.Store
import X86Proofs.Instructions.MovStore.Triple
set_option autoImplicit false

namespace Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def movM32Imm32LegacyEffect (p : BitVec 64) (am : AddrMode) (imm : BitVec 32) : RamState → Effect :=
  storeEffect p (6 + am.tail.length) (storeAddrAt p am (6 + am.tail.length)) fun _ => imm

end Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore
