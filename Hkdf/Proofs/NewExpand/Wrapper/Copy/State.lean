import Hkdf.Proofs.NewExpand.Wrapper.Frame

namespace Hkdf.Proofs.NewExpand.Wrapper.Copy

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Copied [Bindings] (initial s : RamState) (prk : ByteArray) : Prop where
  run : Running initial s
  saved : SavedFrame initial s
  args : Arguments initial s
  rip : s.RIP = 0x102025
  rsp : stackPtr s = stackPtr initial - 360
  key : s.regValue .r13 = stackPtr initial - 184
  hmac : HmacAt s (stackPtr initial - 184) prk ByteArray.empty

structure AtExpand [Bindings] (initial s : RamState) (prk : ByteArray) : Prop where
  run : Running initial s
  saved : SavedFrame initial s
  rip : s.RIP = 0x10f250
  rsp : stackPtr s = stackPtr initial - 368
  key : s.regValue .rdi = stackPtr initial - 184
  descriptor : s.regValue .rsi = stackPtr initial - 360
  hmac : HmacAt s (s.regValue .rdi) prk ByteArray.empty
  pointer : (registerRegion s .rsi 8).Word64At s.external (initial.regValue .r8)
  infoLength : (⟨(s.regValue .rsi).toNat + 8, 8⟩ : MemoryRegion).Word64At s.external
    (initial.regValue .r9)
  count : s.regValue .rdx = 1
  output : s.regValue .rcx = stackArgument initial 1
  length : s.regValue .r8 = stackArgument initial 2
  boundary : returnBoundary s = ⟨0x102044, stackPtr initial - 360⟩

end Hkdf.Proofs.NewExpand.Wrapper.Copy
