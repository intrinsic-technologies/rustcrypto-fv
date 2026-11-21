import ChaCha20Poly1305.Proofs.Encrypt.Prefix.State

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure BeforeHeader [Bindings] (initial s : RamState) (key : Vector UInt8 32)
    (length : Nat) : Prop extends Common initial s key where
  rip : s.RIP = 0x1017f6
  rsp : stackPtr s = stackPtr initial - 168
  rbp : s.regValue .rbp = BitVec.ofNat 64 (length + 16)
  r12 : s.regValue .r12 = initial.regValue .rcx
  r13 : s.regValue .r13 = BitVec.ofNat 64 length
  r14 : s.regValue .r14 = initial.regValue .rdx
  r15 : s.regValue .r15 = initial.regValue .rsi
  rbx : s.regValue .rbx = initial.regValue .r9
  rdi : s.regValue .rdi = initial.regValue .r8

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
