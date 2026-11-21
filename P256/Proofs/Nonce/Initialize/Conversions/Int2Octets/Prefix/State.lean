import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar

structure HighLimbState [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop extends
    Stage initial s boundary where
  rip : s.RIP = 0x106f79
  rdi : s.regValue .rdi = initial.regValue .rdi
  rsi : s.regValue .rsi = initial.regValue .rsi
  rcx : s.regValue .rcx = 32
  r12 : s.regValue .r12 = initial.regValue .rdx
  rax : s.regValue .rax = 127
  r8 : s.regValue .r8 = 0xffffffff00000000
  r9 : s.regValue .r9 = 0
  rdx : s.regValue .rdx = 0xffffffff

structure HighScanState [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop extends
    Stage initial s boundary where
  rip : s.RIP = 0x106fac
  rdi : s.regValue .rdi = initial.regValue .rdi
  rsi : s.regValue .rsi = initial.regValue .rsi
  rcx : s.regValue .rcx = 32
  r12 : s.regValue .r12 = initial.regValue .rdx
  rax : s.regValue .rax = 127
  rdx : s.regValue .rdx = 0
  r8 : s.regValue .r8 = 0
  r9 : s.regValue .r9 = 0
  r10 : s.regValue .r10 = 0xffffffffffffffff
  r11 : s.regValue .r11 = 0

structure MiddleScanState [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop extends
    Stage initial s boundary where
  rip : s.RIP = 0x106fdb
  rdi : s.regValue .rdi = initial.regValue .rdi
  rsi : s.regValue .rsi = initial.regValue .rsi
  rcx : s.regValue .rcx = 32
  r12 : s.regValue .r12 = initial.regValue .rdx
  rax : s.regValue .rax = 127
  rdx : s.regValue .rdx = 0
  r8 : s.regValue .r8 = 0
  r9 : s.regValue .r9 = 0
  r15 : s.regValue .r15 = 0

structure LowScanState [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop extends
    Stage initial s boundary where
  rip : s.RIP = 0x106ff9
  rdi : s.regValue .rdi = initial.regValue .rdi
  rcx : s.regValue .rcx = 32
  r12 : s.regValue .r12 = initial.regValue .rdx
  r8 : s.regValue .r8 = 0

structure LengthState [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop extends
    Stage initial s boundary where
  rip : s.RIP = 0x107018
  rdi : s.regValue .rdi = initial.regValue .rdi
  r12 : s.regValue .r12 = initial.regValue .rdx
  rax : s.regValue .rax = 263
  rdx : s.regValue .rdx = 32

structure CountState [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop extends
    Stage initial s boundary where
  rip : s.RIP = 0x10703b
  rdi : s.regValue .rdi = initial.regValue .rdi
  r12 : s.regValue .r12 = initial.regValue .rdx
  rdx : s.regValue .rdx = 32
  r15 : s.regValue .r15 = 4

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix
