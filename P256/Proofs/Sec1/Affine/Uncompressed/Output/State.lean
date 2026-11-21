import P256.Proofs.Sec1.Affine.Uncompressed.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Prepared [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110c95
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 744) (canonical (xCoordinate bytes))
  y : Field.MontgomeryAt t (stackPtr s - 712) (canonical (yCoordinate bytes))
  zeroX : Field.MontgomeryAt t (stackPtr s - 592) 0
  zeroY : Field.MontgomeryAt t (stackPtr s - 560) 0
  rax : t.regValue .rax = stackPtr s - 592
  r14 : t.regValue .r14 = stackPtr s - 712
  choice : (t.regValue .rbp).setWidth 8 = if valid bytes then 1 else 0
  infinity : (t.regValue .r15).setWidth 8 = ~~~(if valid bytes then 1 else 0)

structure XSelected [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110ca9
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 664)
    (if valid bytes then canonical (xCoordinate bytes) else 0)
  y : Field.MontgomeryAt t (stackPtr s - 712) (canonical (yCoordinate bytes))
  zeroY : Field.MontgomeryAt t (stackPtr s - 560) 0
  r14 : t.regValue .r14 = stackPtr s - 712
  choice : (t.regValue .rbp).setWidth 8 = if valid bytes then 1 else 0
  infinity : (t.regValue .r15).setWidth 8 = ~~~(if valid bytes then 1 else 0)

structure Selected [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110cc3
  output : t.regValue .rbx = s.regValue .rdi
  x : Field.MontgomeryAt t (stackPtr s - 664)
    (if valid bytes then canonical (xCoordinate bytes) else 0)
  y : Field.MontgomeryAt t (stackPtr s - 632)
    (if valid bytes then canonical (yCoordinate bytes) else 0)
  choice : (t.regValue .rbp).setWidth 8 = if valid bytes then 1 else 0
  infinity : (t.regValue .r15).setWidth 8 = ~~~(if valid bytes then 1 else 0)

end P256.Proofs.Sec1.Affine.Uncompressed.Output
