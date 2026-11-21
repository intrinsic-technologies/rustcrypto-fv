import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.LIR.Fn10a410.Frame
import K256.Proofs.ParseSignature.Contract

namespace K256.Proofs.Generate.Generator.Multiply.AddFrame

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR

def regions (fr : Activation) : List MemoryRegion :=
  [⟨(fr.rsp - 0x218).toNat, 0x218⟩, ⟨fr.rdi.toNat, 120⟩]

structure AtBody {n : Nat} (fr : Activation) (a : Values Value n) (m : Ram) : Prop where
  size : 65 < n
  sp : a[65].get 64 = fr.rsp - 0x218
  df : a[22]'(by omega) = ⟨1, 0⟩
  mx : a[39]'(by omega) = ⟨32, fr.mxcsr⟩
  ftw : a[50]'(by omega) = ⟨16, fr.ftw⟩
  fcw : a[51]'(by omega) = ⟨16, fr.fcw⟩
  dest : memLoad m ((fr.rsp - 0x218) + 0x180) 64 = fr.rdi
  bx : memLoad m (fr.rsp - 48) 64 = fr.rbx
  r12 : memLoad m (fr.rsp - 40) 64 = fr.r12
  r13 : memLoad m (fr.rsp - 32) 64 = fr.r13
  r14 : memLoad m (fr.rsp - 24) 64 = fr.r14
  r15 : memLoad m (fr.rsp - 16) 64 = fr.r15
  bp : memLoad m (fr.rsp - 8) 64 = fr.rbp
  ret : memLoad m fr.rsp 64 = fr.ret

end K256.Proofs.Generate.Generator.Multiply.AddFrame
