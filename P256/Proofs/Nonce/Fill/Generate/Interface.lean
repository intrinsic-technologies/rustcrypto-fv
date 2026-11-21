import P256.Proofs.Nonce.Fill.Frame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Generate

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Registers (initial s : RamState) : Prop where
  r12 : s.regValue .r12 = initial.regValue .rdi + 40
  rbx : s.regValue .rbx = 0x11c930
  rbp : s.regValue .rbp = 32
  r14 : s.regValue .r14 = initial.regValue .rsi
  r15 : s.regValue .r15 = 32

structure Ready [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : State) : Prop extends Frame initial s, Slots initial s, Registers initial s where
  rip : s.RIP = 0x1073c2
  rdi : s.regValue .rdi = initial.regValue .rdi + 8
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress state

structure HasValue [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : State) : Prop extends Frame initial s, Slots initial s, Registers initial s where
  rip : s.RIP = 0x1073c7
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress (updateValue state)

structure Copied [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : State) : Prop extends Frame initial s, Slots initial s where
  rip : s.RIP = 0x1073d2
  rbp : s.regValue .rbp = 32
  r15 : s.regValue .r15 = 32
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress (updateValue state)
  output : (registerRegion initial .rsi 32).HasBytes s.external (updateValue state).value

end P256.Proofs.Nonce.Fill.Generate
