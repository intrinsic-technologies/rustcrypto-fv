import P256.Proofs.Verifying.Core.Prepare.Pointers

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

structure Reading [Bindings] (s t : RamState) : Prop extends Frame s t, Prepare.Pointers s t where
  rip : t.RIP = 0x10dc23
  source : t.regValue .rdi = frameBase s+424
  destination : t.regValue .rdx = frameBase s
  count : t.regValue .rsi = 32
  limbs : t.regValue .rcx = 4
  bits : t.regValue .r8 = 256

def setupClobbers (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .flags, .rip,
    .mem (frameBase s + 128) 1, .mem (frameBase s + 576) 4,
    .mem (frameBase s + 24) 8, .mem (frameBase s + 16) 8,
    .mem (frameBase s + 8) 8, .mem (frameBase s + 0) 8]

end P256.Proofs.Verifying.Core.Digest
