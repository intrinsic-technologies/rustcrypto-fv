import P256.Proofs.ReadBe.Interface

set_option autoImplicit false

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def frameBase (s : RamState) : BitVec 64 := stackPtr s - 72

def savedRegisters : List X86.Syntax.Reg := [.rbp, .r15, .r14, .r13, .r12, .rbx]

structure Frame [bindings : Bindings] (s t : RamState) : Prop where
  rsp : stackPtr t = frameBase s
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  directionFlag : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control
  frame : MemoryWriteFrame s t #v[registerRegion s .rdx 32, Stack.region s 128]
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  returnAddress : memLoad t.external (stackPtr s) 64 = (returnBoundary s).rip
  saved : ∀ i < 6, memLoad t.external
    (stackPtr s - BitVec.ofNat 64 (8 * (i + 1))) 64 = s.regValue savedRegisters[i]!

structure LoopState [Bindings] (s t : RamState) (input : ByteArray) (k : Nat) : Prop where
  frame : Frame s t
  rip : t.RIP = if k < 4 then 0x11914e else 0x119170
  bits : t.regValue .rbx = 256
  size : t.regValue .rbp = 32
  output : t.regValue .r14 = s.regValue .rdx
  offset : t.regValue .r15 = BitVec.ofNat 64 (8*k)
  remaining : t.regValue .r13 = BitVec.ofNat 64 (32-8*k)
  source : t.regValue .r12 = s.regValue .rdi + BitVec.ofNat 64 (32-8*k)
  inputBytes : (registerRegion s .rdi 32).HasBytes t.external input
  words : ∀ j < k, memLoad t.external (s.regValue .rdx + BitVec.ofNat 64 (8*j)) 64 =
    BitVec.ofNat 64 (Arith.uint input / 2^(64*j))

end P256.Proofs.ReadBe
