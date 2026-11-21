import P256.Proofs.Sec1.SquareRoot.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def exponentFrameBase (s : RamState) : BitVec 64 := s.regValue .rsp - 1416

def exponentSavedRegisters : List X86.Syntax.Reg := [.rbp, .r15, .r14, .r13, .r12, .rbx]

def exponentWordAt (s : RamState) (address : BitVec 64) (value : BitVec 64) : Prop :=
  (Operand.mem address : Operand 64).read s = value

structure ExponentFrame [bindings : Bindings] (s t : RamState) : Prop where
  rsp : t.regValue .rsp = exponentFrameBase s
  machine : SupportedIntegerMachineState bindings.processor t
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  directionFlag : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 32, Stack.region s 1584]
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  returnAddress : exponentWordAt t (s.regValue .rsp)
    ((Operand.mem (s.regValue .rsp) : Operand 64).read s)
  saved : ∀ i < 6, exponentWordAt t
    (s.regValue .rsp - BitVec.ofNat 64 (8 * (i + 1))) (s.regValue exponentSavedRegisters[i]!)
  outputPointer : exponentWordAt t (exponentFrameBase s + 0x2a0) (s.regValue .rdi)

structure ExponentConstants (s t : RamState) (x : Nat) : Prop where
  input : ResidueAt t (s.regValue .rsi) x
  table : ∀ i < 16, Field.MontgomeryAt t
    (exponentFrameBase s + 0x338 + BitVec.ofNat 64 (32 * i))
    (x ^ i % P256.Spec.Operations.domain.p)
  exponent : Nat256At t (exponentFrameBase s + 0x538) sqrtExponent
  initialWindow : (Operand.mem (exponentFrameBase s + 0x78) : Operand 32).read t = 16
  modulus0 : exponentWordAt t (exponentFrameBase s + 0x88) 0xffffffffffffffff
  modulus1 : exponentWordAt t (exponentFrameBase s + 0x80) 0xffffffff
  modulus2 : exponentWordAt t (exponentFrameBase s + 0x98) 0
  modulus3 : exponentWordAt t (exponentFrameBase s + 0x90) 0xffffffff00000001
  firstWindow : exponentWordAt t (exponentFrameBase s + 0x2a8) 15
  parameterPointer : exponentWordAt t (exponentFrameBase s + 0x2b8) (s.regValue .rsi + 32)
  firstWord : exponentWordAt t (exponentFrameBase s + 0x2b0) 3
  inverse : exponentWordAt t (exponentFrameBase s + 0x2e0) 0xffffffffffffffff
  initialMask : exponentWordAt t (exponentFrameBase s + 0x2d8) 3
  negativeInverse : exponentWordAt t (exponentFrameBase s + 0x2c8) 1

structure ExponentPosition [Bindings] (s t : RamState) (x n : Nat) : Prop where
  frame : ExponentFrame s t
  constants : ExponentConstants s t x
  word : t.regValue .rbp = BitVec.ofNat 64 (n / 16)
  savedWord : exponentWordAt t (exponentFrameBase s + 0x2c0) (BitVec.ofNat 64 (n / 16))
  window : t.regValue .r14 = BitVec.ofNat 64 (n % 16)
  firstWord : t.regValue .rbx = 3
  firstWindow : t.regValue .r13 = 15
  parameterPointer : t.regValue .r15 = s.regValue .rsi + 32
  modulus0 : t.regValue .r11 = 0xffffffffffffffff
  inverse : t.regValue .r12 = 0xffffffffffffffff

structure ExponentLoopState [Bindings] (s t : RamState) (x remaining : Nat) : Prop where
  frame : ExponentFrame s t
  constants : ExponentConstants s t x
  rip : t.RIP = 0x1154c5
  word : t.regValue .rbp = BitVec.ofNat 64 ((remaining - 1) / 16)
  savedWord : exponentWordAt t (exponentFrameBase s + 0x2c0)
    (BitVec.ofNat 64 ((remaining - 1) / 16))
  window : t.regValue .r14 = BitVec.ofNat 64 ((remaining - 1) % 16 + 1)
  firstWord : t.regValue .rbx = 3
  firstWindow : t.regValue .r13 = 15
  parameterPointer : t.regValue .r15 = s.regValue .rsi + 32
  modulus0 : t.regValue .r11 = 0xffffffffffffffff
  inverse : t.regValue .r12 = 0xffffffffffffffff
  accumulator : Field.MontgomeryAt t (exponentFrameBase s + 0x30)
    (x ^ (sqrtExponent / 16 ^ remaining) % P256.Spec.Operations.domain.p)

structure ExponentFinishState [Bindings] (s t : RamState) (x : Nat) : Prop where
  frame : ExponentFrame s t
  rip : t.RIP = 0x1158ff
  accumulator : Field.MontgomeryAt t (exponentFrameBase s + 0x30)
    (x ^ sqrtExponent % P256.Spec.Operations.domain.p)

end P256.Proofs.Sec1.SquareRoot
