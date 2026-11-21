import P256.Proofs.Signing.Interface
import P256.Proofs.Signing.Search
import P256.Proofs.Nonce.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Core

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def frameBase (s : RamState) : BitVec 64 := stackPtr s - 2280

def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.rbp, 8), (.r15, 16), (.r14, 24), (.r13, 32), (.r12, 40), (.rbx, 48)]

structure Frame [bindings : Bindings] (s t : RamState) : Prop where
  machine : SupportedIntegerMachineState bindings.processor t
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  loaded : ProgramLoaded t
  directionFlag : DirectionFlagUnset t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 65, Stack.region s 4584]
  rsp : stackPtr t = frameBase s
  saved : ∀ entry ∈ savedRegisters,
    (Operand.mem (stackPtr s - BitVec.ofNat 64 entry.2) : Operand 64).read t =
      s.regValue entry.1
  returnAddress : (Operand.mem (stackPtr s) : Operand 64).read t =
    (Operand.mem (stackPtr s) : Operand 64).read s
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control

structure StoredArguments (s t : RamState) : Prop where
  output : (Operand.mem (frameBase s + 72) : Operand 64).read t = s.regValue .rdi
  secret : (Operand.mem (frameBase s + 80) : Operand 64).read t = s.regValue .rsi
  digest : (Operand.mem (frameBase s + 88) : Operand 64).read t = s.regValue .rdx
  length : (Operand.mem (frameBase s + 96) : Operand 64).read t = 32

structure Loop [Bindings] (s t : RamState) (state : Nonce.State) : Prop where
  frame : Frame s t
  arguments : StoredArguments s t
  generator : Nonce.GeneratorAt t (frameBase s + 2160) (frameBase s + 272) state
  rbp : t.regValue .rbp = frameBase s + 528
  rbx : t.regValue .rbx = frameBase s + 40
  r13 : t.regValue .r13 = frameBase s + 432
  r14 : t.regValue .r14 = frameBase s + 2160
  r15 : t.regValue .r15 = frameBase s + 1328

structure Candidate [Bindings] (s t : RamState) (state : Nonce.State) (nonce : Nat) : Prop where
  frame : Frame s t
  arguments : StoredArguments s t
  generator : Nonce.GeneratorAt t (frameBase s + 2160) (frameBase s + 272) state
  bytes : ({ start := (frameBase s + 40).toNat, size := 32 } : MemoryRegion).HasBytes
    t.external (Standards.SECG.ECC.Encoding.natToOctets 32 nonce)
  positive : 0 < nonce
  canonical : nonce < Operations.domain.n
  rbp : t.regValue .rbp = frameBase s + 528
  rbx : t.regValue .rbx = frameBase s + 40
  r13 : t.regValue .r13 = frameBase s + 432
  r14 : t.regValue .r14 = frameBase s + 2160
  r15 : t.regValue .r15 = frameBase s + 1328

def initialState (secret : Nat) (digest : ByteArray) : Nonce.State :=
  Standards.RFC.DeterministicSigning.Nonce.initialState Operations.hash 64 32
    Operations.domain.n secret digest

def InitializeContract : Prop :=
  ∀ [Bindings] {s : RamState} {boundary : ReturnBoundary} {secret : Nat}
    {digest : ByteArray}, SignPre s boundary → SignInput s secret digest →
    ∃ fuel t, Advances boundary fuel s t ∧ Loop s t (initialState secret digest) ∧
      t.RIP = 0x10caa5

def NextNonceContract : Prop :=
  (∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state final : Nonce.State} {nonce : Nat}, SignPre s boundary →
    Loop s t state → t.RIP = 0x10caa5 → Search.FirstValid state nonce final →
    ∃ fuel u, 0 < fuel ∧ Advances boundary fuel t u ∧ u.RIP = 0x10cad9 ∧
      Candidate s u final nonce) ∧
  (∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State},
    SignPre s boundary → Loop s t state → t.RIP = 0x10caa5 →
    (¬ ∃ nonce final, Search.FirstValid state nonce final) → Prelude.Diverges boundary t [])

def IterationContract : Prop :=
  ∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    {secret nonce : Nat} {digest : ByteArray}, SignPre s boundary →
    SignInput s secret digest → Candidate s t state nonce → t.RIP = 0x10cad9 →
    (∃ fuel, Advances boundary fuel s t) →
    ∃ fuel u, Advances boundary fuel t u ∧
      ((Ecdsa.signWithNonce secret nonce digest = none ∧ u.RIP = 0x10caa5 ∧ Loop s u state) ∨
        ∃ signature, Ecdsa.signWithNonce secret nonce digest = some signature ∧
          CalleeResult s u boundary 65 4584 ∧
          Nat256At u (s.regValue .rdi) signature.1 ∧
          Nat256At u (s.regValue .rdi + 32) signature.2)

end P256.Proofs.Signing.Core
