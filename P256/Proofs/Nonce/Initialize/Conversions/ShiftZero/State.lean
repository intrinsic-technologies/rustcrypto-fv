import P256.Proofs.Program.Interface
import P256.Proofs.Field.Representation
import P256.Proofs.Program.Stack
import P256.Proofs.Program.SaveRegisters

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

def frame (s : RamState) : List Component :=
  (List.range 16).map (fun i => .reg (BitVec.ofNat 5 i)) ++
    [.flags, .rip, .mem (stackPtr s - 128) 128, .mem (s.regValue .rdi) 32]

structure Stage [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  agrees : AgreesExcept (frame s) s t
  loaded : ProgramLoaded t
  rsp : stackPtr t = stackPtr s - 72
  saved : ∀ entry ∈ savedRegisters,
    (Operand.mem (stackPtr s - BitVec.ofNat 64 entry.2) : Operand 64).read t =
      s.regValue entry.1

structure PreparedState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (a : Limbs) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x10954a
  rsi : t.regValue .rsi = s.regValue .rsi
  rdi : t.regValue .rdi = s.regValue .rdi
  rdx : t.regValue .rdx = 0
  input : readLimbs t (s.regValue .rsi) = a

structure SelectedState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (a : Limbs) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x1095e6
  outputSaved : memLoad t.external (stackPtr s - 56) 64 = s.regValue .rdi
  dil : (t.regValue .rdi).setWidth 8 = 0
  rdx : t.regValue .rdx = 0
  r13 : t.regValue .r13 = a.l3
  r15 : t.regValue .r15 = a.l2
  r10 : t.regValue .r10 = a.l0
  r14 : t.regValue .r14 = a.l1
  r9 : t.regValue .r9 = 0
  r12 : t.regValue .r12 = 0
  r11 : t.regValue .r11 = 0
  rbp : t.regValue .rbp = 0
  rax : t.regValue .rax = 0
  rsi : t.regValue .rsi = 0
  r8 : t.regValue .r8 = 0
  rbx : t.regValue .rbx = 0

structure MixedState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (a : Limbs) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x10963f
  outputSaved : memLoad t.external (stackPtr s - 56) 64 = s.regValue .rdi
  dil : (t.regValue .rdi).setWidth 8 = 0
  rdx : t.regValue .rdx = 1
  rbx : t.regValue .rbx = a.l3
  r8 : t.regValue .r8 = a.l2
  rsi : t.regValue .rsi = a.l1
  rax : t.regValue .rax = a.l0

structure StoredState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (a : Limbs) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x1096d4
  output : Nat256At t (s.regValue .rdi) a.toNat

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
