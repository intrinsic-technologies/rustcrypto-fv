import P256.Proofs.Program.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation
import P256.Proofs.Sec1.Interface
import P256.Spec.Generate

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

def source (s : RamState) : BitVec 64 := memLoad s.external (s.regValue .rsi) 64

def inputRegion (s : RamState) (input : ByteArray) : MemoryRegion :=
  ⟨(source s).toNat, input.size⟩

def writes (s : RamState) : Vector MemoryRegion 3 :=
  #v[registerRegion s .rdi 104, registerRegion s .rsi 16, Stack.region s 3624]

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) (input : ByteArray) : Prop
    extends CalleePre s boundary 0x100bd0 16 104 3624 where
  length : memLoad s.external (s.regValue .rsi + 8) 64 = BitVec.ofNat 64 input.size
  bytes : (inputRegion s input).HasBytes s.external input
  bounded : (inputRegion s input).Bounded
  allocatedInput : (inputRegion s input).Allocated s.external
  separateInput : ∀ region ∈ (writes s).toList, (inputRegion s input).Disjoint region
  descriptorAvoids : (registerRegion s .rsi 16).Avoids (fun a => InProgram a ∨ InPageTables a)

structure Result [bindings : Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = (returnBoundary s).rsp
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  calleeSaved : CalleeSavedRegistersUnchanged s t
  directionFlag : DirectionFlagUnset t
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control
  frame : MemoryWriteFrame s t (writes s)
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome

def Contract (bindings : Bindings) : Prop :=
  ∀ (s : RamState) (boundary : ReturnBoundary) (input : ByteArray) (d : Nat),
    Pre s boundary input → Ecdh.drawNonzeroScalar input = some d →
    ∃ t, Result s t boundary ∧
      SecretKeyFromBytes.Scalar.Nat256At t (s.regValue .rdi) d ∧
      Sec1.AffineAt t (s.regValue .rdi + 32) (Points.mul d Operations.domain.G) ∧
      t.regValue .rax = s.regValue .rdi

end P256.Proofs.Generate.Sampler
