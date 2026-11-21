import P256.Proofs.Ecdh.Interface
import P256.Proofs.Program.CalleeStack
import P256.Proofs.EcdhWrapper.Peer.Pad.Memory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Multiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def scalarLayout : StackCallLayout 4104 32 32 3464 :=
  ⟨512,160,504,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

def peerLayout : StackCallLayout 4104 72 32 3464 :=
  ⟨512,336,504,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem child_pre [bindings : Bindings] {initial t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (hb : MachineRamUnitStrideDecodable bindings t)
    (hm : SupportedIntegerMachineState bindings.processor t)
    (direction : DirectionFlagUnset t) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (rip : t.RIP=0x100000) (rsp : stackPtr t=stackPtr initial-512)
    (rdi : t.regValue .rdi=stackPtr initial-504)
    (rsi : t.regValue .rsi=stackPtr initial-160)
    (rdx : t.regValue .rdx=stackPtr initial-336)
    (ret : (returnBoundary t).rip=0x106bd5) : Ecdh.Pre t (returnBoundary initial) := by
  have avoid := call_stack_avoids (routine := ecdhDiffieHellman) call
  have inProgram : InProgram (returnBoundary t).rip := by
    rw [ret]; exact inProgram_of_textOffset 0x6bd5 (by decide)
  have scalar : CalleePre t (returnBoundary initial) 0x100000 32 32 3464 :=
    CalleePre.of_stack_region call.stackAvailable.1 avoid outside scalarLayout hb hm direction
      loaded grow rip rsp rsi rdi inProgram
  have point : CalleePre t (returnBoundary initial) 0x100000 72 32 3464 .rdx :=
    CalleePre.of_stack_region call.stackAvailable.1 avoid outside peerLayout hb hm direction
      loaded grow rip rsp rdx rdi inProgram
  exact ⟨scalar,point.inputBounded,point.inputAllocated,
    point.separation 0 1 (by decide),point.separation 0 2 (by decide)⟩

end P256.Proofs.EcdhWrapper.Multiply
