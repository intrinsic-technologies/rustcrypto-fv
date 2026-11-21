import P256.Proofs.EcdhWrapper.Peer.Result.Memory
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Result

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

theorem copy [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (hb : MachineRamUnitStrideDecodable bindings s) (ready : ReadyToStep s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP=0x106bc2) (src : s.regValue .rsi=stackPtr initial-128#64)
    (dst : s.regValue .rdi=stackPtr initial-336#64) (count : s.regValue .rcx=9) :
    ∃ t, Advances (returnBoundary initial) 9 s t ∧ ReadyToStep t ∧ t.RIP=0x106bc5 ∧
      AgreesExcept [.reg 6,.reg 7,.reg 1,.mem (stackPtr initial-336) 72,.rip] s t ∧
      (∀ i<72, t.external[stackPtr initial-336+BitVec.ofNat 64 i]?=
        s.external[stackPtr initial-128+BitVec.ofNat 64 i]?) := by
  have stack : Stack.Valid initial 4104 := call.stackAvailable.1
  have hn : (rcx.read s).toNat=9 := by change (s.regValue .rcx).toNat=9; rw [count]; rfl
  have read : MemReadable s (rsi.read s) (8*9) := by
    change MemReadable s (s.regValue .rsi) 72
    rw [src]
    exact readable_of_grow (stack_sub_readable stack (offset := 128) (by decide) (by decide)) grow
  have write : Writable s (rdi.read s) (8*9) := by
    change Writable s (s.regValue .rdi) 72
    rw [dst]
    have readable := readable_of_grow
      (stack_sub_readable stack (offset := 336) (len := 72) (by decide) (by decide)) grow
    refine ⟨readable,tables_of_not_reserved (by decide) readable.low ?_⟩
    intro i hi reserved
    exact (call.separation.2 (callStack ecdhDiffieHellman initial) (by simp)).2 _
      (stack_component_within (routine := ecdhDiffieHellman) stack
        (offset := 336) (len := 72) (by decide) (by decide) ⟨i,hi,rfl⟩) (.inr reserved)
  have apart : (rsi.read s).toNat+8*9≤(rdi.read s).toNat ∨
      (rdi.read s).toNat+8*9≤(rsi.read s).toNat := by
    change (s.regValue .rsi).toNat+72≤(s.regValue .rdi).toNat ∨
      (s.regValue .rdi).toNat+72≤(s.regValue .rsi).toNat
    rw [src,dst,stack_sub_toNat stack (by decide : 128≤4104),
      stack_sub_toNat stack (by decide : 336≤4104)]
    have bounds := stack_bounds stack
    right; omega
  have codeApart : RangeApart (rdi.read s) (8*9) 0x106bc2 3 := by
    change RangeApart (s.regValue .rdi) 72 _ _
    rw [dst]
    exact stack_buffer_code_apart stack (call_stack_avoids (routine := ecdhDiffieHellman) call)
      (offset := 336) (len := 72) (by decide) (by decide)
      (codeOffset := 0x6bc2) (codeLength := 3) (by decide)
  have pre := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory
    rip direction.df hn read write apart codeApart
  obtain ⟨run,rt,effect,bytes⟩ := P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution
    hb.stringStride ready
    (programText_slice (programLoaded_codeIn loaded) 0x6bc2 _ (by decide) (by decide +kernel))
    pre hn (boundary_ne_program outside (inProgram_of_textOffset 0x6bc2 (by decide)))
    (boundary_ne_program outside (inProgram_of_textOffset 0x6bc5 (by decide)))
  simp only [Nat.max_eq_left (by decide : 1≤9)] at run rt effect bytes
  generalize ht : nextStates 9 s=t at run rt effect bytes
  refine ⟨t,run,rt,effect.rip,?_,?_⟩
  · simpa only [repMovsqEffect_components,hn,show rdi.read s=stackPtr initial-336#64 from dst,
      Nat.reduceMul,BitVec.ofNat_eq_ofNat] using effect.agrees
  · simpa only [show rdi.read s=stackPtr initial-336#64 from dst,
      show rsi.read s=stackPtr initial-128#64 from src,Nat.reduceMul,BitVec.ofNat_eq_ofNat] using bytes

end P256.Proofs.EcdhWrapper.Peer.Result
