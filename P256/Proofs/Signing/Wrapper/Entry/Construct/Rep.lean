import P256.Proofs.Signing.Wrapper.Entry.Construct.Memory
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct.Rep

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

theorem run [bindings : Bindings] {initial s : RamState} {secret message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices signingKeyTrySign initial [secret,message] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (hb : MachineRamUnitStrideDecodable bindings s) (ready : ReadyToStep s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP=0x1026f1) (src : s.regValue .rsi=stackPtr initial-448#64)
    (dst : s.regValue .rdi=stackPtr initial-144#64) (count : s.regValue .rcx=12) :
    ∃ t, Advances (returnBoundary initial) 12 s t ∧ ReadyToStep t ∧ t.RIP=0x1026f4 ∧
      AgreesExcept [.reg 6,.reg 7,.reg 1,.mem (stackPtr initial-144) 96,.rip] s t ∧
      (∀ i<96, t.external[stackPtr initial-144+BitVec.ofNat 64 i]?=
        s.external[stackPtr initial-448+BitVec.ofNat 64 i]?) := by
  have stack : Stack.Valid initial 5112 := call.stackAvailable.1
  have hn : (rcx.read s).toNat=12 := by change (s.regValue .rcx).toNat=12; rw [count]; rfl
  have read : MemReadable s (rsi.read s) (8*12) := by
    change MemReadable s (s.regValue .rsi) 96
    rw [src]
    exact readable_of_grow (stack_sub_readable stack (offset := 448) (by decide) (by decide)) grow
  have write : Writable s (rdi.read s) (8*12) := by
    change Writable s (s.regValue .rdi) 96
    rw [dst]
    exact stack_buffer_writable stack (call_stack_avoids (routine := signingKeyTrySign) call)
      grow (by decide) (by decide) (by decide)
  have apart : (rsi.read s).toNat+8*12≤(rdi.read s).toNat ∨
      (rdi.read s).toNat+8*12≤(rsi.read s).toNat := by
    change (s.regValue .rsi).toNat+96≤(s.regValue .rdi).toNat ∨
      (s.regValue .rdi).toNat+96≤(s.regValue .rsi).toNat
    rw [src,dst,stack_sub_toNat stack (by decide : 448≤5112),
      stack_sub_toNat stack (by decide : 144≤5112)]
    have bounds := stack_bounds stack
    left; omega
  have codeApart : RangeApart (rdi.read s) (8*12) 0x1026f1 3 := by
    change RangeApart (s.regValue .rdi) 96 _ _
    rw [dst]
    exact stack_buffer_code_apart stack (call_stack_avoids (routine := signingKeyTrySign) call)
      (offset := 144) (len := 96) (by decide) (by decide)
      (codeOffset := 0x26f1) (codeLength := 3) (by decide)
  have pre := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory
    rip direction.df hn read write apart codeApart
  obtain ⟨run,rt,effect,bytes⟩ := P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution
    hb.stringStride ready
    (programText_slice (programLoaded_codeIn loaded) 0x26f1 _ (by decide) (by decide +kernel))
    pre hn (boundary_ne_program outside (inProgram_of_textOffset 0x26f1 (by decide)))
    (boundary_ne_program outside (inProgram_of_textOffset 0x26f4 (by decide)))
  simp only [Nat.max_eq_left (by decide : 1≤12)] at run rt effect bytes
  generalize ht : nextStates 12 s=t at run rt effect bytes
  refine ⟨t,run,rt,effect.rip,?_,?_⟩
  · simpa only [repMovsqEffect_components,hn,show rdi.read s=stackPtr initial-144#64 from dst,
      Nat.reduceMul,BitVec.ofNat_eq_ofNat] using effect.agrees
  · simpa only [show rdi.read s=stackPtr initial-144#64 from dst,
      show rsi.read s=stackPtr initial-448#64 from src,Nat.reduceMul,BitVec.ofNat_eq_ofNat] using bytes

end P256.Proofs.Signing.Wrapper.Entry.Construct.Rep
