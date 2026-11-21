import Sha2.Proofs.Wrapper.Absorb.Branch
import Sha2.Proofs.Wrapper.Absorb.FillSetup
import Sha2.Proofs.Wrapper.Absorb.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

structure Filled [Bindings] (initial s : RamState) (inputs : Array Input) (index : Nat) (v : Variant := .sha256) : Prop
    extends Preserved (v := v) initial s where
  remaining : index < inputs.size
  bound : 64-(prefixMessage inputs index).size%64 ≤ inputs[index].bytes.size
  hashWords : HashStateAt s (stackPtr initial-88)
    (compressBlocks v.initialHash (prefixMessage inputs index))
  blocks : memLoad s.external (stackPtr initial-56) 64 =
    BitVec.ofNat 64 ((prefixMessage inputs index).size/64)
  bytes : (⟨(stackPtr initial-152).toNat,64⟩ : MemoryRegion).HasBytes s.external
    (filledBlock (prefixMessage inputs index) inputs[index].bytes)
  source : s.regValue .rbx=inputs[index].address+BitVec.ofNat 64 (64-(prefixMessage inputs index).size%64)
  length : s.regValue .rbp=BitVec.ofNat 64 (inputs[index].bytes.size-(64-(prefixMessage inputs index).size%64))
  indexRegister : s.regValue .r14=BitVec.ofNat 64 index
  countRegister : s.regValue .r15=BitVec.ofNat 64 inputs.size

theorem fill_copy {v : Variant} [Bindings] {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context (v := v) initial inputs) (input : Prepared (v := v) initial s inputs index)
    (rip : s.RIP=(v.pc 0x107))
    (enough : 64-(prefixMessage inputs index).size%64 ≤ (inputs[index]'input.remaining).bytes.size) :
    ∃ t, Filled (v := v) initial t inputs index ∧ t.RIP=(v.pc 0x11f) := by
  let i : Fin inputs.size := ⟨index,input.remaining⟩
  have enough' : 64-(prefixMessage inputs index).size%64 ≤ inputs[i].bytes.size := enough
  have extent : (prefixMessage inputs index).size%64 + (64-(prefixMessage inputs index).size%64) ≤ 64 := by omega
  obtain ⟨fuel,b,run,ready,_,setup⟩ :=
    FillSetup.run (returnBoundary initial) (validCall_returnBoundary ctx.machine ctx.call).2.2 s
      (supportedMachine_readyToStep input.machine) (FillSetup.code input.loaded) rip
  have frame : AgreesExcept [.reg 3,.reg 7,.reg 6,.flags,.rip] s b := setup.agrees
  have buffered := buffered_of_agrees ctx input.toBuffered run ready frame (by simp [Component.Covers]) (by simp)
  have destinationB : b.regValue .rdi=stackPtr initial-152+BitVec.ofNat 64 ((prefixMessage inputs index).size%64) := by
    have write : b.regValue .rdi=rspOf s+s.regValue .r12+(192#64) := setup.writes.2.1
    rw [write,input.position,BitVec.add_assoc,
      BitVec.add_comm (BitVec.ofNat 64 ((prefixMessage inputs index).size%64)) (192#64),
      ← BitVec.add_assoc,stack_address input.rsp]
    rfl
  have sourceB : b.regValue .rsi=inputs[i].address+BitVec.ofNat 64 0 := by
    have write : b.regValue .rsi=s.regValue .r13 := setup.writes.2.2
    change b.regValue .rsi=(inputs[index]'input.remaining).address+(0#64)
    rw [BitVec.add_zero]
    exact write.trans input.source
  have countB : b.regValue .rdx=BitVec.ofNat 64 (64-(prefixMessage inputs index).size%64) :=
    (frame.read (n:=64) (r:=2) (by simp)).trans input.space
  obtain ⟨t,copy⟩ := Copy.copy ctx buffered.toPreserved .fill i (offset:=0)
    (by omega) extent setup.rip destinationB sourceB countB
  have hash := hashState_of_bytes buffered.hashWords
    (copy.bytes_unchanged ctx extent (offset:=88) (len:=32) (by decide) (by decide) (.inr (by omega)))
  have tail := copied_tail ctx buffered copy enough' extent
  refine ⟨t,⟨copy.preserved,input.remaining,enough,hash,?_,?_,?_,?_,?_,?_⟩,copy.rip.trans (by cases v <;> rfl)⟩
  · rw [← buffered.blocks]
    apply memLoad_congr
    intro j hj
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    exact copy.bytes_unchanged ctx extent (offset:=56) (len:=8)
      (by decide) (by decide) (.inr (by omega)) j hj
  · have sized := filledBlock_size (prefixMessage inputs index) inputs[i].bytes enough'
    change (⟨(stackPtr initial-152).toNat,64⟩ : MemoryRegion).HasBytes t.external
      (filledBlock (prefixMessage inputs index) inputs[i].bytes)
    exact ⟨sized,tail.2⟩
  · have write : b.regValue .rbx=s.regValue .rdx+s.regValue .r13 := setup.writes.1
    rw [copy.abi.1 .rbx (by simp),write,input.space,input.source,BitVec.add_comm]
  · have kept := (copy.abi.1 .rbp (by simp)).trans
      ((frame.read (n:=64) (r:=5) (by simp)).trans input.rest)
    exact kept.trans (BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) enough)
  · exact (copy.abi.1 .r14 (by simp)).trans ((frame.read (n:=64) (r:=14) (by simp)).trans input.indexRegister)
  · exact (copy.abi.1 .r15 (by simp)).trans ((frame.read (n:=64) (r:=15) (by simp)).trans input.countRegister)

end Sha2.Proofs.Wrapper.Absorb
