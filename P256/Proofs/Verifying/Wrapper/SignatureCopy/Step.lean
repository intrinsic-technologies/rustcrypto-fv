import P256.Proofs.Verifying.Wrapper.LocalMemory
import P256.Proofs.Verifying.Wrapper.SignatureCopy.Word8
import P256.Proofs.Verifying.Wrapper.SignatureCopy.Word32

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.SignatureCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem step8 [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (codeOffset sourceOffset destinationOffset : Nat) (source : BitVec 8) (destination : BitVec 8)
    (sourceEq : source.signExtend 64 = BitVec.ofNat 64 sourceOffset)
    (destinationEq : destination.signExtend 64 = BitVec.ofNat 64 destinationOffset)
    (sourceBound : sourceOffset+8 ≤ 240) (destinationBound : destinationOffset+8 ≤ 64)
    (codeBound : codeOffset+10 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 10 = Word8.bytes source destination)
    (rip : s.RIP = Extracted.textAddress+BitVec.ofNat 64 codeOffset) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = Extracted.textAddress+BitVec.ofNat 64 (codeOffset+10) ∧
      memLoad t.external (stackPtr s+BitVec.ofNat 64 destinationOffset) 64 =
        memLoad s.external (stackPtr s+BitVec.ofNat 64 sourceOffset) 64 ∧
      AgreesExcept [.reg 0,.mem (stackPtr s+BitVec.ofNat 64 destinationOffset) 8,.rip] s t := by
  have first : Extracted.textAddress+BitVec.ofNat 64 codeOffset+(5 : BitVec 64) =
      Extracted.textAddress+BitVec.ofNat 64 (codeOffset+5) := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  have last : Extracted.textAddress+BitVec.ofNat 64 codeOffset+(10 : BitVec 64) =
      Extracted.textAddress+BitVec.ofNat 64 (codeOffset+10) := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  have pre : Word8.Pre (Extracted.textAddress+BitVec.ofNat 64 codeOffset) source destination s := by
    refine ⟨rip,?_,?_,?_⟩
    · change MemReadable s (stackPtr s+source.signExtend 64) 8
      rw [sourceEq]
      exact state.local_readable call.stackAvailable.1 (by omega)
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s
        (stackPtr s+destination.signExtend 64) 8
      rw [destinationEq]
      exact state.local_writable call (by omega) (by decide)
    · change RangeApart (stackPtr s+destination.signExtend 64) 8 _ 10
      rw [destinationEq]
      exact state.local_code call (by omega) (by omega)
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Word8.run (returnBoundary initial)
    (Extracted.textAddress+BitVec.ofNat 64 codeOffset) source destination
    (by rw [first]; exact boundary_ne_program outside (inProgram_of_textOffset _ (by omega)))
    (by rw [last]; exact boundary_ne_program outside (inProgram_of_textOffset _ codeBound))
    s (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) codeOffset (Word8.bytes source destination)
      (by simpa only [Word8.bytes,immBytes_length,List.length_append,List.length_cons,List.length_nil,
          Nat.reduceAdd] using Nat.le_of_lt codeBound) codeBytes) pre
  have ag : AgreesExcept [.reg 0,.mem (stackPtr s+BitVec.ofNat 64 destinationOffset) 8,.rip] s t := by
    simpa only [Word8.effect,Effect.components,Write.component,Operand.component,
      List.map,List.cons_append,List.nil_append,Nat.reduceDiv,destinationEq,stackPtr,Operand.read_reg64,gprIndex,State.regValue] using effect.agrees
  have frame : MemoryWriteFrame s t #v[workRegion initial] := by
    apply ag.memoryWriteFrame
    intro c hc address covered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨workRegion initial,by simp,state.local_work call.stackAvailable.1 (by omega) covered⟩
  refine ⟨fuel,t,run,state.after_work call ready ag frame (by simp) (by simp) (by simp),
    effect.rip.trans last,?_,ag⟩
  have value := effect.writes.2
  change memLoad t.external (stackPtr s+destination.signExtend 64) 64 =
    memLoad s.external (stackPtr s+source.signExtend 64) 64 at value
  simpa only [destinationEq,sourceEq] using value

theorem step32 [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (codeOffset sourceOffset destinationOffset : Nat) (source : BitVec 32) (destination : BitVec 8)
    (sourceEq : source.signExtend 64 = BitVec.ofNat 64 sourceOffset)
    (destinationEq : destination.signExtend 64 = BitVec.ofNat 64 destinationOffset)
    (sourceBound : sourceOffset+8 ≤ 240) (destinationBound : destinationOffset+8 ≤ 64)
    (codeBound : codeOffset+13 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 13 = Word32.bytes source destination)
    (rip : s.RIP = Extracted.textAddress+BitVec.ofNat 64 codeOffset) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = Extracted.textAddress+BitVec.ofNat 64 (codeOffset+13) ∧
      memLoad t.external (stackPtr s+BitVec.ofNat 64 destinationOffset) 64 =
        memLoad s.external (stackPtr s+BitVec.ofNat 64 sourceOffset) 64 ∧
      AgreesExcept [.reg 0,.mem (stackPtr s+BitVec.ofNat 64 destinationOffset) 8,.rip] s t := by
  have first : Extracted.textAddress+BitVec.ofNat 64 codeOffset+(8 : BitVec 64) =
      Extracted.textAddress+BitVec.ofNat 64 (codeOffset+8) := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  have last : Extracted.textAddress+BitVec.ofNat 64 codeOffset+(13 : BitVec 64) =
      Extracted.textAddress+BitVec.ofNat 64 (codeOffset+13) := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  have pre : Word32.Pre (Extracted.textAddress+BitVec.ofNat 64 codeOffset) source destination s := by
    refine ⟨rip,?_,?_,?_⟩
    · change MemReadable s (stackPtr s+source.signExtend 64) 8
      rw [sourceEq]
      exact state.local_readable call.stackAvailable.1 (by omega)
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s
        (stackPtr s+destination.signExtend 64) 8
      rw [destinationEq]
      exact state.local_writable call (by omega) (by decide)
    · change RangeApart (stackPtr s+destination.signExtend 64) 8 _ 13
      rw [destinationEq]
      exact state.local_code call (by omega) (by omega)
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Word32.run (returnBoundary initial)
    (Extracted.textAddress+BitVec.ofNat 64 codeOffset) source destination
    (by rw [first]; exact boundary_ne_program outside (inProgram_of_textOffset _ (by omega)))
    (by rw [last]; exact boundary_ne_program outside (inProgram_of_textOffset _ codeBound))
    s (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) codeOffset (Word32.bytes source destination)
      (by simpa only [Word32.bytes,immBytes_length,List.length_append,List.length_cons,List.length_nil,
          Nat.reduceAdd] using Nat.le_of_lt codeBound) codeBytes) pre
  have ag : AgreesExcept [.reg 0,.mem (stackPtr s+BitVec.ofNat 64 destinationOffset) 8,.rip] s t := by
    simpa only [Word32.effect,Effect.components,Write.component,Operand.component,
      List.map,List.cons_append,List.nil_append,Nat.reduceDiv,destinationEq,stackPtr,Operand.read_reg64,gprIndex,State.regValue] using effect.agrees
  have frame : MemoryWriteFrame s t #v[workRegion initial] := by
    apply ag.memoryWriteFrame
    intro c hc address covered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨workRegion initial,by simp,state.local_work call.stackAvailable.1 (by omega) covered⟩
  refine ⟨fuel,t,run,state.after_work call ready ag frame (by simp) (by simp) (by simp),
    effect.rip.trans last,?_,ag⟩
  have value := effect.writes.2
  change memLoad t.external (stackPtr s+destination.signExtend 64) 64 =
    memLoad s.external (stackPtr s+source.signExtend 64) 64 at value
  simpa only [destinationEq,sourceEq] using value

end P256.Proofs.Verifying.Wrapper.SignatureCopy
