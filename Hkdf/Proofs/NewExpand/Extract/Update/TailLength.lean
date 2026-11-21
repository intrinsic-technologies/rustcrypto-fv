import Hkdf.Proofs.NewExpand.Extract.Frame
import Hkdf.Proofs.NewExpand.Extract.Update.Arguments
import Hkdf.Proofs.NewExpand.Extract.Update.Frame
import Hkdf.Proofs.Common.Instructions.ByteStore

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Instructions
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem outsideByteStore {s t : RamState} {dest : BitVec 64}
    (agrees : AgreesExcept [.mem dest 1,.rip] s t) (a : BitVec 64) (away : a ≠ dest) : t.external[a]? = s.external[a]? := by
    apply agrees.byte
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rintro ⟨i,hi,eq⟩
      have : i = 0 := by omega
      subst i
      apply away
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using eq
    · exact id

def CopyPath.storeOffset : CopyPath → Nat
  | .short => 0xfc7a
  | .residual => 0xfcb2

def CopyPath.storePc (path : CopyPath) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 path.storeOffset

theorem storeLength [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm)
    (frame : Frame initial s boundary) (path : CopyPath) (rip : s.RIP = path.storePc)
    {count : Nat} (small : count < 64) (countR : s.regValue .r14 = BitVec.ofNat 64 count) :
    ∃ t, Frame initial t boundary ∧ t.RIP = path.storePc + (8 : BitVec 64) ∧
      t.external[base initial + 183]? = some (UInt8.ofNat count) ∧
      AgreesExcept [.mem (base initial + 183) 1,.rip] s t := by
  have dest : base initial + 183 = stackPtr initial - 273 := by
    unfold base
    bv_omega
  have address : rspOf s + 183 = base initial + 183 := by
    rw [show rspOf s = stackPtr s from Operand.read_reg64 s 4, frame.rsp]
  have avoid : (Stack.region initial 2264).Avoids InProgram := stackAvoid pre _ (by simp)
  have step : StepEffect (StorePre path.storePc 8 (fun s => rspOf s + 183) 1)
      (codeRange path.storePc [0x44,0x88,0xb4,0x24,0xb7,0,0,0])
      (storeEffect path.storePc 8 (fun s => rspOf s + 183)
        (fun s => (Operand.reg 14 : Operand 8).read s)) :=
    mov_m8_r8_effect_step path.storePc 0x44 (by simp [RexPrefix]) 6
      (.sib 4 none 0 (.d32 183)) (by decide) rfl rfl
  have writable : MemWritable s (rspOf s + 183) 1 := by
    rw [address, dest]
    exact stack_writable1 pre.call.stack pre.call.stackAvoid frame.allocated (by decide)
  have apart : RangeApart (rspOf s + 183) 1 path.storePc 8 := by
    rw [address, dest]
    exact stack_codeApart pre.call.stack avoid (by decide) (by decide)
      (by cases path <;> decide)
  have code := programText_slice (programLoaded_codeIn frame.loaded) path.storeOffset
    [0x44,0x88,0xb4,0x24,0xb7,0,0,0] (by cases path <;> decide) (by cases path <;> decide +kernel)
  obtain ⟨t,run,ready,effect⟩ := step.advances (supportedMachine_readyToStep frame.machine) code
    ⟨rip, writable, apart⟩ (by
      apply boundary_ne_program pre.call.outerBoundary
      cases path
      · exact inProgram_of_textOffset 0xfc82 (by decide)
      · exact inProgram_of_textOffset 0xfcba (by decide))
  have agrees : AgreesExcept [.mem (base initial + 183) 1,.rip] s t := by
    simpa only [storeEffect_components, Nat.reduceDiv, address] using effect.agrees
  have writes : WritesWithin [.mem (base initial + 183) 1,.rip] #v[Stack.region initial 2264] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [dest] at ha
      exact ⟨_, by simp, stackRegion_contains_sub pre.call.stack.2.2.1
        (offset := 273) (by decide) (by decide) ha⟩
    · exact ha.elim
  have running := frame.toRunning.of_agrees run ready agrees writes (stackAvoid pre) (by simp)
  have saved : (Component.mem (stackPtr initial - 48) 56).Agrees s t := by
    rw [show stackPtr initial - 48 = base initial + BitVec.ofNat 64 408 by unfold base; bv_omega]
    exact unchangedSlice (offset := 408) (changed := 183) (outsideByteStore agrees)
      (by decide) (by decide) (.inr (by decide))
  have frameT : Frame initial t boundary := {
    toRunning := running
    rsp := (agrees.read (n := 64) (r := 4) (by simp)).trans frame.rsp
    toSaved := frame.toSaved.of_agrees saved (agrees.mxcsr (by simp)) (agrees.fcw (by simp))
    outputPtr := (agrees_memLoad (unchangedSlice (offset := 80) (changed := 183) (outsideByteStore agrees)
      (by decide) (by decide) (.inl (by decide)))).trans frame.outputPtr }
  have read := stack_readable pre.call.stack running.allocated (offset := 273) (len := 1) (by decide) (by decide)
  change MemReadable t (stackPtr initial - 273) 1 at read
  rw [← dest, ← address] at read
  have mem := Bytes.of_memLoad (n := 8) read.mem
  have write : memLoad t.external (rspOf s + 183) 8 = (s.regValue .r14).setWidth 8 := effect.writes
  rw [write, countR] at mem
  have val : storedByte ((BitVec.ofNat 64 count).setWidth 8) 0 = UInt8.ofNat count := by
    simp only [storedByte,BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mul_zero,Nat.shiftRight_zero]
    congr 1
    omega
  have byte := mem 0 (by decide)
  simp only [BitVec.add_zero, address, val] at byte
  exact ⟨t, frameT, effect.rip, byte, agrees⟩

end Hkdf.Proofs.NewExpand.Extract.Update
