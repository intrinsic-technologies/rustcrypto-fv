import P256.Proofs.Projective.Multiply.Machine.Basepoint.Interface
import P256.Proofs.Projective.Multiply.Machine.Loop.Correct
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.FieldCall.Memory
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.PublicPoint

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall
open Projective.Multiply Projective.Multiply.Machine

structure Multiplied [Bindings] (s t : RamState) (boundary : ReturnBoundary) (d : Nat) : Prop extends
    FrameState s t 65 3352 1944 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10e953
  output : t.regValue .rbx = s.regValue .rdi
  value : ProjectiveAt t (stackPtr s - 1880) (model Basepoint.basePoint d)

def loopLayout : StackCallLayout 3352 768 96 1400 :=
  ⟨1952, 912, 1880, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

def digitsLayout : StackCallLayout 3352 65 96 1400 :=
  ⟨1952, 1784, 1880, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem multiply_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Basepoint.Ready s t boundary d) :
    ∃ u, Multiplied s u boundary d := by
  obtain ⟨v, run, ready, effect⟩ := scalar_call pre (by decide) (by decide) state.toFrameState
    0xe94e 0xffff48fd (by decide) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x3250 (by decide)) state.rip
  change (callEffect (fun _ => 0x103250) 0x10e953 t).Holds t v at effect
  have frame := state.toFrameState.after_call pre (by decide) (by decide) ready effect
  have src : v.regValue .rsi = stackPtr s - 912 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.source
  have dst : v.regValue .rdi = stackPtr s - 1880 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.destination
  have dig : v.regValue .rcx = stackPtr s - 1784 :=
    (effect.agrees.read (n := 64) (r := 1) (by simp)).trans state.digits
  have ret : (returnBoundary v).rip = 0x10e953 := (callEffect_stack effect).1
  have retProg : InProgram (returnBoundary v).rip := by
    rw [ret]
    exact inProgram_of_textOffset 0xe953 (by decide)
  have cp := CalleePre.of_stack pre loopLayout frame.bindingsSupported frame.machine frame.directionFlag
    frame.loaded frame.allocated effect.rip frame.rsp src dst retProg
  have dp := CalleePre.of_stack pre digitsLayout frame.bindingsSupported frame.machine frame.directionFlag
    frame.loaded frame.allocated effect.rip frame.rsp dig dst retProg
  have loopPre : Loop.Pre v boundary := ⟨cp,
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.tableCount,
    (effect.agrees.read (n := 64) (r := 8) (by simp)).trans state.digitCount,
    dp.inputBounded, dp.inputAllocated, dp.separation 0 1 (by decide),
    dp.separation 0 2 (by decide)⟩
  have table : Lookup.TableAt v (v.regValue .rsi) (Projective.table Basepoint.basePoint) := by
    rw [src]
    intro index
    apply (state.table index).of_bytes_eq
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact scalar_call_byte (by decide) state.toFrameState effect (offset := 912) (len := 768)
      (by decide) (by decide) (by have := index.isLt; omega)
  have bytes : Bytes v.external (v.regValue .rcx) 65
      (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte d i)) := by
    rw [dig]
    intro i hi
    exact (scalar_call_byte (by decide) state.toFrameState effect (offset := 1784) (len := 65)
      (by decide) (by decide) hi).trans (state.digitBytes i hi)
  obtain ⟨u, result, value⟩ := Loop.loop_correct loopPre table
  rw [Loop.linearCombination_eq_model bytes, dst] at value
  have memory := stack_result_work_frame (frameOffset := 1944) pre frame result dst
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨u, after_result (frameOffset := 1944) pre frame result (by decide) memory,
    ?_, result.rip.trans ret, ?_, value⟩
  · obtain ⟨a, initialRun⟩ := state.execution
    obtain ⟨b, child⟩ := result.execution
    exact ⟨a+1+b, (initialRun.trans run).trans child⟩
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp)).trans state.output)

end P256.Proofs.PublicPoint
