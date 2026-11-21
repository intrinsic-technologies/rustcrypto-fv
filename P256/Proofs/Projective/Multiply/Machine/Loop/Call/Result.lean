import P256.Proofs.Projective.Multiply.Machine.Loop.Interface
import P256.Proofs.Projective.Preserve
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall

structure PointCallResult [Bindings] (s t u : RamState) (boundary : ReturnBoundary)
    (ret : BitVec 64) (outputOffset : Nat) (point : Projective) : Prop extends FrameState s u 96 1400 376 where
  execution : ∃ fuel, Advances boundary fuel t u
  rip : u.RIP = ret
  value : ProjectiveAt u (stackPtr s - BitVec.ofNat 64 outputOffset) point
  registers : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r
  bytes : ∀ offset len : Nat, offset ≤ 376 → len ≤ offset + 8 →
    (offset + 96 ≤ outputOffset ∨ outputOffset + len ≤ offset) →
    ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?

theorem PointCallResult.read [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {ret : BitVec 64} {outputOffset offset n : Nat} {point : Projective}
    (result : PointCallResult s t u boundary ret outputOffset point)
    (ho : offset ≤ 376) (hl : n/8 ≤ offset+8)
    (apart : offset + 96 ≤ outputOffset ∨ outputOffset+n/8 ≤ offset) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [result.bytes offset (n/8) ho hl apart i hi]

theorem finish_call [Bindings] {s t v u : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64} {outputOffset reserve : Nat} {point : Projective}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (run : Advances boundary 1 t v) (ready : ReadyToStep v)
    (effect : (callEffect target ret t).Holds t v)
    (output : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (ho : outputOffset ≤ 376) (hsaved : 144 ≤ outputOffset)
    (capacity : reserve + 384 ≤ 1400)
    (result : CalleeResult v u boundary 96 reserve)
    (value : ProjectiveAt u (v.regValue .rdi) point) :
    PointCallResult s t u boundary ret outputOffset point := by
  have stateV := state.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have memory := stack_result_work_frame (frameOffset := 376) pre.toCalleePre stateV result
    output (by omega) hsaved capacity (by decide)
  have retV : (returnBoundary v).rip = ret := (callEffect_stack effect).1
  refine ⟨after_result (frameOffset := 376) pre.toCalleePre stateV result (by decide) memory,
    ?_, result.rip.trans retV, output ▸ value, ?_, ?_⟩
  · obtain ⟨fuel, run'⟩ := result.execution
    exact ⟨1+fuel, run.trans run'⟩
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  · intro offset len ho' hl apart i hi
    exact (stack_result_byte (frameOffset := 376) pre.toCalleePre stateV result output (by decide) (by omega) ho' hl apart hi).trans
      (scalar_call_byte (by decide) state effect ho' hl hi)

end P256.Proofs.Projective.Multiply.Machine.Loop
