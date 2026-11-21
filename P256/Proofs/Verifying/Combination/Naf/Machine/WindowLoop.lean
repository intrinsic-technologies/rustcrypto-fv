import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.AdvanceLoop
import P256.Proofs.Verifying.Combination.Naf.Machine.Transport
import P256.Proofs.Verifying.Combination.Naf.Machine.WindowMachine

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem window_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n i c : Nat} {ds : List Int} (pre : Pre s boundary)
    (state : LoopState s t n i (i/64) c ds 0x10f3fe)
    (first : t.regValue .rax = Iterator.word n (i/64))
    (second : t.regValue .rdx = Iterator.word n (i/64+1))
    (index : t.regValue .rbx = BitVec.ofNat 64 (i%64)) :
    WindowPre t n i c (s.regValue .rdi) := by
  refine ⟨readyToStep state.machine state.bindingsSupported, state.loaded, state.rip,
    first, second, index, state.r12, state.rbp, state.r13,
    stack_readable pre.toCalleePre state.toFrameState (by decide),
    stack_readable pre.toCalleePre state.toFrameState (by decide),
    ?_, ?_, state.source.1, state.indexBound, state.carryBound⟩
  · change memLoad t.external (stackPtr t+40#64) 64 = 31
    rw [stack_address state.rsp (offset := 40) (by decide)]
    exact state.mask
  · change memLoad t.external (stackPtr t+16#64) 64 = s.regValue .rdi
    rw [stack_address state.rsp (offset := 16) (by decide)]
    exact state.outputPointer


theorem window_loop [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n i k c : Nat} {ds : List Int} (pre : Pre s boundary)
    (input : Nat256At s (s.regValue .rdx) n) (state : LoopState s t n i k c ds) :
    ∃ fuel u, Advances boundary fuel t u ∧
      LoopState s u n i (i/64) c ds (if (n/2^i%32+c)%2=0 then 0x10f43f else 0x10f470) ∧
      u.regValue .rdx = BitVec.ofNat 64 (n/2^i%32+c) ∧ u.regValue .rsi = s.regValue .rdi := by
  obtain ⟨fuelA, a, runA, stateA, first, second, index⟩ := advance_loop pre input state
  obtain ⟨fuelW, u, runW, ready, _, rip, value, output, agrees⟩ :=
    window_execute (window_pre pre stateA first second index) pre.outerBoundary
  refine ⟨fuelA+fuelW, u, runA.trans runW, ?_, value, output⟩
  exact stateA.after_registers ready agrees (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) rip

end P256.Proofs.Verifying.Combination.Naf.Machine
