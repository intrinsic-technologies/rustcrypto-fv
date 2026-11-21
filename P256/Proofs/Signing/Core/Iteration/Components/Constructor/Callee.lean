import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Call
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}

theorem call_memory {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    (effect : (callEffect target ret t).Holds t u) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 72, workRegion s] := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a ha
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · rw [constructor_call_address state] at ha
    exact ⟨workRegion s, by simp, Program.ScalarFrame.Work.contains pre (offset := 224) (by decide) (by decide) ha⟩
  · exact ha.elim

theorem local_pre {entry ret : BitVec 64} {input output inputBytes outputBytes reserve : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    (ready : ReadyToStep u)
    (effect : (callEffect (fun _ => entry) ret t).Holds t u)
    (source : t.regValue .rsi = stackPtr t + BitVec.ofNat 64 input)
    (destination : t.regValue .rdi = stackPtr t + BitVec.ofNat 64 output)
    (retInProgram : InProgram ret)
    (inputBound : input + inputBytes ≤ 192) (outputBound : output + outputBytes ≤ 192)
    (apart : input + inputBytes ≤ output ∨ output + outputBytes ≤ input)
    (reserveBound : reserve ≤ 288) : CalleePre u boundary entry inputBytes outputBytes reserve := by
  let layout : StackCallLayout 512 inputBytes outputBytes reserve :=
    ⟨224, 216 - input, 216 - output, by decide, by omega, by omega, by omega,
      by omega, by omega, by omega⟩
  apply pre.of_stack layout (bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees)
    (supportedMachine_of_ready_agrees state.machine ready effect.agrees)
    (effect.agrees.directionFlagClear (by simp) state.directionFlag)
    (constructor_call_loaded pre state effect)
    (fun a ha => effect.agrees.grow a (state.allocated a ha)) effect.rip
  · exact effect.writes.1.trans (constructor_call_address state)
  · exact (effect.agrees.read (n := 64) (r := 6) (by simp)).trans
      (source.trans (Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)))
  · exact (effect.agrees.read (n := 64) (r := 7) (by simp)).trans
      (destination.trans (Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)))
  · change InProgram (stackTop u)
    rw [(callEffect_stack effect).1]
    exact retInProgram

theorem call_result_memory {entry ret : BitVec 64} {output outputBytes reserve : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    (effect : (callEffect (fun _ => entry) ret t).Holds t u)
    (destination : t.regValue .rdi = stackPtr t + BitVec.ofNat 64 output)
    (outputBound : output + outputBytes ≤ 192) (reserveBound : reserve ≤ 288)
    (result : CalleeResult u v boundary outputBytes reserve) :
    MemoryWriteFrame t v #v[registerRegion s .rdi 72, workRegion s] := by
  have bounds := Program.stack_bounds pre.stack
  have sp : (stackPtr u).toNat = (stackPtr s).toNat - 224 := by
    have hsp : stackPtr u = stackPtr s - 224 :=
      effect.writes.1.trans (constructor_call_address state)
    rw [hsp]
    exact Program.stack_sub_toNat pre.stack (by decide)
  have dst : u.regValue .rdi = stackPtr s - BitVec.ofNat 64 (216 - output) :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans
      (destination.trans (Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)))
  have dn : (u.regValue .rdi).toNat = (stackPtr s).toNat - (216 - output) := by
    rw [dst]
    exact Program.stack_sub_toNat pre.stack (by omega)
  apply memoryWriteFrame_trans (call_memory pre state effect)
  intro a ha
  apply result.frame a
  intro region hr hin
  apply ha (workRegion s) (by simp)
  have cases : region = registerRegion u .rdi outputBytes ∨ region = Stack.region u reserve := by
    simpa using hr
  change (stackPtr s).toNat - 512 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 512 + 488
  rcases cases with rfl | rfl
  · change (u.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (u.regValue .rdi).toNat + outputBytes at hin
    rw [dn] at hin
    constructor <;> omega
  · change (stackPtr u).toNat - reserve ≤ a.toNat ∧ a.toNat <
      (Stack.region u reserve).start + (Stack.region u reserve).size at hin
    rw [stack_region_end, sp] at hin
    constructor <;> omega

theorem Frame.after_call {entry ret : BitVec 64} {output outputBytes reserve : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    (effect : (callEffect (fun _ => entry) ret t).Holds t u)
    (destination : t.regValue .rdi = stackPtr t + BitVec.ofNat 64 output)
    (outputBound : output + outputBytes ≤ 192) (reserveBound : reserve ≤ 288)
    (result : CalleeResult u v boundary outputBytes reserve) : Frame s v := by
  have memory := call_result_memory pre state effect destination outputBound reserveBound result
  refine {
    bindingsSupported := result.bindingsSupported
    machine := result.machine
    loaded := result.loaded
    directionFlag := result.directionFlag
    allocated := fun a ha => result.allocated a (effect.agrees.grow a (state.allocated a ha))
    frame := memoryWriteFrame_trans state.frame (Program.ScalarFrame.Work.frame pre memory)
    rsp := result.rsp.trans ((callEffect_stack effect).2.trans state.rsp)
    savedRbx := (Program.ScalarFrame.Work.read pre (by decide) memory (offset := 24) (by decide) (by decide)).trans state.savedRbx
    savedR14 := (Program.ScalarFrame.Work.read pre (by decide) memory (offset := 16) (by decide) (by decide)).trans state.savedR14
    savedR15 := (Program.ScalarFrame.Work.read pre (by decide) memory (offset := 8) (by decide) (by decide)).trans state.savedR15
    rbp := (result.calleeSaved .rbp (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 5) (by simp)).trans state.rbp)
    r12 := (result.calleeSaved .r12 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 12) (by simp)).trans state.r12)
    r13 := (result.calleeSaved .r13 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 13) (by simp)).trans state.r13)
    returnAddress := ?_
    mxcsr := result.mxcsr.trans ((effect.agrees.mxcsr (by simp)).trans state.mxcsr)
    fp87 := result.fp87.trans ((effect.agrees.fcw (by simp)).trans state.fp87)
  }
  have h := Program.ScalarFrame.Work.read pre (by decide) memory (offset := 0) (n := 64) (by decide) (by decide)
  simp only [BitVec.sub_zero] at h
  exact h.trans state.returnAddress

theorem Stage.after_call {entry ret : BitVec 64} {output outputBytes reserve fuel : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (run : Advances boundary fuel t u)
    (effect : (callEffect (fun _ => entry) ret t).Holds t u)
    (destination : t.regValue .rdi = stackPtr t + BitVec.ofNat 64 output)
    (outputBound : output + outputBytes ≤ 192) (reserveBound : reserve ≤ 288)
    (result : CalleeResult u v boundary outputBytes reserve) : Stage s v boundary := by
  obtain ⟨n, hn⟩ := state.execution
  obtain ⟨m, hm⟩ := result.execution
  exact ⟨state.toFrame.after_call pre effect destination outputBound reserveBound result,
    ⟨n + fuel + m, (hn.trans run).trans hm⟩,
    (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp)).trans state.output)⟩

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
