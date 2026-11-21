import P256.Proofs.SignatureFromDer.Fixed.FrameLemmas
import P256.Proofs.Program.ScalarFrame.CallStep
import P256.Proofs.Program.CalleeStack
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult StackCallLayout boundary_ne_program programLoaded_codeIn programText_slice supportedMachine_of_ready_agrees readyToStep stack_region_end)

namespace P256.Proofs.SignatureFromDer.Fixed.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}

theorem call_memory {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Frame s t)
    (effect : (callEffect target ret t).Holds t u) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 72, workRegion s] := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a ha
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · rw [show pushAddr t = stackPtr s - 192 by rw [pushAddr, state.rsp, BitVec.sub_sub]; rfl] at ha
    exact ⟨workRegion s, by simp, Program.ScalarFrame.Work.contains pre (offset := 192) (by decide) (by decide) ha⟩
  · exact ha.elim

theorem scalar_pre {ret : BitVec 64}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Frame s t)
    (ready : ReadyToStep u)
    (effect : (callEffect (fun _ => 0x10fa20) ret t).Holds t u)
    (source : t.regValue .rsi = stackPtr t + 72)
    (destination : t.regValue .rdi = stackPtr t + 8)
    (retInProgram : InProgram ret) : CalleePre u boundary 0x10fa20 32 40 288 := by
  let layout : StackCallLayout 560 32 40 288 :=
    ⟨192, 112, 176, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have memory := Program.ScalarFrame.Work.frame pre (call_memory pre state effect)
  apply pre.of_stack layout (Program.bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees)
    (supportedMachine_of_ready_agrees state.machine ready effect.agrees)
    (effect.agrees.directionFlagClear (by simp) state.directionFlag)
    (fun a b hb => by
      rw [memory a]
      · exact state.loaded a b hb
      · intro region hr hin
        exact pre.avoids region (by simpa using hr) a hin (.inl ⟨b, hb⟩))
    (fun a ha => effect.agrees.grow a (state.allocated a ha)) effect.rip
  · exact effect.writes.1.trans (show pushAddr t = stackPtr s - 192 by rw [pushAddr, state.rsp, BitVec.sub_sub]; rfl)
  · calc
      u.regValue .rsi = t.regValue .rsi := effect.agrees.read (n := 64) (r := 6) (by simp)
      _ = stackPtr t + 72 := source
      _ = stackPtr s - 112 := Program.ScalarFrame.scalar_stack_address (frameOffset := 184) state.rsp (by decide) (offset := 72) (by decide)
  · calc
      u.regValue .rdi = t.regValue .rdi := effect.agrees.read (n := 64) (r := 7) (by simp)
      _ = stackPtr t + 8 := destination
      _ = stackPtr s - 176 := Program.ScalarFrame.scalar_stack_address (frameOffset := 184) state.rsp (by decide) (offset := 8) (by decide)
  · have hret : (returnBoundary u).rip = ret := (callEffect_stack effect).1
    rw [hret]
    exact retInProgram

theorem scalar_result_memory {ret : BitVec 64}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Frame s t)
    (effect : (callEffect (fun _ => 0x10fa20) ret t).Holds t u)
    (destination : t.regValue .rdi = stackPtr t + 8)
    (result : CalleeResult u v boundary 40 288) :
    MemoryWriteFrame t v #v[registerRegion s .rdi 72, workRegion s] := by
  have bounds := Program.stack_bounds pre.stack
  have sp : (stackPtr u).toNat = (stackPtr s).toNat - 192 := by
    have hsp : stackPtr u = stackPtr s - 192 := effect.writes.1.trans (show pushAddr t = stackPtr s - 192 by rw [pushAddr, state.rsp, BitVec.sub_sub]; rfl)
    rw [hsp]
    exact Program.stack_sub_toNat pre.stack (offset := 192) (by decide)
  have dst : u.regValue .rdi = stackPtr s - 176 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans
      (destination.trans (Program.ScalarFrame.scalar_stack_address (frameOffset := 184) state.rsp (by decide) (offset := 8) (by decide)))
  have dn : (u.regValue .rdi).toNat = (stackPtr s).toNat - 176 := by
    rw [dst]
    exact Program.stack_sub_toNat pre.stack (by decide)
  apply memoryWriteFrame_trans (call_memory pre state effect)
  intro a ha
  apply result.frame a
  intro region hr hin
  apply ha (workRegion s) (by simp)
  have cases : region = registerRegion u .rdi 40 ∨ region = Stack.region u 288 := by simpa using hr
  change (stackPtr s).toNat - 560 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 560 + 544
  rcases cases with rfl | rfl
  · change (u.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (u.regValue .rdi).toNat + 40 at hin
    rw [dn] at hin
    constructor <;> omega
  · change (stackPtr u).toNat - 288 ≤ a.toNat ∧ a.toNat <
      (Stack.region u 288).start + (Stack.region u 288).size at hin
    rw [stack_region_end, sp] at hin
    constructor <;> omega

theorem scalar_result_frame {ret : BitVec 64}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Frame s t)
    (effect : (callEffect (fun _ => 0x10fa20) ret t).Holds t u)
    (destination : t.regValue .rdi = stackPtr t + 8)
    (result : CalleeResult u v boundary 40 288) : Frame s v := by
  have memory := scalar_result_memory pre state effect destination result
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (effect.agrees.grow a (state.allocated a ha)),
    memoryWriteFrame_trans state.frame (Program.ScalarFrame.Work.frame pre memory), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    result.mxcsr.trans ((effect.agrees.mxcsr (by simp)).trans state.mxcsr),
    result.fp87.trans ((effect.agrees.fcw (by simp)).trans state.fp87)⟩
  · exact result.rsp.trans ((callEffect_stack effect).2.trans state.rsp)
  · exact (Program.ScalarFrame.Work.read pre (by decide) memory (offset := 16) (by decide) (by decide)).trans state.savedRbx
  · exact (Program.ScalarFrame.Work.read pre (by decide) memory (offset := 8) (by decide) (by decide)).trans state.savedR14
  · exact (result.calleeSaved .rbp (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 5) (by simp)).trans state.rbp)
  · exact (result.calleeSaved .r12 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 12) (by simp)).trans state.r12)
  · exact (result.calleeSaved .r13 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 13) (by simp)).trans state.r13)
  · exact (result.calleeSaved .r15 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 15) (by simp)).trans state.r15)
  · have h := Program.ScalarFrame.Work.read pre (by decide) memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress


theorem scalar_result_byte {ret : BitVec 64}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Frame s t)
    (effect : (callEffect (fun _ => 0x10fa20) ret t).Holds t u)
    (destination : t.regValue .rdi = stackPtr t + 8)
    (result : CalleeResult u v boundary 40 288)
    {offset i len : Nat} (lo : 48 ≤ offset) (hi : offset + len ≤ 184) (index : i < len) :
    v.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := Program.stack_bounds pre.stack
  have tn : (stackPtr t).toNat = (stackPtr s).toNat - 184 := by
    rw [state.rsp]
    exact Program.stack_sub_toNat pre.stack (by decide)
  have un : (stackPtr u).toNat = (stackPtr s).toNat - 192 := by
    have hu : stackPtr u = stackPtr s - 192 := effect.writes.1.trans (show pushAddr t = stackPtr s - 192 by rw [pushAddr, state.rsp, BitVec.sub_sub]; rfl)
    rw [hu]
    exact Program.stack_sub_toNat pre.stack (by decide)
  have dst : u.regValue .rdi = stackPtr t + 8 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have dn : (u.regValue .rdi).toNat = (stackPtr s).toNat - 184 + 8 := by
    rw [dst]
    change ((stackPtr t).toNat + 8) % 2^64 = _
    rw [tn, Nat.mod_eq_of_lt (by omega)]
  rw [result.frame _]
  · rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 184) state.rsp (by decide) (by omega)]
    exact Program.ScalarFrame.call_byte (frameOffset := 184) (by decide) state.rsp effect (offset := 184-offset) (len := len)
      (by omega) (by omega) index
  · intro region hr hin
    have an : (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
        (stackPtr s).toNat - 184 + offset + i := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, toNat_add_ofNat _ _ (by rw [tn]; omega), tn]
      omega
    have cases : region = registerRegion u .rdi 40 ∨ region = Stack.region u 288 := by simpa using hr
    rcases cases with rfl | rfl
    · change (u.regValue .rdi).toNat ≤ _ ∧ _ < (u.regValue .rdi).toNat + 40 at hin
      rw [dn, an] at hin
      omega
    · change (stackPtr u).toNat - 288 ≤ _ ∧ _ <
        (Stack.region u 288).start + (Stack.region u 288).size at hin
      rw [stack_region_end, un, an] at hin
      omega

end P256.Proofs.SignatureFromDer.Fixed.Decode
