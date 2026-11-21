import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Callee
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Correct
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Representation

set_option autoImplicit false

open P256.Proofs.Program (CalleePre inProgram_of_textOffset)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem nat256_call [Bindings] {s t u : RamState} {target : RamState → BitVec 64}
    {ret : BitVec 64} {off d : Nat} (state : Frame s t)
    (effect : (callEffect target ret t).Holds t u) (bound : off + 32 ≤ 216)
    (scalar : Nat256At t (stackPtr t + BitVec.ofNat 64 off) d) :
    Nat256At u (stackPtr t + BitVec.ofNat 64 off) d := by
  rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)] at scalar ⊢
  refine ⟨scalar.1, fun i hi => ?_⟩
  rw [Program.ScalarFrame.call_byte (frameOffset := 216) (by decide) state.rsp effect (offset := 216-off) (len := 32)
    (by omega) (by omega) hi]
  exact scalar.2 i hi

theorem equal_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d off : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (offset : Nat) (disp : BitVec 32) (bound : offset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119270)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (rdi : t.regValue .rdi = stackPtr t + BitVec.ofNat 64 off)
    (rdx : t.regValue .rdx = stackPtr t + 0#64)
    (rsi : t.regValue .rsi = 4) (rcx : t.regValue .rcx = 4)
    (offBound : off + 32 ≤ 216)
    (scalar : Nat256At t (stackPtr t + BitVec.ofNat 64 off) d)
    (zero : Nat256At t (stackPtr t + 0#64) 0) :
    ∃ u, Stage s u boundary ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 offset + 5#64 ∧
      (u.regValue .rax).setWidth 8 = (if d = 0 then 1 else 0) ∧
      (∀ (k value : Nat), k + 32 ≤ 216 → Nat256At t (stackPtr t + BitVec.ofNat 64 k) value →
        Nat256At u (stackPtr u + BitVec.ofNat 64 k) value) := by
  let p := Extracted.textAddress + BitVec.ofNat 64 offset
  obtain ⟨v, hv, rv, ev⟩ := Program.ScalarFrame.call_step pre (frameOffset := 216) (by decide) (by decide)
    (Program.readyToStep state.machine state.bindingsSupported) state.loaded state.allocated state.rsp offset disp
    (by omega) bytes (by rw [target]; decide)
    (by rw [target]; exact inProgram_of_textOffset 0x19270 (by decide)) rip
  have ev' : (callEffect (fun _ => 0x119270) (p + 5#64) t).Holds t v := by
    change (callEffect (fun _ => branchTarget p 5 (disp.signExtend 64)) (p + 5#64) t).Holds t v at ev
    rw [target] at ev
    exact ev
  have push : pushAddr t = stackPtr s - 224#64 := by rw [pushAddr, state.rsp, BitVec.sub_sub]; rfl
  have fv : AgreesExcept [.reg 4, .mem (stackPtr s - 224#64) 8, .rip] t v := by
    simpa only [pushEffect_components, push] using ev'.agrees
  have di : v.regValue .rdi = stackPtr t + BitVec.ofNat 64 off :=
    (fv.read (n := 64) (r := 7) (by simp)).trans rdi
  have dx : v.regValue .rdx = stackPtr t + 0#64 :=
    (fv.read (n := 64) (r := 2) (by simp)).trans rdx
  have spv : stackPtr v = stackPtr s - 224#64 := ev'.writes.1.trans push
  have allocatedv := fun a ha => ev'.agrees.grow a (state.allocated a ha)
  have cp : P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Pre v boundary := by
    refine ⟨rv, Program.ScalarFrame.loaded_of_frame pre (memoryWriteFrame_trans state.frame
      (Program.ScalarFrame.Work.frame pre (call_memory pre state.toFrame ev'))), ev'.rip,
      (fv.read (n := 64) (r := 6) (by simp)).trans rsi,
      (fv.read (n := 64) (r := 1) (by simp)).trans rcx, ?_, ?_, ?_,
      pre.outerBoundary, ?_⟩
    · rw [di, Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (by omega)]
      exact Program.readable_of_grow
        (Program.stack_sub_readable pre.stack (by omega) (by omega)) allocatedv
    · rw [dx, Program.ScalarFrame.scalar_stack_address (frameOffset := 216) state.rsp (by decide) (offset := 0) (by decide)]
      exact Program.readable_of_grow
        (Program.stack_sub_readable pre.stack (by decide) (by decide)) allocatedv
    · rw [spv]
      exact Program.readable_of_grow
        (Program.stack_sub_readable pre.stack (by decide) (by decide)) allocatedv
    · change InProgram (stackTop v)
      rw [(callEffect_stack ev').1]
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, p] using
        inProgram_of_textOffset (offset + 5) bound
  have left : Nat256At v (v.regValue .rdi) d := by
    rw [di]
    exact nat256_call state.toFrame ev' offBound scalar
  have right : Nat256At v (v.regValue .rdx) 0 := by
    rw [dx]
    exact nat256_call state.toFrame ev' (off := 0) (by decide) zero
  obtain ⟨u, result, value⟩ := P256.Proofs.SecretKeyFromBytes.Scalar.Equal.equal_correct cp
  simp only [P256.Proofs.SecretKeyFromBytes.Scalar.Equal.prefixEqual_nat256 left right, decide_eq_true_eq] at value
  have f : AgreesExcept ([.mem (stackPtr s - 224#64) 8, .reg 4] ++ P256.Proofs.SecretKeyFromBytes.Scalar.Equal.clobbers) t u :=
    (fv.trans result.agrees).mono (by simp [P256.Proofs.SecretKeyFromBytes.Scalar.Equal.clobbers])
  have writes : WritesWithin ([.mem (stackPtr s - 224#64) 8, .reg 4] ++ P256.Proofs.SecretKeyFromBytes.Scalar.Equal.clobbers)
      #v[registerRegion s .rdi 72, workRegion s] := by
    intro c hc a ha
    simp only [P256.Proofs.SecretKeyFromBytes.Scalar.Equal.clobbers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals try exact ha.elim
    exact ⟨workRegion s, by simp, Program.ScalarFrame.Work.contains pre (offset := 224) (by decide) (by decide) ha⟩
  have sp : stackPtr u = stackPtr t := result.rsp.trans (callEffect_stack ev').2
  obtain ⟨n, hn⟩ := result.execution
  refine ⟨u, state.after pre (hv.trans hn) result.ready f writes (sp.trans state.rsp)
    (by simp [P256.Proofs.SecretKeyFromBytes.Scalar.Equal.clobbers]), result.rip.trans (callEffect_stack ev').1, value, ?_⟩
  intro k value hk scalar
  rw [sp]
  have preserved := nat256_call state.toFrame ev' hk scalar
  simpa only [Nat256At, result.memory] using preserved

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks
