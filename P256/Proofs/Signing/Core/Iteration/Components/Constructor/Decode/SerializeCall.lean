import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Prologue
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.InputCall
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.CallResult
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Serialize
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode.Arguments

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem serialize_left [Bindings] {s : RamState} {boundary : ReturnBoundary} {a : Nat}
    (pre : ConstructorPre s boundary) (scalar : Nat256At s (s.regValue .rsi) a) :
    ∃ t, Stage s t boundary ∧ t.RIP = 0x1098b2 ∧
      t.regValue .r14 = s.regValue .rdx ∧ t.regValue .r15 = stackPtr t + 128#64 ∧
      (MemoryRegion.mk (stackPtr t + 128#64).toNat 32).HasBytes t.external
        (Standards.SECG.ECC.Encoding.natToOctets 32 a) := by
  obtain ⟨v, state, rip, r14, r15, rsi, rdi⟩ := prologue pre.toCalleePre
  obtain ⟨u, run, ready, effect⟩ := Program.ScalarFrame.call_step pre.toCalleePre (frameOffset := 216) (by decide) (by decide)
    (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated state.rsp 0x98ad 0xc0ae
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x15960 (by decide)) rip
  change (callEffect (fun _ => 0x115960) 0x1098b2 v).Holds v u at effect
  have cp : CalleePre u boundary 0x115960 32 32 64 :=
    input_pre pre.toCalleePre state.toFrame ready effect rsi rdi
      (inProgram_of_textOffset 0x98b2 (by decide)) (by decide) (by decide)
  have usrc : u.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans rsi
  have value : Nat256At u (u.regValue .rsi) a := by
    rw [usrc]
    exact input_scalar_call pre.toCalleePre state.toFrame pre.inputBounded
      (pre.separation 0 2 (by decide)) effect (state.toFrame.left_scalar pre scalar)
  obtain ⟨t, result, bytes⟩ := Serialize.serialize_correct cp value
  have st := state.after_call pre.toCalleePre run effect rdi (by decide) (by decide) result
  have sp : stackPtr t = stackPtr v := result.rsp.trans (callEffect_stack effect).2
  have dst : u.regValue .rdi = stackPtr v + 128#64 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans rdi
  refine ⟨t, st, result.rip.trans (callEffect_stack effect).1, ?_, ?_, ?_⟩
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 14) (by simp)).trans r14)
  · rw [sp]
    exact (result.calleeSaved .r15 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 15) (by simp)).trans r15)
  · simpa only [registerRegion, dst, sp] using bytes

theorem serialize_right [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a b : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (rip : t.RIP = 0x109923)
    (first : Nat256At t (stackPtr t + 64#64) a)
    (second : Nat256At t (stackPtr t + 128#64) b) :
    ∃ w, Stage s w boundary ∧ w.RIP = 0x10993b ∧
      w.regValue .r14 = stackPtr w + 160#64 ∧
      (MemoryRegion.mk (stackPtr w + 160#64).toNat 32).HasBytes w.external
        (Standards.SECG.ECC.Encoding.natToOctets 32 b) ∧
      Nat256At w (stackPtr w + 64#64) a := by
  obtain ⟨n, v, run, ready, _, effect⟩ := serialize_arguments_run boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x9923 serializeArgumentBytes
      (by decide) (by decide +kernel)) rip
  have f : AgreesExcept [.reg 14, .reg 6, .reg 7, .rip] t v := effect.agrees
  have stateV := state.after_registers run ready f (by simp [Component.Covers]) (by simp)
  have spV : stackPtr v = stackPtr t := f.read (n := 64) (r := 4) (by simp)
  have memory := f.external (by simp [Component.Covers])
  have args : v.regValue .r14 = stackPtr t + 160#64 ∧
      v.regValue .rsi = stackPtr t + 128#64 ∧ v.regValue .rdi = stackPtr t + 160#64 := effect.writes
  have src : v.regValue .rsi = stackPtr v + 128#64 := by rw [spV]; exact args.2.1
  have dst : v.regValue .rdi = stackPtr v + 160#64 := by rw [spV]; exact args.2.2
  have firstV : Nat256At v (stackPtr v + 64#64) a := by simpa only [Nat256At, spV, memory] using first
  have secondV : Nat256At v (stackPtr v + 128#64) b := by simpa only [Nat256At, spV, memory] using second
  obtain ⟨u, runU, readyU, call⟩ := Program.ScalarFrame.call_step pre (frameOffset := 216) (by decide) (by decide)
    (readyToStep stateV.machine stateV.bindingsSupported)
    stateV.loaded stateV.allocated stateV.rsp 0x9936 0xc025
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x15960 (by decide)) effect.rip
  change (callEffect (fun _ => 0x115960) 0x10993b v).Holds v u at call
  have cp : CalleePre u boundary 0x115960 32 32 64 :=
    local_pre pre stateV.toFrame readyU call src dst
      (inProgram_of_textOffset 0x993b (by decide)) (by decide) (by decide) (.inl (by decide)) (by decide)
  have usrc : u.regValue .rsi = stackPtr v + 128#64 :=
    (call.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have value : Nat256At u (u.regValue .rsi) b := by
    rw [usrc]
    exact scalar_call stateV.toFrame call (by decide) secondV
  obtain ⟨w, result, bytes⟩ := Serialize.serialize_correct cp value
  have stateW := stateV.after_call pre runU call dst (by decide) (by decide) result
  have sp : stackPtr w = stackPtr v := result.rsp.trans (callEffect_stack call).2
  have udst : u.regValue .rdi = stackPtr v + 160#64 :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  refine ⟨w, stateW, result.rip.trans (callEffect_stack call).1, ?_, ?_, ?_⟩
  · rw [sp, spV]
    exact (result.calleeSaved .r14 (by simp)).trans
      ((call.agrees.read (n := 64) (r := 14) (by simp)).trans args.1)
  · simpa only [registerRegion, udst, sp] using bytes
  · exact call_result_scalar pre stateV.toFrame call dst result (by decide) (by decide)
      (.inl (by decide)) firstV

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode
