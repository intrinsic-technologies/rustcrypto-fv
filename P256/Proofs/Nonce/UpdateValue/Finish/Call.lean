import P256.Proofs.Nonce.UpdateValue.Finish.State
import P256.Proofs.Nonce.UpdateValue.Prepare.Key.Call
import P256.Proofs.HMAC.State
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {state : State}

omit [Bindings] in
theorem hash_address : scratch initial + 272 = stackPtr initial - 216 := by
  change stackPtr initial - 488 + 272 = stackPtr initial - 216
  rw [show (488 : BitVec 64) = 216 + 272 by decide, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem called (pre : UpdateValuePre initial boundary state)
    (input : CallReady initial s state) (ready : ReadyToStep t)
    (effect : (callEffect (fun _ => 0x100f10) 0x10abe2 s).Holds s t) :
    Called initial t boundary state := by
  have frame := input.toFrameState.after_call pre.callee (by decide) (by decide) ready effect
  have hash : t.regValue .rdi = scratch initial + 272 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans input.hashPointer
  have output : t.regValue .rsi = scratch initial + 8 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input.outputPointer
  have ret : (returnBoundary t).rip = 0x10abe2 := (callEffect_stack effect).1
  let layout : StackCallLayout 1168 32 168 672 :=
    ⟨496, 480, 216, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have base : CalleePre t boundary 0x100f10 32 168 672 :=
    CalleePre.of_stack pre.callee layout frame.bindingsSupported frame.machine frame.directionFlag
      frame.loaded frame.allocated effect.rip frame.rsp
      (output.trans Prepare.Key.output_address) (hash.trans hash_address)
      (ret ▸ inProgram_of_textOffset 0xabe2 (by decide))
  have hmac : HMAC.HmacStateAt t (scratch initial + 272) state.key state.value := by
    apply input.hmac.copy
    intro i hi
    rw [hash_address]
    exact ScalarFrame.scalar_call_byte (by decide) input.toFrameState effect
      (by decide) (by decide) hi
  have memory := effect.agrees.memoryWriteFrame
    (ScalarFrame.scalar_call_writes pre.callee (by decide) input.toFrameState)
  have digestAvoids : (registerRegion t .rsi 32).Avoids
      (fun a => InProgram a ∨ InPageTables a) := by
    intro a ha hp
    apply pre.avoids (Stack.region initial 1168) (by simp) a ?_ hp
    change (t.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (t.regValue .rsi).toNat + 32 at ha
    rw [output, Prepare.Key.output_address] at ha
    change (stackPtr initial - BitVec.ofNat 64 480).toNat ≤ a.toNat ∧
      a.toNat < (stackPtr initial - BitVec.ofNat 64 480).toNat + 32 at ha
    rw [stack_sub_toNat pre.stack (offset := 480) (by decide)] at ha
    change (stackPtr initial).toNat - 1168 ≤ a.toNat ∧
      a.toNat < (Stack.region initial 1168).start + (Stack.region initial 1168).size
    rw [stack_region_end]
    have bounds := stack_bounds pre.stack
    constructor <;> omega
  refine ⟨frame, ⟨⟨base, digestAvoids⟩, input.drbg.key_size, Or.inl input.drbg.value_size,
    by simpa only [hash] using hmac⟩,
    (effect.agrees.read (n := 64) (r := 3) (by simp)).trans input.valuePointer,
    hash.trans hash_address, output.trans Prepare.Key.output_address, ?_, ret⟩
  apply input.drbg.of_frame pre.stateBounded memory
  intro r hr
  have eq : r = Stack.region initial 1168 := by simpa using hr
  subst r
  exact pre.separation

theorem call (pre : UpdateValuePre initial boundary state) (input : CallReady initial s state) :
    ∃ t, Advances boundary 1 s t ∧ Called initial t boundary state := by
  obtain ⟨t, run, ready, effect⟩ := ScalarFrame.scalar_call pre.callee
    (by decide) (by decide) input.toFrameState 0xabdd 0xffff632e
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0xf10 (by decide)) input.rip
  exact ⟨t, run, called pre input ready effect⟩

end P256.Proofs.Nonce.UpdateValue.Finish
