import P256.Proofs.Nonce.UpdateValue.Prepare.State
import P256.Proofs.Nonce.UpdateValue.Result
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.CalleeStack
import P256.Proofs.SHA256

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare.Compression

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {state : State}

def layout : StackCallLayout 1168 64 32 336 :=
  ⟨496, 480, 320, by decide, by decide, by decide, by decide, by decide, by decide,
    .inl (by decide)⟩

theorem call (pre : UpdateValuePre initial boundary state) (input : CompressionInput initial s state) :
    ∃ t, Advances boundary 1 s t ∧
      ScalarFrame.FrameState initial t 64 1168 496 ∧
      (callEffect (fun _ => 0x115990) 0x10aa24 s).Holds s t ∧
      SHA256.CompressionPre t boundary SHA256.initialHash (HMAC.keyPad state.key 0x36) 1 := by
  obtain ⟨t, run, ready, effect⟩ := ScalarFrame.scalar_call pre.callee
    (by decide) (by decide) input.toFrameState 0xaa1f 0xaf6c
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x15990 (by decide)) input.rip
  have frame := input.toFrameState.after_call pre.callee (by decide) (by decide) ready effect
  have address (offset : Nat) (bound : offset ≤ 488) :
      scratch initial + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (488-offset) := by
    rw [← show stackPtr s = scratch initial from input.rsp]
    exact ScalarFrame.scalar_stack_address input.rsp (by decide) bound
  have addr168 : scratch initial + 168 = stackPtr initial - 320 := address 168 (by decide)
  have addr8 : scratch initial + 8 = stackPtr initial - 480 := address 8 (by decide)
  have source : t.regValue .rsi = stackPtr initial - 480 := by
    exact ((effect.agrees.read (n := 64) (r := 6) (by simp)).trans input.source).trans
      (address 8 (by decide))
  have output : t.regValue .rdi = stackPtr initial - 320 := by
    exact ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans input.destination).trans
      (address 168 (by decide))
  have ret : InProgram (returnBoundary t).rip := by
    change InProgram (stackTop t)
    rw [(callEffect_stack effect).1]
    exact inProgram_of_textOffset 0xaa24 (by decide)
  have callee := pre.callee.of_stack layout frame.bindingsSupported frame.machine
    frame.directionFlag frame.loaded frame.allocated effect.rip frame.rsp source output ret
  have copied {offset len : Nat} (bound : offset ≤ 488) (span : len ≤ offset + 8) :
      ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? :=
    fun _ hi => ScalarFrame.scalar_call_byte (by decide) input.toFrameState effect bound span hi
  refine ⟨t, run, frame, effect, callee, ?_, ?_, ?_⟩
  · exact (effect.agrees.read (n := 64) (r := 2) (by simp)).trans input.count
  · change (MemoryRegion.mk (t.regValue .rsi).toNat 64).HasBytes t.external _
    rw [source]
    apply hasBytes_copy (by simpa only [addr8] using input.key)
    exact copied (offset := 480) (len := 64) (by decide) (by decide)
  · rw [output]
    refine ⟨input.hash.1, ?_⟩
    intro j hj
    apply loadBytes_ok_copy
      (copied_sub (offset := 4*j) (len := 4)
        (copied (offset := 320) (len := 32) (by decide) (by decide)) (by omega))
    have h := input.hash.2 j hj
    rw [addr168] at h
    exact h

end P256.Proofs.Nonce.UpdateValue.Prepare.Compression
