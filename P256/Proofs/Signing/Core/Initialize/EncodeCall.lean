import P256.Proofs.Signing.Core.Initialize.Memory
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add base_nat)

variable [Bindings] {s t entry u : RamState} {boundary : ReturnBoundary}

def encodeLayout : StackBufferLayout 4584 32 0 :=
  ⟨2288, 1752, by decide, by decide, by decide, by decide⟩

theorem encode_pre (pre : SignPre s boundary) (frame : Frame s t)
    (ready : ReadyToStep entry)
    (effect : (callEffect (fun _ => 0x112ea0) 0x10ca39 t).Holds t entry)
    (source : t.regValue .rsi = s.regValue .rsi)
    (destination : t.regValue .rdi = frameBase s + 528) :
    CalleePre entry boundary 0x112ea0 32 32 0 := by
  have state := (scalarFrame frame).after_call pre.toCalleePre (by decide) (by decide) ready effect
  refine CalleePre.of_input_and_stack pre.toCalleePre encodeLayout state.bindingsSupported
    state.machine state.directionFlag state.loaded state.allocated effect.rip state.rsp ?_ ?_ ?_
  · exact (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  · exact ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination).trans
      (base_add s (by decide))
  · have ret : (returnBoundary entry).rip = 0x10ca39 := (callEffect_stack effect).1
    rw [ret]
    exact inProgram_of_textOffset 0xca39 (by decide)

theorem encode_frame (pre : SignPre s boundary) (frame : Frame s t)
    (ready : ReadyToStep entry)
    (effect : (callEffect (fun _ => 0x112ea0) 0x10ca39 t).Holds t entry)
    (result : CalleeResult entry u boundary 32 0)
    (destination : t.regValue .rdi = frameBase s + 528) : Frame s u := by
  have state := (scalarFrame frame).after_call pre.toCalleePre (by decide) (by decide) ready effect
  have dest : entry.regValue .rdi = stackPtr s - 1752 :=
    ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination).trans (base_add s (by decide))
  exact coreFrame (FieldCall.after_result pre.toCalleePre state result (by decide)
    (FieldCall.stack_result_work_frame pre.toCalleePre state result dest
      (by decide) (by decide) (by decide) (by decide)))

theorem encode_byte (pre : SignPre s boundary) (frame : Frame s t)
    (ready : ReadyToStep entry)
    (effect : (callEffect (fun _ => 0x112ea0) 0x10ca39 t).Holds t entry)
    (result : CalleeResult entry u boundary 32 0)
    (destination : t.regValue .rdi = frameBase s + 528)
    {offset len i : Nat} (bound : offset+len ≤ 2280)
    (apart : offset+len ≤ 528 ∨ 560 ≤ offset) (hi : i < len) :
    u.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have state := (scalarFrame frame).after_call pre.toCalleePre (by decide) (by decide) ready effect
  have dest : entry.regValue .rdi = stackPtr s - 1752 :=
    ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination).trans (base_add s (by decide))
  rw [base_add s (by omega)]
  exact (FieldCall.stack_result_byte (frameOffset := 2280) (outputOffset := 1752)
    (offset := 2280-offset) (len := len) pre.toCalleePre state result dest
    (by decide) (by decide) (by omega) (by omega) (by omega) hi).trans
    (ScalarFrame.scalar_call_byte (frameOffset := 2280) (offset := 2280-offset) (len := len) (by decide) (scalarFrame frame) effect (by omega) (by omega) hi)

theorem encode_word (pre : SignPre s boundary) (frame : Frame s t)
    (ready : ReadyToStep entry)
    (effect : (callEffect (fun _ => 0x112ea0) 0x10ca39 t).Holds t entry)
    (result : CalleeResult entry u boundary 32 0)
    (destination : t.regValue .rdi = frameBase s + 528)
    {offset : Nat} (bound : offset+8 ≤ 2280)
    (apart : offset+8 ≤ 528 ∨ 560 ≤ offset) :
    (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read u =
      (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read t := by
  apply memLoad_congr
  intro i hi
  change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
  rw [encode_byte pre frame ready effect result destination bound apart hi]

theorem encode_preserved
    (effect : (callEffect (fun _ => 0x112ea0) 0x10ca39 t).Holds t entry)
    (result : CalleeResult entry u boundary 32 0)
    (r : Syntax.Reg) (hr : r ∈ [.rbx,.rbp,.r12,.r13,.r14,.r15]) :
    u.regValue r = t.regValue r := by
  apply (result.calleeSaved r hr).trans
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact effect.agrees.read (n := 64) (r := 3) (by simp)
  · exact effect.agrees.read (n := 64) (r := 5) (by simp)
  · exact effect.agrees.read (n := 64) (r := 12) (by simp)
  · exact effect.agrees.read (n := 64) (r := 13) (by simp)
  · exact effect.agrees.read (n := 64) (r := 14) (by simp)
  · exact effect.agrees.read (n := 64) (r := 15) (by simp)

end P256.Proofs.Signing.Core.Initialize
