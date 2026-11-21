import P256.Proofs.Program.CalleeStack
import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.Padding.Memory
import P256.Proofs.SHA256
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Program (stack_bounds stack_sub_toNat)

theorem compression_pre [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {ret : BitVec 64}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : BlockReady initial s message)
    (frame : ScalarFrame.FrameState initial t 0 672 336)
    (effect : (callEffect (fun _ => 0x115990) ret s).Holds s t)
    (returnInProgram : InProgram ret) :
    SHA256.CompressionPre t boundary
      (SHA256.compressBlocks P256.Proofs.SHA256.initialHash message) (SHA256.tailFirst message) 1 := by
  have src : t.regValue .rsi = stackPtr initial - 320 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.inputPointer
  have dst : t.regValue .rdi = stackPtr initial - 192 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.hashPointer
  let layout : StackCallLayout 672 64 32 336 :=
    ⟨336, 320, 192, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have base : CalleePre t boundary 0x115990 64 32 336 :=
    CalleePre.of_stack (pre.toCalleePre) layout frame.bindingsSupported frame.machine frame.directionFlag
      frame.loaded frame.allocated effect.rip frame.rsp src dst
      (by change InProgram (stackTop t); rw [(callEffect_stack effect).1]; exact returnInProgram)
  have sp : (stackPtr t).toNat = (stackPtr initial).toNat - 336 := by
    rw [frame.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hp : (t.regValue .rdi).toNat = (stackPtr initial).toNat - 192 := by
    rw [dst]
    exact stack_sub_toNat pre.stack (by decide)
  refine { base with
    countRegister := (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.count
    inputBytes := ?_
    hashWords := ?_ }
  · change (MemoryRegion.mk (t.regValue .rsi).toNat 64).HasBytes _ _
    rw [src]
    exact hasBytes_copy state.buffer
      (fun i hi => call_byte state.toFrameState effect (by decide) (by decide) hi)
  · rw [dst]
    exact state.hash.copy
      (fun i hi => call_byte state.toFrameState effect (by decide) (by decide) hi)

theorem compression_frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {block : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (rsp : stackPtr s = stackPtr initial - 336#64)
    (hashPointer : s.regValue .rdi = stackPtr initial - 192#64)
    (result : SHA256.CompressionResult s t boundary hash block) :
    MemoryWriteFrame s t #v[scratchRegion initial] := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 336 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hp : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 192 := by
    rw [hashPointer]
    exact stack_sub_toNat pre.stack (by decide)
  intro a ha
  apply result.frame a
  intro region member hin
  have cases : region = registerRegion s .rdi 32 ∨ region = Stack.region s 336 := by
    simpa using member
  apply ha (scratchRegion initial) (by simp)
  change (stackPtr initial).toNat - 672 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 672 + 520
  rcases cases with rfl | rfl
  · change (s.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rdi).toNat + 32 at hin
    rw [hp] at hin
    constructor <;> omega
  · change (stackPtr s).toNat - 336 ≤ a.toNat ∧
      a.toNat < (Stack.region s 336).start + (Stack.region s 336).size at hin
    rw [stack_region_end, sp] at hin
    constructor <;> omega

theorem compress [Bindings] (outer : Bool)
    {initial s : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : BlockReady initial s message) (rip : s.RIP = compressionStart outer) :
    ∃ fuel t, Advances boundary fuel s t ∧ Compressed initial t message ∧
      t.RIP = paddingEnd outer ∧ MemoryWriteFrame s t #v[scratchRegion initial] := by
  let site := if outer then outerTailSite else innerTailSite
  have siteRip : Extracted.textAddress + BitVec.ofNat 64 site.offset = compressionStart outer := by
    cases outer <;> rfl
  have ret : Extracted.textAddress + BitVec.ofNat 64 site.offset + 5#64 = paddingEnd outer := by
    cases outer <;> rfl
  obtain ⟨u, callRun, _, effect, frame⟩ :=
    compression_call pre state.toFrameState site (rip.trans siteRip.symm)
  have callPre := compression_pre pre state frame effect (by
    rw [ret]
    cases outer
    · exact inProgram_of_textOffset 0x1111 (by decide)
    · exact inProgram_of_textOffset 0x13af (by decide))
  obtain ⟨t, result⟩ := SHA256.compression_correct callPre
  obtain ⟨fuel, run⟩ := result.execution
  have dst : u.regValue .rdi = stackPtr initial - 192 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.hashPointer
  have memory := compression_frame pre frame.rsp dst result
  have outputPointer : t.regValue .rbx = initial.regValue .rsi :=
    (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp)).trans state.outputPointer)
  have finalFrame : ScalarFrame.FrameState initial t 0 672 328 :=
    after_result pre (by decide) frame result.toCalleeResult (scratch_frame memory)
      (result.rsp.trans ((callEffect_stack effect).2.trans state.rsp))
  refine ⟨1 + fuel, t, callRun.trans run, ⟨finalFrame, outputPointer, ?_⟩,
    result.rip.trans ((callEffect_stack effect).1.trans ret),
    memoryWriteFrame_trans (call_frame pre state.toFrameState effect) memory⟩
  simpa only [dst, SHA256.compressBlocks_single _ _ (SHA256.tailFirst_size message),
    BitVec.ofNat_eq_ofNat] using result.hashWords

end P256.Proofs.HMAC.Finalize.Padding
