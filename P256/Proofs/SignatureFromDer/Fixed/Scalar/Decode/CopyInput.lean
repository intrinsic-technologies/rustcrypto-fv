import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.Input

set_option autoImplicit false

open P256.Proofs.Program (CalleePre)
open P256.Proofs.Program.ScalarFrame

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_input [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : Stage s t boundary)
    (rip : t.RIP = 0x10fa41) (source : t.regValue .rsi = s.regValue .rsi)
    (bytes : (registerRegion s .rsi 32).HasBytes s.external input) :
    ∃ u, CopiedState s u boundary input := by
  let src : RamState → BitVec 64 := fun v => (Operand.reg 6 : Operand 64).read v + 0
  let dst : RamState → BitVec 64 := fun v => stackPtr v + 72
  have srcEq : src t = s.regValue .rsi := by
    change t.regValue .rsi + 0 = s.regValue .rsi
    exact (BitVec.add_zero _).trans source
  have dstEq : dst t = stackPtr s - 80 := Program.ScalarFrame.scalar_stack_address (frameOffset := 152) state.rsp (by decide) (by decide)
  have readable : MemReadable t (src t) 32 := by
    rw [srcEq]
    simpa only [BitVec.add_zero] using input_readable pre state.toFrameState
      (offset := 0) (by decide)
  have apart : RangeApart (dst t) 32 (src t) 32 := by
    rw [srcEq]
    simpa only [BitVec.add_zero] using input_stack_apart pre state.toFrameState
      (offset := 0) (by decide)
  have cp := copy_stack_pre pre state.toFrameState (offset := 72)
    (by decide) rfl rip readable apart
  obtain ⟨u, ust, effect⟩ := copy_execute pre state (Copy.run boundary pre.outerBoundary)
    (Copy.code state.loaded) cp (offset := 72) (by decide) rfl
  have agree := Copy32.frame effect
  have sp : stackPtr u = stackPtr t := agree.read (n := 64) (r := 4) (by simp [Copy32.components])
  have output : MemReadable u (dst t) 32 := by
    have h := Program.ScalarFrame.stack_readable (frameOffset := 152) pre ust.toFrameState (by decide) (offset := 72) (len := 32) (by decide)
    rw [sp] at h
    exact h
  have copied := Program.ScalarFrame.Copy32.copy_bytes effect readable output
  change ∀ i < 32, u.external[dst t + BitVec.ofNat 64 i]? = t.external[src t + BitVec.ofNat 64 i]? at copied
  rw [srcEq, dstEq] at copied
  have inputBytes := Program.ScalarFrame.FrameState.input_bytes pre state.toFrameState bytes
  refine ⟨u, ⟨ust, effect.rip, bytes.1, ?_⟩⟩
  intro i
  have hi : i.val < 32 := by have := i.isLt; have size : input.size = 32 := bytes.1; omega
  change u.external[BitVec.ofNat 64 ((stackPtr s - 80).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, copied i.val hi]
  have h := inputBytes.2 i
  change t.external[BitVec.ofNat 64 ((s.regValue .rsi).toNat + i.val)]? = _ at h
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode
