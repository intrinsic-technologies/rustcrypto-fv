import P256.Proofs.Sec1.Affine.Dispatch
import P256.Proofs.Sec1.Affine.Identity
import P256.Proofs.Sec1.Affine.Epilogue
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def CompressedCorrect : Prop :=
  ∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {tag : UInt8}, AffineDecodePre s boundary bytes → bytes.size = 33 →
    bytes.data[0]? = some tag → (tag = 2 ∨ tag = 3) → Routed s t tag →
    t.RIP = 0x110108 →
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      AffineResultAt u (s.regValue .rdi) (P256.Spec.Points.decodePoint bytes)

def CompactCorrect : Prop :=
  ∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray},
    AffineDecodePre s boundary bytes → bytes.size = 33 → bytes.data[0]? = some 5 →
    Routed s t 5 → t.RIP = 0x11020f →
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      AffineResultAt u (s.regValue .rdi) (P256.Spec.Points.decodePoint bytes)

def UncompressedCorrect : Prop :=
  ∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray},
    AffineDecodePre s boundary bytes → bytes.size = 65 → bytes.data[0]? = some 4 →
    Routed s t 4 → t.RIP = 0x110635 →
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      AffineResultAt u (s.regValue .rdi) (P256.Spec.Points.decodePoint bytes)

theorem affine_decode_of_branches (compressed : CompressedCorrect)
    (compact : CompactCorrect) (uncompressed : UncompressedCorrect)
    [Bindings] {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) :
    ∃ t, CalleeResult s t boundary 80 3360 ∧
      AffineResultAt t (s.regValue .rdi) (P256.Spec.Points.decodePoint bytes) := by
  have finish_branch {a b : RamState} {n m : Nat}
      (beforeRun : Advances boundary n s a) (run : Advances boundary m a b)
      (frame : Frame s b) (rip : b.RIP = 0x110d22)
      (value : AffineResultAt b (s.regValue .rdi) (P256.Spec.Points.decodePoint bytes)) :
      ∃ t, CalleeResult s t boundary 80 3360 ∧
        AffineResultAt t (s.regValue .rdi) (P256.Spec.Points.decodePoint bytes) := by
    obtain ⟨t, result, memory⟩ := finish pre.toCalleePre frame rip ⟨n + m, beforeRun.trans run⟩
    exact ⟨t, result, value.of_bytes_eq (fun _ _ ↦ by rw [memory])⟩
  rcases pre.input.1 with identity | ⟨size, tag | tag | tag⟩ | ⟨size, tag⟩
  · subst bytes
    obtain ⟨n, a, beforeRun, state, rip⟩ := dispatch_identity pre
    obtain ⟨m, b, run, frame, last, value⟩ := Identity.correct pre state rip
    exact finish_branch beforeRun run frame last value
  · have tagValue : bytes.data[0]?.getD 0 = 2 := by rw [tag]; rfl
    obtain ⟨n, a, beforeRun, state, rip⟩ := dispatch_compressed pre (Or.inl tagValue)
    rw [tagValue] at state
    obtain ⟨m, b, run, frame, last, value⟩ :=
      compressed pre size tag (Or.inl rfl) state rip
    exact finish_branch beforeRun run frame last value
  · have tagValue : bytes.data[0]?.getD 0 = 3 := by rw [tag]; rfl
    obtain ⟨n, a, beforeRun, state, rip⟩ := dispatch_compressed pre (Or.inr tagValue)
    rw [tagValue] at state
    obtain ⟨m, b, run, frame, last, value⟩ :=
      compressed pre size tag (Or.inr rfl) state rip
    exact finish_branch beforeRun run frame last value
  · have tagValue : bytes.data[0]?.getD 0 = 5 := by rw [tag]; rfl
    obtain ⟨n, a, beforeRun, state, rip⟩ :=
      dispatch_uncompressed_or_compact pre (Or.inr tagValue)
    rw [tagValue] at state rip
    obtain ⟨m, b, run, frame, last, value⟩ := compact pre size tag state (by simpa using rip)
    exact finish_branch beforeRun run frame last value
  · have tagValue : bytes.data[0]?.getD 0 = 4 := by rw [tag]; rfl
    obtain ⟨n, a, beforeRun, state, rip⟩ :=
      dispatch_uncompressed_or_compact pre (Or.inl tagValue)
    rw [tagValue] at state rip
    obtain ⟨m, b, run, frame, last, value⟩ := uncompressed pre size tag state (by simpa using rip)
    exact finish_branch beforeRun run frame last value

end P256.Proofs.Sec1.Affine
