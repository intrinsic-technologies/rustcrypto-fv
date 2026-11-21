import P256.Proofs.Sec1.Decompress.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Cubic

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field

abbrev FrameState [Bindings] (s t : RamState) := ScalarFrame.FrameState s t 80 2592 408

theorem input_stack_address {s t : RamState} (h : stackPtr t = stackPtr s - 408)
    {offset : Nat} (ho : offset ≤ 408) :
    stackPtr t + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (408-offset) :=
  ScalarFrame.scalar_stack_address h (by decide) ho

theorem montgomeryAt_of_copy {s t : RamState} {a b : BitVec 64} {x : Nat}
    (hx : MontgomeryAt s a x)
    (memory : ∀ i < 32, t.external[b + BitVec.ofNat 64 i]? =
      s.external[a + BitVec.ofNat 64 i]?) : MontgomeryAt t b x :=
  ⟨hx.1, hx.2.1, fun i hi ↦ (memory i hi).trans (hx.2.2 i hi)⟩

theorem agrees_of_footprint {s t : RamState} {small large : List Component}
    (h : AgreesExcept small s t)
    (hreg : ∀ c ∈ small, c.isMem = false → c ∈ large)
    (hmem : ∀ c ∈ small, ∀ a, c.Covers a → ∃ d ∈ large, d.Covers a) :
    AgreesExcept large s t := by
  refine ⟨?_, ?_, h.rest, h.grow⟩
  · intro c hc hm
    exact h.agree c (fun hs ↦ hc (hreg c hs hm)) hm
  · intro a ha
    apply h.memory a
    intro c hc hcover
    obtain ⟨d, hd, hcover'⟩ := hmem c hc a hcover
    exact ha d hd hcover'

theorem copy_byte {s t u : RamState}
    (frame : AgreesExcept [.reg 0, .reg 1, .rip, .mem (stackPtr s-408) 32] t u)
    {offset len : Nat}
    (apart : OffsetsApart (-(408 : BitVec 64)) 32 (-BitVec.ofNat 64 offset) len)
    (bound : 32 + len < 2^64) {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply frame.byte
  intro c hc ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j, hj, he⟩ := ha
  apply OffsetsApart.ne apart (stackPtr s) hj hi bound
  simpa only [BitVec.sub_eq_add_neg] using he.symm

end P256.Proofs.Sec1.Decompress.Cubic
