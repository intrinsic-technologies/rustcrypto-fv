import P256.Proofs.Sec1.Decompress.Input.Canonical.HighWord
import P256.Proofs.Program.Stack

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (programLoaded_codeIn programText_slice)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def canonicalFrame (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 8, .reg 9, .reg 14,
    .flags, .rip, .mem (stackPtr s) 8, .mem (stackPtr s + 184#64) 8]

theorem canonical_stack {s t : RamState} (h : AgreesExcept (canonicalFrame s) s t) :
    stackPtr t = stackPtr s := h.read (n := 64) (r := 4) (by simp [canonicalFrame])

theorem canonical_frame_eq {s t : RamState} (h : stackPtr t = stackPtr s) :
    canonicalFrame t = canonicalFrame s := by simp only [canonicalFrame, h]

theorem CanonicalPre.of_agrees {s t : RamState} {p q : BitVec 64}
    (h : CanonicalPre p s) (hf : AgreesExcept (canonicalFrame s) s t)
    (rip : t.RIP = q) : CanonicalPre q t := by
  have hs := canonical_stack hf
  refine ⟨⟨rip, ?_, ?_⟩, ?_, ?_⟩
  · rw [hs]
    exact P256.Proofs.Program.writable_of_grow h.writable hf.grow
  · simpa only [hs] using h.avoids
  · rw [hs]
    exact P256.Proofs.Program.writable_of_grow h.pointerWritable hf.grow
  · simpa only [hs] using h.pointerAvoids

theorem canonical_loaded {s t : RamState} {p : BitVec 64}
    (pre : CanonicalPre p s) (loaded : ProgramLoaded s)
    (h : AgreesExcept (canonicalFrame s) s t) : ProgramLoaded t := by
  intro a b hb
  refine (h.byte ?_).trans (loaded a b hb)
  intro c hc hv
  simp only [canonicalFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  · exact pre.avoids a hv ⟨b, hb⟩
  · exact pre.pointerAvoids a hv ⟨b, hb⟩

theorem canonical_run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {p q : BitVec 64} {offset : Nat} {bytes : List UInt8} {P : RamState → Prop}
    {E : RamState → Effect}
    (block : AdvanceTriple boundary P (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes)
      (Effect.post E))
    (hSize : offset + bytes.length ≤ 118431)
    (hBytes : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pre : CanonicalPre p s)
    (hp : P s) (hq : (E s).rip = q) (frame : (E s).components ⊆ canonicalFrame s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      CanonicalPre q t ∧ (E s).Holds s t ∧ AgreesExcept (canonicalFrame s) s t := by
  obtain ⟨fuel, t, run, ready', _, effect⟩ := block s ready
    (programText_slice (programLoaded_codeIn loaded) offset bytes hSize hBytes) hp
  have hf := effect.agrees.mono frame
  exact ⟨fuel, t, run, ready', canonical_loaded pre loaded hf,
    pre.of_agrees hf (effect.rip.trans hq), effect, hf⟩

end P256.Proofs.Sec1.Decompress.Input
