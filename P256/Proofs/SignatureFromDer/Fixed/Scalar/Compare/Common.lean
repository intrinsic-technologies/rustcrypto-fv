import P256.Proofs.SecretKeyFromBytes.Arithmetic
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare.Slot
import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Program.Stack

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare (BorrowSlotPre)
open P256.Proofs.Program (programLoaded_codeIn programText_slice)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def compareFrame (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .flags, .rip, .mem (stackPtr s + 8) 8]

theorem compare_stack {s t : RamState} (h : AgreesExcept (compareFrame s) s t) :
    stackPtr t = stackPtr s := h.read (n := 64) (r := 4) (by simp [compareFrame])

theorem compare_frame_eq {s t : RamState} (h : stackPtr t = stackPtr s) :
    compareFrame t = compareFrame s := by simp only [compareFrame, h]

theorem compare_pre_of_agrees {s t : RamState} {p q : BitVec 64}
    (h : BorrowSlotPre p s) (hf : AgreesExcept (compareFrame s) s t)
    (rip : t.RIP = q) : BorrowSlotPre q t := by
  have hs := compare_stack hf
  refine ⟨rip, ?_, ?_⟩
  · rw [hs]
    exact P256.Proofs.Program.writable_of_grow h.writable hf.grow
  · simpa only [hs] using h.avoids

theorem compare_loaded {s t : RamState} {p : BitVec 64}
    (pre : BorrowSlotPre p s) (loaded : ProgramLoaded s)
    (h : AgreesExcept (compareFrame s) s t) : ProgramLoaded t := by
  intro a b hb
  refine (h.byte ?_).trans (loaded a b hb)
  intro c hc hv
  simp only [compareFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  · exact pre.avoids a hv ⟨b, hb⟩

theorem compare_run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {p q : BitVec 64} {offset : Nat} {bytes : List UInt8} {P : RamState → Prop}
    {E : RamState → Effect}
    (block : AdvanceTriple boundary P (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes)
      (Effect.post E))
    (hSize : offset + bytes.length ≤ 118431)
    (hBytes : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pre : BorrowSlotPre p s)
    (hp : P s) (hq : (E s).rip = q) (frame : (E s).components ⊆ compareFrame s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      BorrowSlotPre q t ∧ (E s).Holds s t ∧ AgreesExcept (compareFrame s) s t := by
  obtain ⟨fuel, t, run, ready', _, effect⟩ := block s ready
    (programText_slice (programLoaded_codeIn loaded) offset bytes hSize hBytes) hp
  have hf := effect.agrees.mono frame
  exact ⟨fuel, t, run, ready', compare_loaded pre loaded hf,
    compare_pre_of_agrees pre hf (effect.rip.trans hq), effect, hf⟩

def compareInput (s : RamState) : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs :=
  ⟨s.regValue .r15, s.regValue .r12, s.regValue .r13, s.regValue .rbp⟩

theorem compare_trans {s t u : RamState} (h : AgreesExcept (compareFrame s) s t)
    (h' : AgreesExcept (compareFrame t) t u) : AgreesExcept (compareFrame s) s u := by
  rw [compare_frame_eq (compare_stack h)] at h'
  exact (h.trans h').mono (by simp)

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare
