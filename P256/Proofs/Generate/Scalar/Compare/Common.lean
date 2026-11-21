import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.SecretKeyFromBytes.Compare

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (programLoaded_codeIn programText_slice inProgram_of_textOffset)

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess
  X86Proofs

structure ComparePre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : MemWritable s (stackPtr s + 8) 8
  avoids : ∀ a, (Component.mem (stackPtr s + 8) 8).Covers a → ¬ InProgram a

theorem ComparePre.apart {p : BitVec 64} {s : RamState} (h : ComparePre p s)
    (offset len : Nat) (hc : offset + len ≤ 118431) :
    RangeApart (stackPtr s + 8) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply h.avoids _ ⟨i, hi, rfl⟩
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset+j) (by omega)

theorem ComparePre.avoids_code {p : BitVec 64} {s : RamState} (h : ComparePre p s)
    (offset : Nat) (bytes : List UInt8) (hc : offset + bytes.length ≤ 118431)
    {e : Effect}
    (hm : ∀ c ∈ e.components, ∀ a len, c = .mem a len → a = stackPtr s + 8 ∧ len = 8) :
    e.Avoids (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) := by
  apply Effect.avoids_codeRange
  intro c hc' a len he
  obtain ⟨rfl, rfl⟩ := hm c hc' a len he
  exact h.apart offset bytes.length hc

def compareFrame (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .flags, .rip, .mem (stackPtr s + 8) 8]

theorem compare_stack {s t : RamState} (h : AgreesExcept (compareFrame s) s t) :
    stackPtr t = stackPtr s := h.read (n := 64) (r := 4) (by simp [compareFrame])

theorem compare_frame_eq {s t : RamState} (h : stackPtr t = stackPtr s) :
    compareFrame t = compareFrame s := by simp only [compareFrame, h]

theorem compare_pre_of_agrees {s t : RamState} {p q : BitVec 64}
    (h : ComparePre p s) (hf : AgreesExcept (compareFrame s) s t)
    (rip : t.RIP = q) : ComparePre q t := by
  have hs := compare_stack hf
  refine ⟨rip, ?_, ?_⟩
  · rw [hs]
    exact ⟨h.writable.low,
      fun i hi => hf.grow _ (h.writable.mem i hi), h.writable.tables⟩
  · simpa only [hs] using h.avoids

theorem compare_loaded {s t : RamState} {p : BitVec 64}
    (pre : ComparePre p s) (loaded : ProgramLoaded s)
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
    (block : AdvanceTriple boundary P (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      bytes)
      (Effect.post E))
    (hSize : offset + bytes.length ≤ 118431)
    (hBytes : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pre : ComparePre p s)
    (hp : P s) (hq : (E s).rip = q) (frame : (E s).components ⊆ compareFrame s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      ComparePre q t ∧ (E s).Holds s t ∧ AgreesExcept (compareFrame s) s t := by
  obtain ⟨fuel, t, run, ready', _, effect⟩ := block s ready
    (programText_slice (programLoaded_codeIn loaded) offset bytes hSize hBytes) hp
  have hf := effect.agrees.mono frame
  exact ⟨fuel, t, run, ready', compare_loaded pre loaded hf,
    compare_pre_of_agrees pre hf (effect.rip.trans hq), effect, hf⟩

def compareInput (s : RamState) : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs :=
  ⟨s.regValue .r13, s.regValue .r12, s.regValue .r15, s.regValue .r14⟩

theorem compare_trans {s t u : RamState} (h : AgreesExcept (compareFrame s) s t)
    (h' : AgreesExcept (compareFrame t) t u) : AgreesExcept (compareFrame s) s u := by
  rw [compare_frame_eq (compare_stack h)] at h'
  exact (h.trans h').mono (by simp)

end P256.Proofs.Generate.Scalar
