import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical.Slot
import P256.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def components (y : Bool) (t : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2] ++
    (if y then [.reg 7, .reg 8, .reg 12, .reg 13, .reg 14, .reg 15]
    else [.reg 5, .reg 6, .reg 7, .reg 12, .reg 13, .reg 15]) ++
    [.flags, .rip, .mem (stackPtr t + 16) 8]

theorem stack_eq {y : Bool} {s t : RamState} (agrees : AgreesExcept (components y s) s t) :
    stackPtr t = stackPtr s := agrees.read (n := 64) (r := 4) (by cases y <;> simp [components])

theorem agrees_trans {y : Bool} {s t u : RamState}
    (first : AgreesExcept (components y s) s t)
    (second : AgreesExcept (components y t) t u) : AgreesExcept (components y s) s u := by
  have eq : components y t = components y s := by simp only [components, stack_eq first]
  rw [eq] at second
  exact (first.trans second).mono (by simp)

theorem writes [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (y : Bool) (pre : AffineDecodePre s boundary bytes) (state : Frame s t) :
    WritesWithin (components y t) #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 3360] := by
  intro c hc a ha
  have hm : c = .mem (stackPtr t + 16) 8 := by
    cases y <;> simp only [components, Bool.false_eq_true, ↓reduceIte, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    all_goals rcases hc with ((rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl) |
      rfl | rfl | rfl
    all_goals first | exact ha.elim | rfl
  subst c
  refine ⟨ScalarFrame.workRegion s 3360, by simp, ?_⟩
  have addr : stackPtr t + 16 = stackPtr s - 744 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  rw [addr] at ha
  exact ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
variable {offset : Nat} {bytes : List UInt8} {P : RamState → Prop} {E : RamState → Effect}

theorem run (y : Bool) (pre : AffineDecodePre s boundary input) (state : Frame s t)
    (block : AdvanceTriple boundary P
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post E))
    (size : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (hp : P t) (allowed : (E t).components ⊆ components y t) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (E t).Holds t u ∧
      AgreesExcept (components y t) t u := by
  obtain ⟨fuel, u, execution, ready, _, effect⟩ := block t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes size code) hp
  have agrees := effect.agrees.mono allowed
  exact ⟨fuel, u, execution, state.after_effect pre.toCalleePre (by decide) ready agrees
    (writes y pre state) (by cases y <;> simp [components])
    (hdf := by cases y <;> simp [components])
    (hmxcsr := by cases y <;> simp [components])
    (hfcw := by cases y <;> simp [components]), effect, agrees⟩

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
