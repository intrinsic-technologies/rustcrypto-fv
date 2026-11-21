import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Mark
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Copy
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Payload

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Instructions.CrossPageStore (Writable)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10df89
  countReadable : MemReadable s (rspOf s + 208) 8
  readable : ∀ i ∈ ([72,80,88,96,104,112,120] : List Nat),
    MemReadable s (rspOf s + BitVec.ofNat 64 i) 8
  writable : ∀ i ∈ ([8,16,24,32,40,48,56,64,105,113,120,128] : List Nat),
    Writable s (rspOf s + BitVec.ofNat 64 i) 8
  marker : Writable s (rspOf s + 104) 1
  codeApart : ∀ i ∈ ([8,16,24,32,40,48,56,64,105,113,120,128] : List Nat),
    ∀ offset len : Nat, offset + len ≤ 146 →
      RangeApart (rspOf s + BitVec.ofNat 64 i) 8
        (0x10df89 + BitVec.ofNat 64 offset) len
  markerApart : ∀ offset len : Nat, offset + len ≤ 146 →
    RangeApart (rspOf s + 104) 1 (0x10df89 + BitVec.ofNat 64 offset) len

def bytes : List UInt8 := Mark.bytes ++ Copy.bytes

def effect : RamState → Effect := Effect.seq Mark.effect Copy.effect

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10df89 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xdf89 bytes
    (by decide +kernel) (by decide +kernel)

private theorem markPre {s : RamState} (h : Pre s) : Mark.Pre s := by
  refine ⟨h.rip,h.countReadable,?_,h.marker,?_,?_⟩
  · intro i hi
    exact h.writable i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)
  · intro i hi offset len bound
    exact h.codeApart i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega) offset len (by omega)
  · intro offset len bound
    exact h.markerApart offset len (by omega)

private theorem mark_avoids {s : RamState} (h : Pre s) :
    (Mark.effect s).Avoids (codeRange 0x10df89 bytes) := by
  apply Effect.avoids_codeRange
  x86_norm [Mark.effect]
  exact ⟨h.markerApart 0 146 (by decide), h.codeApart 120 (by decide) 0 146 (by decide),
    h.codeApart 113 (by decide) 0 146 (by decide),
    h.codeApart 105 (by decide) 0 146 (by decide),
    h.codeApart 128 (by decide) 0 146 (by decide)⟩

private theorem copyPre {s t : RamState} (h : Pre s) (he : (Mark.effect s).Holds s t) :
    Copy.Pre t := by
  have rsp : rspOf t = rspOf s := he.agrees.read (n := 64) (r := 4)
    (by simp [Mark.effect, Effect.components, Write.component, Operand.component])
  refine ⟨he.rip,?_,?_,?_⟩
  · intro i hi
    rw [rsp]
    exact (h.readable i hi).of_holds he
  · intro i hi
    rw [rsp]
    exact (h.writable i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).of_holds he
  · intro i hi offset len bound
    rw [rsp]
    have apart := h.codeApart i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega) (61+offset) len (by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc,
      BitVec.reduceAdd] using apart

private theorem copy_avoids {s t : RamState} (h : Pre s) (he : (Mark.effect s).Holds s t) :
    (Copy.effect t).Avoids (codeRange 0x10df89 bytes) := by
  have rsp : rspOf t = rspOf s := he.agrees.read (n := 64) (r := 4)
    (by simp [Mark.effect, Effect.components, Write.component, Operand.component])
  apply Effect.avoids_codeRange
  x86_norm [Copy.effect]
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  x86_norm at rsp
  rw [rsp]
  exact ⟨h.codeApart 64 (by decide) 0 146 (by decide),
    h.codeApart 56 (by decide) 0 146 (by decide),
    h.codeApart 48 (by decide) 0 146 (by decide),
    h.codeApart 40 (by decide) 0 146 (by decide),
    h.codeApart 32 (by decide) 0 146 (by decide),
    h.codeApart 24 (by decide) 0 146 (by decide),
    h.codeApart 16 (by decide) 0 146 (by decide),
    h.codeApart 8 (by decide) 0 146 (by decide)⟩

theorem run_steps [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10df89 bytes)
      (fun s t => ∃ a, (Mark.effect s).Holds s a ∧ (Copy.effect a).Holds a t) := by
  intro s ready loaded pre
  obtain ⟨fuelA,a,runA,readyA,_,mark⟩ :=
    Mark.run boundary outside s ready
      (loaded.mono (codeRange_slice_subset 0x10df89 bytes 0 61)) (markPre pre)
  have loadedA := mark.codeIn (mark_avoids pre) loaded
  obtain ⟨fuelB,t,runB,readyT,_,copy⟩ :=
    Copy.run boundary outside a readyA
      (loadedA.mono (codeRange_slice_subset 0x10df89 bytes 61 85)) (copyPre pre mark)
  exact ⟨fuelA+fuelB,t,runA.trans runB,readyT,
    copy.codeIn (copy_avoids pre mark) loadedA,a,mark,copy⟩

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10df89 bytes) (Effect.post effect) := by
  apply (run_steps boundary outside).conseq
  intro s t _ result
  obtain ⟨a,mark,copy⟩ := result
  exact mark.seq Copy.localEffect
    (by simp [Mark.effect, Write.Full, Operand.Full]) copy

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad
