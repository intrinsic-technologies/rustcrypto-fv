import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Steps
import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow

set_option autoImplicit false
namespace P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def components (base : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 13, .reg 14, .flags, .rip, .mem (base + 8) 1, .mem (base + 8) 8,
    .mem (base + 0x50) 8, .mem (base + 0x58) 8, .mem (base + 0x60) 8,
    .mem (base + 0x68) 8, .mem (base + 0x70) 8]

theorem agrees_wide {s t : RamState} {base : BitVec 64}
    (h : AgreesExcept (components base) s t) :
    AgreesExcept (SquareFour.components base) s t := by
  apply h.widen
  · intro c hc hm
    simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [SquareFour.components, Component.isMem]
  · intro address c hc ha
    simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨i, hi, rfl⟩ := ha
    · simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using
        (offset_covers (base := base) (i := 8 + i) (by unfold scratchOffset; omega))
    · simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using
        (offset_covers (base := base) (i := 8 + i) (by unfold scratchOffset; omega))
    · simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using
        (offset_covers (base := base) (i := 80 + i) (by unfold scratchOffset; omega))
    · simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using
        (offset_covers (base := base) (i := 88 + i) (by unfold scratchOffset; omega))
    · simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using
        (offset_covers (base := base) (i := 96 + i) (by unfold scratchOffset; omega))
    · simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using
        (offset_covers (base := base) (i := 104 + i) (by unfold scratchOffset; omega))
    · simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using
        (offset_covers (base := base) (i := 112 + i) (by unfold scratchOffset; omega))

theorem trans {s t u : RamState} {base : BitVec 64}
    (h : AgreesExcept (components base) s t) (h' : AgreesExcept (components base) t u) :
    AgreesExcept (components base) s u :=
  (h.trans h').mono (fun _ hc => (List.mem_append.mp hc).elim id id)

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    {E : RamState → Effect} {pc : Nat} {bytes : List UInt8}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (triple : P256.Proofs.Common.Field.AdvanceTriple boundary
      (fun t => ExponentFrame s t ∧ t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 pc) bytes) (Effect.post E))
    (bound : pc + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom pc bytes.length = bytes)
    (ag : (E t).components ⊆ components (exponentFrameBase s)) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (E t).Holds t u ∧ AgreesExcept (components (exponentFrameBase s)) t u := by
  obtain ⟨fuel,u,he,hr,_,hh⟩ := triple t (readyToStep hf.machine hf.bindingsSupported)
    (programText_slice (programLoaded_codeIn hf.loaded) pc bytes bound code) ⟨hf,hip⟩
  have ha := hh.agrees.mono ag
  exact ⟨u,fuel,he,frame_of_agrees ctx hf hr (agrees_wide ha),hh,ha⟩

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
