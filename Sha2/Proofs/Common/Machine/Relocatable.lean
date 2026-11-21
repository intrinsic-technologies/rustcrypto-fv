import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

def BlockInProgram (p : BitVec 64) (size : Nat) : Prop :=
  ∀ i ≤ size, InProgram (p + BitVec.ofNat 64 i)

theorem blockInProgram_of_textOffset (offset size : Nat) (bound : offset + size < 71757) :
    BlockInProgram (Extracted.textAddress + BitVec.ofNat 64 offset) size := by
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset + i) (by omega)

end Sha2.Proofs.Common.Machine

macro "advance_reloc_begin " step:term " next " hn:term : tactic => `(tactic| (
  refine Sha2.Proofs.Common.Field.AdvanceTriple.block_first ?k $step ?sub ?pre ?av ?next
  try (case sub => x86_sub)
  try (case' pre => x86_carry_begin)
  try (case' av => x86_carry_av)
  try (case next => intro _ _; x86_norm; exact $hn)
  case' k => x86_norm))

macro "advance_reloc_then " step:term " next " hn:term : tactic => do
  let (s, t, hP, hH, hO) := (Lean.mkIdent `s, Lean.mkIdent `t, Lean.mkIdent `hP,
    Lean.mkIdent `hH, Lean.mkIdent `hO)
  `(tactic| (
    refine Sha2.Proofs.Common.Field.AdvanceTriple.block_then
      ?k $step ?loc ?sub ?full ?mid
    try (case loc => x86_local)
    try (case sub => x86_sub)
    try (case full => x86_full)
    (case' mid =>
      intro $s $t $hP $hH $hO
      refine (fun h : (_ ∧ _) ∧ _ => ⟨h.1.1, h.1.2, h.2⟩) ?_
      constructor
      · x86_carry_mid $hP $hH $hO
      · x86_norm; exact $hn)
    case' k => x86_norm))
