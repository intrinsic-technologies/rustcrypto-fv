import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.ParameterCopy

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def parameterCopyPlan (offset : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | (source, target) :: rest => source + 40 ≤ 144 ∧ target + 8 ≤ 1368 ∧
    offset+12 < 118431 ∧ Extracted.textBytes.toListFrom offset 4 =
      0x49 :: 0x8b :: (AddrMode.base 15 (.d8 (BitVec.ofNat 8 source))).modrm 1 ::
        (AddrMode.base 15 (.d8 (BitVec.ofNat 8 source))).tail ∧
    Extracted.textBytes.toListFrom (offset+4) 8 =
      0x48 :: 0x89 :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 target))).modrm 1 ::
        (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 target))).tail ∧ parameterCopyPlan (offset+12) rest

instance parameterCopyPlanDecidable (offset : Nat) (pairs : List (Nat × Nat)) : Decidable (parameterCopyPlan offset pairs) :=
  match pairs with
  | [] => isTrue trivial
  | (_, _) :: rest =>
    letI : Decidable (parameterCopyPlan (offset+12) rest) := parameterCopyPlanDecidable (offset+12) rest
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ parameterCopyPlan (offset+12) rest))

def parameterCopiesMemory (s : RamState) (pairs : List (Nat × Nat)) (memory : Ram) : Ram :=
  pairs.foldl (fun m pair => memStore m (exponentFrameBase s + BitVec.ofNat 64 pair.2)
    (memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 (32 + pair.1)) 64)) memory

def parameterCopiesComponents (s : RamState) (pairs : List (Nat × Nat)) : List Component :=
  [.reg 1, .rip] ++ pairs.map (fun pair => .mem (exponentFrameBase s + BitVec.ofNat 64 pair.2) 8)

theorem copy_parameter_pairs [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : Frame s t)
    (pairs : List (Nat × Nat)) (offset : Nat) (plan : parameterCopyPlan offset pairs)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (h15 : t.regValue .r15 = s.regValue .rsi + 32) :
    ∃ u, Advances boundary (2*pairs.length) t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset+12*pairs.length) ∧
      AgreesExcept (parameterCopiesComponents s pairs) t u ∧
      u.external = parameterCopiesMemory s pairs t.external := by
  induction pairs generalizing t offset with
  | nil => exact ⟨t, (by exact (advances_zero _ _ _).mpr rfl), hf, by simpa using hip, AgreesExcept.refl _ _, rfl⟩
  | cons pair pairs ih =>
    obtain ⟨hsrc, hdst, hbound, hload, hstore, rest⟩ := plan
    obtain ⟨u, run, frame, rip, agrees, mem⟩ :=
      copy_parameter_pair ctx hf offset pair.1 pair.2 hip h15 hsrc hdst hbound hload hstore
    have reg15 : u.regValue .r15 = s.regValue .rsi + 32 :=
      (agrees.read (n := 64) (r := 15) (by simp)).trans h15
    obtain ⟨v, run', frame', rip', agrees', mem'⟩ := ih frame (offset+12) rest rip reg15
    refine ⟨v, ?_, frame', ?_, ?_, ?_⟩
    · simpa [List.length_cons, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using run.trans run'
    · simpa [List.length_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rip'
    · apply (agrees.trans agrees').mono
      intro c hc
      simp only [parameterCopiesComponents, List.map_cons, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc ⊢
      grind only
    · rw [mem', mem]
      rfl


end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
