import AesGcm.Proofs.AES16.Encrypt.Loop

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem rounds (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (loc : LIR.lifted.Location)
    (hsep : (callStack fr).Disjoint (span fr.rsi (16 * ((variant use256).Nr + 1))))
    (hwork : WorkingState code use256 key fr loc)
    (hloop : LoopState use256 key input fr 0 (by omega) loc) :
    ∃ last : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨last, []⟩ ∧
      WorkingState code use256 key fr last ∧ FinalState use256 key input fr last := by
  have walk : ∀ (fuel j : Nat) (hj : 4 * j < (variant use256).Nr + 1),
      j ≤ lastIteration use256 → j + fuel = lastIteration use256 →
      ∀ loc : LIR.lifted.Location, WorkingState code use256 key fr loc →
        LoopState use256 key input fr j hj loc →
        ∃ last : LIR.lifted.Location,
          (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨last, []⟩ ∧
          WorkingState code use256 key fr last ∧ FinalState use256 key input fr last := by
    intro fuel
    induction fuel with
    | zero =>
      intro j hj hb he loc hw hl
      obtain ⟨next, hr, hn, hs⟩ := loop_step use256 code hcode key input fr j hj hb loc hsep hw hl
      rcases hs with ⟨_, hf⟩ | ⟨hlt, _⟩
      · exact ⟨next, hr, hn, hf⟩
      · omega
    | succ fuel ih =>
      intro j hj hb he loc hw hl
      obtain ⟨next, hr, hn, hs⟩ := loop_step use256 code hcode key input fr j hj hb loc hsep hw hl
      rcases hs with ⟨heq, _⟩ | ⟨hlt, hnext, hs⟩
      · omega
      · obtain ⟨last, hrest, hwlast, hlast⟩ := ih (j + 1) hnext (by omega) (by omega) next hn hs
        exact ⟨last, hr.trans hrest, hwlast, hlast⟩
  exact walk (lastIteration use256) 0 (by omega) (Nat.zero_le _) (Nat.zero_add _) loc hwork hloop

end AesGcm.Proofs.Machine.AES16.Encrypt
