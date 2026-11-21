import Sha2.Proofs.Wrapper512.Absorb.Short
import Sha2.Proofs.Wrapper512.Absorb.Large
import Sha2.Proofs.Wrapper512.Absorb.Next
import Sha2.Proofs.Wrapper512.Absorb.Contract

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Wrapper (prefixMessage)

theorem step [Bindings] (body : Common.SHA512.Compression.BlockCorrect)
    {v : Variant} {initial : RamState} {inputs : Array Input} {form : Form}
    (ctx : Context v initial inputs form) (table : form ≠ .digest := by decide) :
    Step v initial inputs form := by
  constructor
  intro index state loop
  obtain ⟨a, loaded, ⟨loadFuel, loadRun⟩, loadFrame⟩ := load_slice ctx loop table
  obtain ⟨b, selected, ripB, ⟨selectFuel, selectRun⟩, selectFrame⟩ := select_size ctx loaded table
  by_cases small : (inputs[index]'loop.remaining).bytes.size <
      128 - (prefixMessage inputs index).size % 128
  · have entry : b.RIP = v.pc (v.shortOffset form) form := by
      simpa only [small, ite_true] using ripB
    obtain ⟨c, buffered, ripC, indexC, countC, savedC, bufferC, targetC, ⟨absorbFuel, absorbRun⟩, absorbFrame⟩ :=
      short ctx selected.toSliceState entry small table
    obtain ⟨t, result, ⟨nextFuel, nextRun⟩, nextFrame⟩ :=
      advance_iteration ctx buffered false ripC indexC countC loop.remaining
        table bufferC targetC (by intros; contradiction) savedC
    exact ⟨t, result, ⟨_, ((loadRun.trans selectRun).trans absorbRun).trans nextRun⟩,
      fun address outside => ((nextFrame address outside).trans (absorbFrame address outside)).trans
        ((selectFrame address outside).trans (loadFrame address outside))⟩
  · have entry : b.RIP = v.pc (v.largeOffset form) form := by
      simpa only [small, ite_false] using ripB
    obtain ⟨c, buffered, ripC, indexC, countC, savedC, bufferC, targetC, activeC, ⟨absorbFuel, absorbRun⟩, absorbFrame⟩ :=
      large body ctx selected entry (by omega) table
    have active : ∀ second, form = .traitFinalizeIntoReset second →
        true = true → c.regValue .rbx = stackPtr c + 32 := by
      intro second h _
      subst form
      have active := activeC second rfl
      change c.regValue .rbx = stackPtr c + 32
      rw [buffered.rsp]
      change c.regValue .rbx = stackPtr initial - 648 + 32
      change c.regValue .rbx = stackPtr initial - 616 at active
      rw [active]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    obtain ⟨t, result, ⟨nextFuel, nextRun⟩, nextFrame⟩ :=
      advance_iteration ctx buffered true ripC indexC countC loop.remaining
        table bufferC targetC active savedC
    exact ⟨t, result, ⟨_, ((loadRun.trans selectRun).trans absorbRun).trans nextRun⟩,
      fun address outside => ((nextFrame address outside).trans (absorbFrame address outside)).trans
        ((selectFrame address outside).trans (loadFrame address outside))⟩

end Sha2.Proofs.Wrapper512.Absorb
