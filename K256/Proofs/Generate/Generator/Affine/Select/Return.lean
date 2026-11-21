import K256.Proofs.Generate.Generator.Affine.State
import K256.Proofs.Generate.LIR.Fn10fe50
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC

theorem returnPoint {fr : Activation} {a : Registers} {m : Ram}
    (atoms : Atom.All Extracted.programImage a m (Fn10fe50.frameAt .l10ee65 fr)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10ee65, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ out.store = m ∧
      Atom.All Extracted.programImage out.values m (Fn10fe50.doneAt fr) := by
  simp only [Fn10fe50.frameAt, Fn10fe50.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, rdi, _, mxcsr, ftw, fcw, rbx, r12, r13, r14, r15, rbp, retRead, retVal,
    retLow, writeStack, _, _, _⟩ := atoms
  have sp : a[4].get 64 = fr.rsp - 232 := congrArg (Value.get 64) rsp
  have bx : a[3].get 64 = fr.rdi := congrArg (Value.get 64) rdi
  have readSlot (k : BitVec 64) (bound : ((0 - k) - (0 - 976) : BitVec 64).toNat + 8 ≤ 976) :
      LoadOk m (fr.rsp - k) 8 :=
    LoadOk.of_offsets writeStack.readable (addr_sub _ _) (addr_sub _ _) bound
  have retOk : LoadOk m fr.rsp 8 := ⟨retRead.low, retRead.present⟩
  have a48 : fr.rsp - 232 + 184 = fr.rsp - 48 := by bv_omega
  have a40 : fr.rsp - 232 + 192 = fr.rsp - 40 := by bv_omega
  have a32 : fr.rsp - 232 + 200 = fr.rsp - 32 := by bv_omega
  have a24 : fr.rsp - 232 + 208 = fr.rsp - 24 := by bv_omega
  have a16 : fr.rsp - 232 + 216 = fr.rsp - 16 := by bv_omega
  have a8 : fr.rsp - 232 + 224 = fr.rsp - 8 := by bv_omega
  have a0 : fr.rsp - 232 + 232 = fr.rsp := BitVec.sub_add_cancel _ _
  have aDone : fr.rsp - 232 + 240 = fr.rsp + 8 := by bv_omega
  suffices ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l10ee65, a, m⟩ = .returned out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ out.store = m ∧
      Atom.All Extracted.programImage out.values m (Fn10fe50.doneAt fr) by
    obtain ⟨out, run, tag, store, done_⟩ := this
    exact ⟨out, .done (by simp only [Program.step, run, Transfer.next]), tag, store, done_⟩
  refine ⟨?out, ?run, ?tag, ?store, ?done_⟩
  case run =>
    cfg_eval
    simp only [sp, bx, a48, a40, a32, a24, a16, a8, a0, aDone, readSlot 48 (by decide), readSlot 40 (by decide),
      readSlot 32 (by decide), readSlot 24 (by decide), readSlot 16 (by decide), readSlot 8 (by decide),
      retOk, retVal, retLow, rbx, rbp, r12, r13, r14, r15, and_self, ↓reduceIte]
    rfl
  case tag => rfl
  case store => rfl
  case done_ =>
    simp only [Fn10fe50.doneAt, Atom.All, Atom.Holds]
    exact ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, rfl, mxcsr, ftw, fcw, trivial⟩

end K256.Proofs.Generate.Generator.Affine
