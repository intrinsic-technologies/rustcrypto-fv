import K256.Proofs.Sec1.LIR.Fn121480.Frame
import K256.Proofs.ParseSignature.BlackBox

namespace K256.Proofs.Sec1.Affine

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR

theorem returnAffine {code : CodeMap} (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (atoms : Atom.All code args mem (Fn121480.frameAt .l121599 fr)) :
    ∃ out, program.runBlock (dialect code) ⟨.l121599, args, mem⟩ = .returned out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ out.store = mem ∧
      Atom.All code out.values mem (Fn121480.doneAt fr) ∧ out.values[0] = ⟨64, fr.rdi⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ Activation.argumentNumbers → out.values[i] = args[i]) := by
  simp only [Fn121480.frameAt, Fn121480.frameAtG2, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, outPtr, r13, mxcsr, ftw, fcw, rbx, r12, r14, r15, rbp, retRead, retVal,
    retLow, writeStack, _, _, _⟩ := atoms
  have sp : args[4].get 64 = fr.rsp - 136 := congrArg (Value.get 64) rsp
  have bx : args[3].get 64 = fr.rdi := congrArg (Value.get 64) outPtr
  have readSlot (k : BitVec 64) (bound : ((0 - k) - (0 - 1192) : BitVec 64).toNat + 8 ≤ 1192) :
      LoadOk mem (fr.rsp - k) 8 :=
    LoadOk.of_offsets writeStack.readable (addr_sub _ _) (addr_sub _ _) bound
  have retOk : LoadOk mem fr.rsp 8 := ⟨retRead.low, retRead.present⟩
  have a40 : fr.rsp - 136 + 96 = fr.rsp - 40 := by bv_omega
  have a32 : fr.rsp - 136 + 104 = fr.rsp - 32 := by bv_omega
  have a24 : fr.rsp - 136 + 112 = fr.rsp - 24 := by bv_omega
  have a16 : fr.rsp - 136 + 120 = fr.rsp - 16 := by bv_omega
  have a8 : fr.rsp - 136 + 128 = fr.rsp - 8 := by bv_omega
  have a0 : fr.rsp - 136 + 136 = fr.rsp := by bv_omega
  have doneSp : fr.rsp - 136 + 144 = fr.rsp + 8 := by bv_omega
  refine ⟨?out, ?exec, ?tag, ?store, ?done_, ?value, ?arguments⟩
  case exec =>
    cfg_eval
    simp only [sp, bx, doneSp, a40, a32, a24, a16, a8, a0, readSlot 40 (by decide), readSlot 32 (by decide), readSlot 24 (by decide), readSlot 16 (by decide), readSlot 8 (by decide), retOk, retVal, retLow, rbx, rbp, r12, r14, r15, and_self, ↓reduceIte]
    rfl
  case tag => rfl
  case store => rfl
  case done_ =>
    simp only [Fn121480.doneAt, Atom.All, Atom.Holds]
    exact ⟨rfl, df, rfl, rfl, rfl, r13, rfl, rfl, mxcsr, ftw, fcw, trivial⟩
  case value => rfl
  case arguments =>
    rintro ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Sec1.Affine
