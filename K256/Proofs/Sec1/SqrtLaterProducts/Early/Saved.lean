import K256.Proofs.Sec1.SqrtLaterProducts.Early.Memory
import K256.Proofs.Sec1.SqrtLaterProducts.Early.Three
import K256.Proofs.Sec1.SqrtLaterProducts.Early.Four
import K256.Proofs.Sec1.SqrtLaterProducts.Early.Five
import K256.Proofs.Sec1.SqrtChainExecution.Stages

namespace K256.Proofs.Sec1.SqrtLaterProducts.Early

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution

private def keptOffsets (newSlots : List Word) : List Word :=
  [352,328,304,336,320,240,288,312,256,248,160,168,144] ++ newSlots

private theorem keepSlots {m scratch : Ram} {sp ret : Word} {written kept : List Word}
    (writes : Final.ScratchWrites m scratch sp written) (lo : 8 ≤ sp.toNat)
    (hi : sp.toNat + 432 ≤ 2^32)
    (limits : kept.all (fun k => decide (k.toNat ≤ 440) && written.all
      (fun off => decide (off.toNat ≤ 440 ∧ (k.toNat + 8 ≤ off.toNat ∨ off.toNat + 8 ≤ k.toNat)))) = true)
    (k : Word) (hk : k ∈ kept) :
    memLoad (memStore scratch (sp - 8) ret) (sp + k) 64 = memLoad m (sp + k) 64 := by
  have good := Bool.and_eq_true_iff.mp (List.all_eq_true.mp limits k hk)
  exact retained writes lo hi (of_decide_eq_true good.1)
    (fun off h => of_decide_eq_true (List.all_eq_true.mp good.2 off h))

private theorem valueOfGet {v : Value} {x : Word} (hw : v.width = 64) (h : v.get 64 = x) :
    v = ⟨64,x⟩ := by
  cases v with
  | mk w b =>
    change w = 64 at hw
    subst w
    rw [← h]
    simp only [Value.get, BitVec.setWidth_eq]

private theorem getOfValue {v : Value} {x : Word} (h : v = ⟨64,x⟩) : v.get 64 = x := by
  rw [h]
  exact BitVec.setWidth_eq _

theorem savedThree {code : CodeMap} {args regs : Values Value Reg.count} {sp ret : Word}
    {mem scratch : Ram} {a : Limbs}
    (saved : Atom.All code args mem (savedAtoms 2 sp a))
    (writes : Final.ScratchWrites mem scratch sp offsetsThree)
    (lo : 8 ≤ sp.toNat) (hi : sp.toNat + 432 ≤ 2^32)
    (new1 : memLoad (memStore scratch (sp - 8) ret) (sp + 176) 64 = args[13].get 64)
    (new2 : memLoad (memStore scratch (sp - 8) ret) (sp + 208) 64 = args[15].get 64) :
    Atom.All code regs (memStore scratch (sp - 8) ret) (savedAtoms 3 sp a) := by
  have keep := keepSlots (ret := ret) (kept := keptOffsets []) writes lo hi (by decide +kernel)
  obtain ⟨old352, old328, old304, old336, old320, old240, old288, old312, old256, old248,
    old160, r13, r15, _, old168, _, old144, _⟩ := saved
  exact ⟨(keep 352 (by decide)).trans old352,
    (keep 328 (by decide)).trans old328,
    (keep 304 (by decide)).trans old304,
    (keep 336 (by decide)).trans old336,
    (keep 320 (by decide)).trans old320,
    (keep 240 (by decide)).trans old240,
    (keep 288 (by decide)).trans old288,
    (keep 312 (by decide)).trans old312,
    (keep 256 (by decide)).trans old256,
    (keep 248 (by decide)).trans old248,
    (keep 160 (by decide)).trans old160,
    new1.trans (getOfValue r13),
    new2.trans (getOfValue r15),
    (keep 168 (by decide)).trans old168,
    (keep 144 (by decide)).trans old144, trivial⟩

theorem savedFour {code : CodeMap} {args regs : Values Value Reg.count} {sp ret : Word}
    {mem scratch : Ram} {a : Limbs}
    (saved : Atom.All code args mem (savedAtoms 3 sp a))
    (writes : Final.ScratchWrites mem scratch sp offsetsFour)
    (lo : 8 ≤ sp.toNat) (hi : sp.toNat + 432 ≤ 2^32) :
    Atom.All code regs (memStore scratch (sp - 8) ret) (savedAtoms 4 sp a) := by
  have keep := keepSlots (ret := ret) (kept := keptOffsets [176,208]) writes lo hi (by decide +kernel)
  obtain ⟨old352, old328, old304, old336, old320, old240, old288, old312, old256, old248,
    old160, old176, old208, old168, old144, _⟩ := saved
  exact ⟨(keep 352 (by decide)).trans old352,
    (keep 328 (by decide)).trans old328,
    (keep 304 (by decide)).trans old304,
    (keep 336 (by decide)).trans old336,
    (keep 320 (by decide)).trans old320,
    (keep 240 (by decide)).trans old240,
    (keep 288 (by decide)).trans old288,
    (keep 312 (by decide)).trans old312,
    (keep 256 (by decide)).trans old256,
    (keep 248 (by decide)).trans old248,
    (keep 160 (by decide)).trans old160,
    (keep 176 (by decide)).trans old176,
    (keep 208 (by decide)).trans old208,
    (keep 168 (by decide)).trans old168,
    (keep 144 (by decide)).trans old144, trivial⟩

theorem savedFive {code : CodeMap} {args regs : Values Value Reg.count} {sp ret : Word}
    {mem scratch : Ram} {a : Limbs}
    (saved : Atom.All code args mem (savedAtoms 4 sp a))
    (writes : Final.ScratchWrites mem scratch sp offsetsFive)
    (lo : 8 ≤ sp.toNat) (hi : sp.toNat + 432 ≤ 2^32)
    (widths : ∀ n : Fin Reg.count, n.val ∈ Activation.entryNumbers → regs[n].width = 64)
    (input : WordsAt (memStore scratch (sp - 8) ret) sp 64 (words a 10))
    (aliases : let m := memStore scratch (sp - 8) ret
      memLoad m (sp + 88) 64 = memLoad m sp 64 ∧
      regs[15].get 64 = memLoad m (sp + 8) 64 ∧
      regs[13].get 64 = memLoad m (sp + 16) 64 ∧
      regs[3].get 64 = memLoad m (sp + 24) 64 ∧
      memLoad m (sp + 80) 64 = memLoad m (sp + 32) 64) :
    Atom.All code regs (memStore scratch (sp - 8) ret) (savedAtoms 5 sp a) := by
  have keep := keepSlots (ret := ret) (kept := keptOffsets [176,208]) writes lo hi (by decide +kernel)
  obtain ⟨old352, old328, old304, old336, old320, old240, old288, old312, old256, old248,
    old160, old176, old208, old168, old144, _⟩ := saved
  obtain ⟨a0,a1,a2,a3,a4⟩ := aliases
  have p0 : memLoad (memStore scratch (sp - 8) ret) sp 64 = (words a 10)[0] := by
    have h := input 0 (by decide)
    change memLoad _ (sp + 0) 64 = _ at h
    rwa [show sp + (0 : Word) = sp from BitVec.add_zero sp] at h
  exact ⟨(keep 352 (by decide)).trans old352,
    (keep 328 (by decide)).trans old328,
    (keep 304 (by decide)).trans old304,
    (keep 336 (by decide)).trans old336,
    (keep 320 (by decide)).trans old320,
    (keep 240 (by decide)).trans old240,
    (keep 288 (by decide)).trans old288,
    (keep 312 (by decide)).trans old312,
    (keep 256 (by decide)).trans old256,
    (keep 248 (by decide)).trans old248,
    (keep 160 (by decide)).trans old160,
    (keep 176 (by decide)).trans old176,
    (keep 208 (by decide)).trans old208,
    (keep 168 (by decide)).trans old168,
    (keep 144 (by decide)).trans old144,
    a0.trans p0,
    valueOfGet (widths 15 (by decide)) (a1.trans (input 1 (by decide))),
    valueOfGet (widths 13 (by decide)) (a2.trans (input 2 (by decide))),
    valueOfGet (widths 3 (by decide)) (a3.trans (input 3 (by decide))),
    a4.trans (input 4 (by decide)), trivial⟩

end K256.Proofs.Sec1.SqrtLaterProducts.Early
