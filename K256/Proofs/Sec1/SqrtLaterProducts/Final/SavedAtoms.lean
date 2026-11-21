import K256.Proofs.Sec1.SqrtChainExecution.Stages
import K256.Proofs.Sec1.SqrtLaterProducts.Early.Memory
import K256.Proofs.Sec1.SqrtLaterProducts.Final.Ten
import K256.Proofs.Sec1.SqrtLaterProducts.Final.Eleven
import K256.Proofs.Sec1.SqrtLaterProducts.Final.Twelve
import K256.Proofs.Sec1.SqrtLaterProducts.Final.Thirteen

namespace K256.Proofs.Sec1.SqrtLaterProducts.Final

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution

private theorem all_iff_mem {code args mem} (atoms : List Atom) :
    Atom.All code args mem atoms ↔ ∀ x ∈ atoms, x.Holds code args mem := by
  induction atoms with
  | nil => simp [Atom.All]
  | cons a as ih => simp [Atom.All, ih]

private def limbAtom (sp : Word) (a : Limbs) (s : SavedLimb) : Atom :=
  match s.place with
  | .stack k => .mem (sp + BitVec.ofNat 64 k) 64 (savedValue a s)
  | .reg r => .gpr r (savedValue a s)

def offsets (i : Fin 13) : List Word :=
  if i = 9 then offsetsTen else if i = 10 then offsetsEleven
  else if i = 11 then offsetsTwelve else offsetsThirteen

private def retainedLimb (i : Fin 13) (s : SavedLimb) : Bool :=
  (savedLimbs i.castSucc).any (fun t =>
    decide (t.place = s.place ∧ t.product = s.product ∧ t.index = s.index)) &&
    match s.place with
    | .reg _ => false
    | .stack k =>
      let w := BitVec.ofNat 64 k
      decide (w.toNat ≤ 440) && (offsets i).all (fun v =>
        decide (v.toNat ≤ 440 ∧ (w.toNat + 8 ≤ v.toNat ∨ v.toNat + 8 ≤ w.toNat)))

theorem savedAfter {code : CodeMap} {args regs : Values Value Reg.count} {sp ret : Word}
    {mem scratch : Ram} {a : Limbs} {i : Fin 13} (late : 9 ≤ i.val)
    (saved : Atom.All code args mem (savedAtoms i.castSucc sp a))
    (writes : ScratchWrites mem scratch sp (offsets i))
    (lo : 8 ≤ sp.toNat) (hi : sp.toNat + 432 ≤ 2^32)
    (mask : i.val = 12 → regs[12] = ⟨64, 0x1000003d10⟩) :
    Atom.All code regs (memStore scratch (sp - 8) ret) (savedAtoms i.succ sp a) := by
  have cert : ∀ j : Fin 13, 9 ≤ j.val → (savedLimbs j.succ).all (retainedLimb j) = true := by
    decide +kernel
  apply (all_iff_mem _).2
  intro atom member
  change atom ∈ (savedLimbs i.succ).map (limbAtom sp a) ++ _ at member
  rcases List.mem_append.mp member with hm | hm
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
    have hc := List.all_eq_true.mp (cert i late) s hs
    simp only [retainedLimb, Bool.and_eq_true] at hc
    obtain ⟨hmem, hstack⟩ := hc
    obtain ⟨t, ht, hsame⟩ := List.any_eq_true.mp hmem
    obtain ⟨hp, hv, hj⟩ := of_decide_eq_true hsame
    have hts : t = s := by cases t; cases s; congr
    subst t
    have old := (all_iff_mem _).1 saved (limbAtom sp a s)
      (List.mem_append_left _ (List.mem_map.mpr ⟨s, ht, rfl⟩))
    cases hplace : s.place with
    | reg r => simp [hplace] at hstack
    | stack k =>
      simp only [hplace, Bool.and_eq_true, decide_eq_true_eq] at hstack
      simp only [limbAtom, hplace, Atom.Holds] at old ⊢
      exact (Early.retained writes lo hi hstack.1 fun v hv =>
        of_decide_eq_true (List.all_eq_true.mp hstack.2 v hv)).trans old
  · split at hm
    next eq =>
      obtain rfl := List.mem_singleton.mp hm
      exact mask (by change i.val + 1 = 13 at eq; omega)
    next => exact (List.not_mem_nil hm).elim

end K256.Proofs.Sec1.SqrtLaterProducts.Final
