import K256.Proofs.Ecdh.Affine.Inverse.Zero.State
import K256.Proofs.Generate.Generator.Affine.Invert.Parameters
import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Ecdh.Affine.Inverse.Zero

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

open K256.Proofs.Generate.Generator.Affine K256.Proofs.Generate.Generator.Affine.Invert K256.Proofs.Generate.Generator.Affine.Invert.Core

variable {a : Registers} {m : Ram} {sp : Word} {z : Fin modulus} {w : Vector Word 4}

private theorem stackApartRodata (h : ZeroEntry a m sp z w) :
    sp.toNat ≤ 0x200000 ∨ 0x203e50 ≤ (sp - 736).toNat := by
  have stackStart := toNat_sub_ofNat sp 736 h.low
  change (sp - 736).toNat = _ at stackStart
  have spHigh := h.high
  by_cases hlo : sp.toNat ≤ 0x200000
  · exact Or.inl hlo
  right
  apply Classical.byContradiction
  intro hhi
  let p := max 0x200000 (sp - 736).toNat
  have hp : p < 0x203e50 := by dsimp [p]; omega
  have hps : p < sp.toNat := by dsimp [p]; omega
  let addr := BitVec.ofNat 64 p
  have addrNat : addr.toNat = p := by
    change (BitVec.ofNat 64 p).toNat = p
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp only [p]; omega)]
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  have sectionMem : sec ∈ Extracted.programSections := by
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hlo' : sec.address.toNat ≤ addr.toNat := by
    change 0x200000 ≤ addr.toNat
    rw [addrNat]
    exact Nat.le_max_left _ _
  have hhi' : addr.toNat < sec.address.toNat + sec.bytes.size := by
    change addr.toNat < 0x200000 + Extracted.rodataBytes.size
    rw [addrNat, Common.rodataBytes_size]
    exact hp
  obtain ⟨byte, hb⟩ := exists_mem_toCodeMap sectionMem hlo' hhi'
  let i := p - (sp - 736).toNat
  have hi : i < 736 := by dsimp only [i]; omega
  apply h.stack.notCode (addr, byte) hb i hi
  apply BitVec.eq_of_toNat_eq
  change addr.toNat = ((sp - 736) + BitVec.ofNat 64 i).toNat
  rw [addrNat, toNat_add_ofNat _ _ (by dsimp only [i, p]; omega)]
  dsimp only [i, p]
  omega

set_option maxHeartbeats 900000 in
theorem initializeLoop (h : ZeroEntry a m sp z w) :
    ∃ b p, Reaches .l108e30 a m .l1091e4 b p ∧ ZeroLoopState a m sp z 0 b p 0 1 := by
  have rsp := congrArg (Value.get 64) h.rsp
  have rcx := congrArg (Value.get 64) h.rcx
  have rdx := congrArg (Value.get 64) h.rdx
  have rsi := congrArg (Value.get 64) h.rsi
  have rdi := congrArg (Value.get 64) h.rdi
  have r8 := congrArg (Value.get 64) h.r8
  simp only [Value.get_mk_setWidth, BitVec.setWidth_eq] at rsp rcx rdx rsi rdi r8
  have stack := h.stack
  have source := h.source
  have low := h.low
  have high := h.high
  have rodata := stackApartRodata h
  have loadMod (i : Fin 4) := modulus_loaded h.image i
  have loadUnit (i : Fin 4) := unit_loaded h.image i
  have m0 := (loadMod 0).1
  have m1 := (loadMod 1).1
  have m2 := (loadMod 2).1
  have m3 := (loadMod 3).1
  have e0 := (loadUnit 0).1
  have e1 := (loadUnit 1).1
  have e2 := (loadUnit 2).1
  have e3 := (loadUnit 3).1
  change Readable m 0x2021e0 8 at m0
  change Readable m 0x2021e8 8 at m1
  change Readable m 0x2021f0 8 at m2
  change Readable m 0x2021f8 8 at m3
  change Readable m 0x202180 8 at e0
  change Readable m 0x202188 8 at e1
  change Readable m 0x202190 8 at e2
  change Readable m 0x202198 8 at e3
  have f0 := (loadMod 0).2
  have f1 := (loadMod 1).2
  have f2 := (loadMod 2).2
  have f3 := (loadMod 3).2
  have u0 := (loadUnit 0).2
  have u1 := (loadUnit 1).2
  have u2 := (loadUnit 2).2
  have u3 := (loadUnit 3).2
  have g0 := h.words 0 (by decide)
  have g1 := h.words 1 (by decide)
  have g2 := h.words 2 (by decide)
  have g3 := h.words 3 (by decide)
  change memLoad m 0x2021e0 64 = _ at f0
  change memLoad m 0x2021e8 64 = _ at f1
  change memLoad m 0x2021f0 64 = _ at f2
  change memLoad m 0x2021f8 64 = _ at f3
  change memLoad m 0x202180 64 = _ at u0
  change memLoad m 0x202188 64 = _ at u1
  change memLoad m 0x202190 64 = _ at u2
  change memLoad m 0x202198 64 = _ at u3
  simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, Lift.reduceAddOffset] at g0 g1 g2 g3
  refine ⟨?b, ?p, ?reach, ?state⟩
  case reach =>
    have run : program.runBlock (dialect Extracted.programImage) ⟨.l108e30, a, m⟩ =
        .jump ⟨.l1091e4, ?b, ?p⟩ := by
      cfg_eval [rsp, rcx, rdx, rsi, rdi, r8, Lift.reduceAddOffset, Lift.reduceSubOffset,
        Lift.reduceAddNeg, Lift.reduceSubNeg, BitVec.reduceAdd, BitVec.reduceSub]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l108e30)
      rfl
    refine .step (b := ⟨⟨.l1091e4, _, _⟩, []⟩) ?_ (Star.refl _)
    simp only [Program.sem, Program.step, run, Transfer.next]
  case state =>
    refine ⟨rfl, rfl, rfl, ?scratch, ?kept, ?saved, ?frame,
      ⟨modulusWords, false, ?fWords, ?fSign, congrArg Int.ofNat modulus_value.symm⟩,
      ⟨w, false, ?gWords, ?gSign, congrArg Int.ofNat h.input.symm⟩,
      ⟨#v[0, 0, 0, 0], false, ?dWords, ?dSign, by decide +kernel⟩,
      ⟨unitWords, false, ?eWords, ?eSign, congrArg Int.ofNat unit_value.symm⟩,
      ?dBound, ?eBound, ?dInvariant, ?eInvariant, ?originalZero, ?outputPtr, ?modulusPtr,
      ?modulusInverse⟩
    case scratch =>
      apply congrArg (Value.mk 64)
      change sp - 392 = sp - 408 + 16
      bv_omega
    case kept =>
      intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> rfl
    case saved =>
      intro ⟨i, hi⟩ off hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals (refine_norm []; rfl)
    case frame => slot_state region
    case fWords | gWords | dWords | eWords =>
      intro i hi
      have hp : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hp with rfl | rfl | rfl | rfl
      all_goals
        refine_norm [base, wordAddr, Nat.reduceMul, f0, f1, f2, f3, g0, g1, g2, g3, u0, u1, u2, u3] <;> rfl
    case fSign | gSign | dSign | eSign =>
      refine_norm [base]
      rfl
    case dBound => decide +kernel
    case eBound => decide +kernel
    case dInvariant =>
      change (0 * (z.val : Int)) % modulus = (modulus : Int) % modulus
      simp only [Int.zero_mul, Int.zero_emod, Int.emod_self]
    case eInvariant =>
      change (1 * (z.val : Int)) % modulus = (z.val : Int) % modulus
      exact congrArg (· % (modulus : Int)) (Int.one_mul _)
    case originalZero =>
      refine_norm [base, g0, g1, g2, g3]
      have hz := h.input.trans h.zero
      unfold value at hz
      apply BitVec.or_eq_zero_iff.mpr
      refine ⟨BitVec.or_eq_zero_iff.mpr ⟨BitVec.or_eq_zero_iff.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
      all_goals apply BitVec.eq_of_toNat_eq; change _ = 0; omega
    case outputPtr => refine_norm [base] <;> rfl
    case modulusPtr => refine_norm [base] <;> rfl
    case modulusInverse => refine_norm [base] <;> rfl

end K256.Proofs.Ecdh.Affine.Inverse.Zero
