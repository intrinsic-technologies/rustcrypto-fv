import P256.Proofs.Sec1.Decode.Frame
import P256.Proofs.Common.Instructions.RepMovsqAny
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxHeartbeats 400000 in
theorem copy [Bindings] {original s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : DecodePre original boundary bytes) (state : Frame original s)
    (rip : s.RIP = 0x10e649) :
    ∃ t fuel, Advances boundary fuel s t ∧ Frame original t ∧ t.RIP = 0x10e659 ∧
      (∀ i < 72, t.external[stackPtr original - 232 + BitVec.ofNat 64 i]? =
        s.external[stackPtr original - 312 + BitVec.ofNat 64 i]?) ∧
      AgreesExcept [.reg 7, .reg 1, .reg 6, .mem (stackPtr original - 232) 72, .rip] s t := by
  obtain ⟨a, aa, ra, ea⟩ :=
    (lea_r64_effect_step 0x10e649 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xe649 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe64e (by decide)))
  have ga : AgreesExcept [.reg 7, .rip] s a := ea.agrees
  have ma := ga.external (by simp [Component.Covers])
  obtain ⟨b, ab, rb, eb⟩ :=
    (mov_r64_r64_effect_step 0x10e64e 0x48 0xe6 (by simp [RexWPrefix]) rfl).advances ra
      (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma) 0xe64e _
        (by decide) (by decide +kernel)) ea.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe651 (by decide)))
  have gb : AgreesExcept [.reg 6, .rip] a b := eb.agrees
  have mb := (ga.trans gb).external (by simp [Component.Covers])
  obtain ⟨c, ac, rc, ec⟩ :=
    (mov_r32_imm32_effect_step 0x10e651 0xb9 (by decide) 9).advances rb
      (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq mb) 0xe651 _
        (by decide) (by decide +kernel)) eb.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe656 (by decide)))
  have gc : AgreesExcept [.reg 1, .rip] b c := ec.agrees
  have setup : AgreesExcept [.reg 7, .reg 1, .reg 6, .rip] s c :=
    ((ga.trans gb).trans gc).mono (by simp)
  have mc := setup.external (by simp [Component.Covers])
  have src : rsi.read c = stackPtr original - 312 :=
    (gc.read (n := 64) (r := 6) (by simp)).trans
      (eb.writes.trans ((ga.read (n := 64) (r := 4) (by simp)).trans state.rsp))
  have dst : rdi.read c = stackPtr original - 232 := by
    have h : rdi.read a = stackPtr s + 80 := ea.writes
    rw [((gb.trans gc).read (n := 64) (r := 7) (by simp)), h]
    exact ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have count : rcx.read c = 9 := ec.writes
  have hn : (rcx.read c).toNat = 9 := by rw [count]; rfl
  have allocated : ∀ a : BitVec 64, (original.external[a]?).isSome → (c.external[a]?).isSome :=
    fun a ha ↦ setup.grow a (state.allocated a ha)
  have readable : MemReadable c (rsi.read c) 72 := by
    rw [src]
    exact readable_of_grow (stack_sub_readable pre.stack
      (offset := 312) (len := 72) (by decide) (by decide)) allocated
  have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable c (rdi.read c) 72 := by
    rw [dst]
    have rd := readable_of_grow (stack_sub_readable pre.stack
      (offset := 232) (len := 72) (by decide) (by decide)) allocated
    refine ⟨rd, ?_⟩
    apply tables_of_not_reserved (by decide) rd.low
    intro i hi reserved
    exact pre.avoids (Stack.region original 3680) (by simp) _
      (ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) ⟨i, hi, rfl⟩)
      (.inr reserved)
  have disjoint : (rsi.read c).toNat + 72 ≤ (rdi.read c).toNat ∨
      (rdi.read c).toNat + 72 ≤ (rsi.read c).toNat := by
    rw [src, dst]
    have hs : (stackPtr original - 312).toNat = (stackPtr original).toNat - 312 :=
      stack_sub_toNat pre.stack (by decide)
    have hd : (stackPtr original - 232).toNat = (stackPtr original).toNat - 232 :=
      stack_sub_toNat pre.stack (by decide)
    rw [hs, hd]
    have bounds := stack_bounds pre.stack
    left
    omega
  have apart : RangeApart (rdi.read c) 72 0x10e656 3 := by
    rw [dst]
    intro i hi j hj he
    apply pre.avoids (Stack.region original 3680) (by simp)
      (stackPtr original - 232 + BitVec.ofNat 64 i)
    · exact ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) ⟨i, hi, rfl⟩
    · left
      rw [he]
      have h := inProgram_of_textOffset (0xe656 + j) (by omega)
      change InProgram (0x10e656 + BitVec.ofNat 64 j)
      change InProgram (0x100000#64 + BitVec.ofNat 64 (0xe656 + j)) at h
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
      exact h
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory ec.rip
    (setup.directionFlagClear (by simp) state.directionFlag).df hn readable writable disjoint apart
  obtain ⟨run, ready, effect, copied⟩ :=
    P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution state.bindingsSupported.stringStride rc
      (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq mc) 0xe656
        [0xf3, 0x48, 0xa5] (by decide) (by decide +kernel)) pc hn
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe656 (by decide)))
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe659 (by decide)))
  simp only [show max 9 1 = 9 from rfl] at run ready effect copied
  generalize ht : nextStates 9 c = t at run ready effect copied
  have frame : AgreesExcept [.reg 6, .reg 7, .reg 1,
      .mem (stackPtr original - 232) 72, .rip] c t := by
    simpa only [repMovsqEffect_components, hn, dst, Nat.reduceMul] using effect.agrees
  have total : AgreesExcept [.reg 7, .reg 1, .reg 6,
      .mem (stackPtr original - 232) 72, .rip] s t := (setup.trans frame).mono (by simp)
  have writes : WritesWithin [.reg 7, .reg 1, .reg 6,
      .mem (stackPtr original - 232) 72, .rip]
      #v[registerRegion original .rdi 80, ScalarFrame.Work.region original 3680 32] := by
    intro component member address covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨ScalarFrame.Work.region original 3680 32, by simp,
      ScalarFrame.Work.contains pre.toCalleePre (by decide) (by decide) covered⟩
  refine ⟨t, 12, ((aa.trans ab).trans ac).trans run,
    state.after_effect pre ready total writes (by simp), effect.rip, ?_, total⟩
  intro i hi
  have h := copied i (by omega)
  simpa only [src, dst, mc] using h

end P256.Proofs.Sec1.Decode.Result
