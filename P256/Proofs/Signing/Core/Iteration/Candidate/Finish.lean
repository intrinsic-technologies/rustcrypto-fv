import P256.Proofs.Signing.Core.Iteration.Candidate.Select
import P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Setup
import P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Compare
import P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Invert
import P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Copy
import P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Combine
import P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Branch
import P256.Proofs.Signing.Core.Iteration.Choice

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)
open NextNonce (arguments_copy)
open Finish
open ScalarFrame (choiceClobbers)

structure Validated [Bindings] (s t : RamState) (state : Nonce.State) (nonce : Nat) : Prop where
  frame : Frame s t
  arguments : StoredArguments s t
  generator : Nonce.GeneratorAt t (frameBase s + 2160) (frameBase s + 272) state
  scalar : Nat256At t (frameBase s + 8) nonce
  positive : 0 < nonce
  canonical : nonce < Operations.domain.n
  rbp : t.regValue .rbp = frameBase s + 528
  rbx : t.regValue .rbx = frameBase s + 40
  r13 : t.regValue .r13 = frameBase s + 432
  r14 : t.regValue .r14 = frameBase s + 2160
  r15 : t.regValue .r15 = frameBase s + 1328

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {state : Nonce.State} {nonce : Nat} (pre : SignPre s boundary)
    (input : Selected s t state nonce) (rip : t.RIP = 0x10cb5f) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10cbed ∧ Validated s u state nonce := by
  obtain ⟨n, a, runA, frameA, effectA⟩ := Finish.Setup.run pre input.frame rip
  have preserveA (i : Nat) (bound : i < 2280) (apart : i < 1328 ∨ 1360 ≤ i) :
      a.external[frameBase s + BitVec.ofNat 64 i]? =
        t.external[frameBase s + BitVec.ofNat 64 i]? := by
    apply word_writes_byte (Finish.Setup.writes input.frame) effectA.agrees (by omega)
    intro off ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    constructor <;> omega
  have scalarA : Nat256At a (frameBase s + 432) nonce := by
    refine ⟨input.scalar.1, fun i hi => ?_⟩
    have h := preserveA (432+i) (by omega) (.inl (by omega))
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h.trans (input.scalar.2 i hi)
  have diA : a.regValue .rdi = frameBase s + 432 := effectA.writes.2.2.2.2.1.trans input.r13
  have siA : a.regValue .rsi = frameBase s + 1328 := effectA.writes.2.2.2.2.2.trans input.r15
  obtain ⟨m, b, runB, frameB, ripB, flagB, bytesB, regsB⟩ :=
    compare pre frameA effectA.rip diA siA scalarA (Finish.Setup.zero pre input.frame frameA effectA)
  rw [ite_eq_right (Nat.ne_of_gt input.positive)] at flagB
  obtain ⟨c, runC, frameC, ripC, diC, agreesC⟩ := invert_choice pre frameB ripB flagB
  have memoryC := agreesC.external (by simp [Component.Covers])
  obtain ⟨d, runD, frameD, ripD, flagD, agreesD⟩ := choice_call pre frameC 0xcba1 0xc4ca
    (by decide) (by decide +kernel) (by decide +kernel) ripC
  have scalarD : Nat256At d (frameBase s + 432) nonce := by
    refine ⟨scalarA.1, fun i hi => ?_⟩
    have h := scalarA.2 i hi
    have addr : frameBase s + 432 + BitVec.ofNat 64 i = frameBase s + BitVec.ofNat 64 (432+i) := by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
    rw [addr] at h ⊢
    rw [choice_byte agreesD (by omega), memoryC, bytesB _ (by omega)]
    exact h
  obtain ⟨k, e, runE, frameE, effectE⟩ := Finish.Copy.run pre frameD ripD
  have scalarE : Nat256At e (frameBase s + 8) nonce :=
    ⟨scalarD.1, fun i hi =>
      (Finish.Copy.copied pre frameD frameE effectE i hi).trans (scalarD.2 i hi)⟩
  have agreesBE := (agreesC.trans agreesD).trans effectE.agrees
  have alE : (e.regValue .rax).setWidth 8 = 1 := by
    have ax : e.regValue .rax = d.regValue .rax :=
      effectE.agrees.read (n := 64) (r := 0) (by simp [Finish.Copy.Block.effect, Effect.components])
    rw [ax, flagD, diC]
    rfl
  have r12E : (e.regValue .r12).setWidth 8 = 1 := by
    have reg : e.regValue .r12 = t.regValue .r12 :=
      (agreesBE.read (n := 64) (r := 12) (by
        simp [Finish.Copy.Block.effect, Effect.components, choiceClobbers])).trans
        ((regsB .r12 (by simp)).trans (effectA.agrees.read (n := 64) (r := 12)
          (by simp [Finish.Setup.Block.effect, Effect.components])))
    rw [reg]
    exact input.flag
  obtain ⟨f, runF, frameF, ripF, diF, agreesF⟩ := combine pre frameE effectE.rip alE r12E
  have memoryF := agreesF.external (by simp [Component.Covers])
  obtain ⟨g, runG, frameG, ripG, flagG, agreesG⟩ := choice_call pre frameF 0xcbe0 0xc48b
    (by decide) (by decide +kernel) (by decide +kernel) ripF
  have status : (Operand.reg 0 : Operand 8).read g = 1 := by
    change (g.regValue .rax).setWidth 8 = 1
    rw [flagG, diF]
    rfl
  obtain ⟨u, runU, readyU, ripU, agreesU⟩ := accept
    (readyToStep frameG.machine frameG.bindingsSupported) frameG.loaded ripG status pre.outerBoundary
  have frameU := after_registers frameG readyU agreesU
    (by simp [Component.Covers]) (by simp) (by simp) (by simp) (by simp)
  have memoryU := agreesU.external (by simp [Component.Covers])
  have bytesE (i : Nat) (bound : i < 2280) (apart : i < 8 ∨ 40 ≤ i) :
      e.external[frameBase s + BitVec.ofNat 64 i]? =
        d.external[frameBase s + BitVec.ofNat 64 i]? := by
    apply word_writes_byte (Finish.Copy.writes frameD) effectE.agrees (by omega)
    intro off ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    constructor <;> omega
  have bytesU (i : Nat) (lo : 40 ≤ i) (hi : i < 2280) (apart : i < 1328 ∨ 1360 ≤ i) :
      u.external[frameBase s + BitVec.ofNat 64 i]? =
        t.external[frameBase s + BitVec.ofNat 64 i]? := by
    rw [memoryU, choice_byte agreesG hi, memoryF, bytesE i hi (.inr lo),
      choice_byte agreesD hi, memoryC, bytesB i hi, preserveA i hi apart]
  have scalarU : Nat256At u (frameBase s + 8) nonce := by
    refine ⟨scalarE.1, fun i hi => ?_⟩
    have h := scalarE.2 i hi
    have addr : frameBase s + 8 + BitVec.ofNat 64 i = frameBase s + BitVec.ofNat 64 (8+i) := by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
    rw [addr] at h ⊢
    rw [memoryU, choice_byte agreesG (by omega), memoryF]
    exact h
  have args := arguments_copy input.arguments (fun i range => bytesU i (by omega) (by omega) (.inl (by omega)))
  have genBytes (offset len : Nat) (lo : 40 ≤ offset) (hi : offset+len ≤ 2280)
      (apart : offset+len ≤ 1328 ∨ 1360 ≤ offset) :
      ∀ i < len, u.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hin
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact bytesU _ (by omega) (by omega) (by omega)
  have generator := input.generator.copy
    (genBytes 2160 72 (by decide) (by decide) (.inr (by decide)))
    ⟨input.generator.2.1.1, fun i hi =>
      (genBytes 272 32 (by decide) (by decide) (.inl (by decide)) i hi).trans
        (input.generator.2.1.2 i hi)⟩
  have agreesBU := ((agreesBE.trans agreesF).trans agreesG).trans agreesU
  have regsU (reg : Syntax.Reg) (member : reg ∈ [.rbx, .rbp, .r13, .r14, .r15]) :
      u.regValue reg = t.regValue reg := by
    refine Eq.trans ?_ ((regsB reg (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp)).trans ?_)
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
    · exact agreesBU.read (n := 64) (r := 3) (by simp [Finish.Copy.Block.effect, Effect.components, choiceClobbers])
    · exact agreesBU.read (n := 64) (r := 5) (by simp [Finish.Copy.Block.effect, Effect.components, choiceClobbers])
    · exact agreesBU.read (n := 64) (r := 13) (by simp [Finish.Copy.Block.effect, Effect.components, choiceClobbers])
    · exact agreesBU.read (n := 64) (r := 14) (by simp [Finish.Copy.Block.effect, Effect.components, choiceClobbers])
    · exact agreesBU.read (n := 64) (r := 15) (by simp [Finish.Copy.Block.effect, Effect.components, choiceClobbers])
    · exact effectA.agrees.read (n := 64) (r := 3) (by simp [Finish.Setup.Block.effect, Effect.components])
    · exact effectA.agrees.read (n := 64) (r := 5) (by simp [Finish.Setup.Block.effect, Effect.components])
    · exact effectA.agrees.read (n := 64) (r := 13) (by simp [Finish.Setup.Block.effect, Effect.components])
    · exact effectA.agrees.read (n := 64) (r := 14) (by simp [Finish.Setup.Block.effect, Effect.components])
    · exact effectA.agrees.read (n := 64) (r := 15) (by simp [Finish.Setup.Block.effect, Effect.components])
  refine ⟨n+m+3+6+k+2+6+2, u,
    ((((((runA.trans runB).trans runC).trans runD).trans runE).trans runF).trans runG).trans runU,
    ripU, ⟨frameU, args, generator, scalarU, input.positive, input.canonical,
      (regsU .rbp (by simp)).trans input.rbp,
      (regsU .rbx (by simp)).trans input.rbx,
      (regsU .r13 (by simp)).trans input.r13,
      (regsU .r14 (by simp)).trans input.r14,
      (regsU .r15 (by simp)).trans input.r15⟩⟩

end P256.Proofs.Signing.Core.Iteration.Candidate
