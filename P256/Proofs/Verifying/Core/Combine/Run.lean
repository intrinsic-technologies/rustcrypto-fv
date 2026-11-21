import P256.Proofs.Verifying.Core.Combine.Setup
import P256.Proofs.Verifying.Core.Combine.FirstScalar
import P256.Proofs.Verifying.Core.Combine.SecondScalar

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open P256.Proofs.Common.Field (AdvanceTriple)

theorem registers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t)
    (off : Nat) (bytes : List UInt8) (effect : RamState → Effect)
    (bound : off+bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom off bytes.length = bytes)
    (block : AdvanceTriple boundary (fun t => t.RIP = Extracted.textAddress+BitVec.ofNat 64 off)
      (codeRange (Extracted.textAddress+BitVec.ofNat 64 off) bytes) (Effect.post effect))
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 off)
    (noMem : ∀ c ∈ (effect t).components, ∀ a, ¬ c.Covers a)
    (noRsp : .reg 4 ∉ (effect t).components)
    (noDf : .df ∉ (effect t).components := by component_not_mem)
    (noMx : .mxcsr ∉ (effect t).components := by component_not_mem)
    (noFc : .fcw ∉ (effect t).components := by component_not_mem) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ (effect t).Holds t u := by
  obtain ⟨n,u,run,ready,_,out⟩ := block t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) off bytes bound code) rip
  exact ⟨n,u,run,state.after_effect pre.toCalleePre (by decide) ready out.agrees
    (fun c hc a ha => (noMem c hc a ha).elim) noRsp noDf noMx noFc,out⟩

theorem first_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dd83) :
    FirstScalar.Pre t := by
  refine ⟨rip,?_,?_,?_⟩
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    exact stack_readable (frameOffset := 1176) pre.toCalleePre state (by decide) (by omega)
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> exact local_writable8 pre state (by decide) (by decide)
  · intro i hi off len h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    exact stack_code (frameOffset := 1176) pre.toCalleePre state (by decide) (by omega) h

theorem second_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10ddd9) :
    SecondScalar.Pre t := by
  refine ⟨rip,?_,?_,?_⟩
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    exact stack_readable (frameOffset := 1176) pre.toCalleePre state (by decide) (by omega)
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> exact local_writable8 pre state (by decide) (by decide)
  · intro i hi off len h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    exact stack_code (frameOffset := 1176) pre.toCalleePre state (by decide) (by omega) h


set_option maxHeartbeats 800000 in
theorem first_scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dd83)
    (input : SecretKeyFromBytes.Scalar.Nat256At t (frameBase s+800) x) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ (FirstScalar.effect t).Holds t u ∧
      SecretKeyFromBytes.Scalar.Nat256At u (frameBase s+672) x := by
  obtain ⟨n,u,run,ready,_,effect⟩ := FirstScalar.block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xdd83 FirstScalar.bytes
      (by decide) (by decide +kernel)) (first_pre pre state rip)
  have st := state.after_effect pre.toCalleePre (by decide) ready effect.agrees (by
    intro c hc a ha
    simp only [FirstScalar.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion s 9992,by simp,local_work_contains pre state (by decide) ha⟩)
    (by simp [FirstScalar.effect,Effect.components])
  refine ⟨n,u,run,st,effect,?_⟩
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_,_,h0,h1,h2,h3⟩
  have sp : rspOf t = frameBase s := state.rsp
  simp only [Write.AllHold,sp] at h0 h1 h2 h3
  change memLoad u.external (frameBase s+672#64) 64 =
    memLoad t.external (frameBase s+800#64) 64 at h0
  change memLoad u.external (frameBase s+680#64) 64 =
    memLoad t.external (frameBase s+808#64) 64 at h1
  change memLoad u.external (frameBase s+688#64) 64 =
    memLoad t.external (frameBase s+816#64) 64 at h2
  change memLoad u.external (frameBase s+696#64) 64 =
    memLoad t.external (frameBase s+824#64) 64 at h3
  apply SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs input.1
  · have h := (stack_readable (frameOffset := 1176) pre.toCalleePre st (offset := 672) (len := 32)
      (by decide) (by decide)).mem
    rw [st.rsp] at h
    exact h
  · intro k hk
    have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases cases with rfl|rfl|rfl|rfl
    · have h := input.memLoad_limb 0 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_zero] at h ⊢
      exact h0.trans h
    · have h := input.memLoad_limb 1 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_assoc,BitVec.reduceAdd] at h ⊢
      exact h1.trans h
    · have h := input.memLoad_limb 2 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_assoc,BitVec.reduceAdd] at h ⊢
      exact h2.trans h
    · have h := input.memLoad_limb 3 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_assoc,BitVec.reduceAdd] at h ⊢
      exact h3.trans h

theorem first_byte {s t u : RamState} {offset len : Nat}
    (rsp : rspOf t = frameBase s) (effect : (FirstScalar.effect t).Holds t u)
    (bound : offset+len ≤ 1176) (apart : offset+len ≤ 672 ∨ 704 ≤ offset)
    {i : Nat} (hi : i < len) :
    u.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc covered
  simp only [FirstScalar.effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  all_goals obtain ⟨j,hj,eq⟩ := covered
  all_goals rw [rsp] at eq
  all_goals bv_omega

set_option maxHeartbeats 800000 in
theorem second_scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10ddd9)
    (input : SecretKeyFromBytes.Scalar.Nat256At t (frameBase s+832) x) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ (SecondScalar.effect t).Holds t u ∧
      SecretKeyFromBytes.Scalar.Nat256At u (frameBase s+96) x := by
  obtain ⟨n,u,run,ready,_,effect⟩ := SecondScalar.block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xddd9 SecondScalar.bytes
      (by decide) (by decide +kernel)) (second_pre pre state rip)
  have st := state.after_effect pre.toCalleePre (by decide) ready effect.agrees (by
    intro c hc a ha
    simp only [SecondScalar.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion s 9992,by simp,local_work_contains pre state (by decide) ha⟩)
    (by simp [SecondScalar.effect,Effect.components])
  refine ⟨n,u,run,st,effect,?_⟩
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_,_,h0,h1,h2,h3⟩
  have sp : rspOf t = frameBase s := state.rsp
  simp only [Write.AllHold,sp] at h0 h1 h2 h3
  change memLoad u.external (frameBase s+96#64) 64 =
    memLoad t.external (frameBase s+832#64) 64 at h0
  change memLoad u.external (frameBase s+104#64) 64 =
    memLoad t.external (frameBase s+840#64) 64 at h1
  change memLoad u.external (frameBase s+112#64) 64 =
    memLoad t.external (frameBase s+848#64) 64 at h2
  change memLoad u.external (frameBase s+120#64) 64 =
    memLoad t.external (frameBase s+856#64) 64 at h3
  apply SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs input.1
  · have h := (stack_readable (frameOffset := 1176) pre.toCalleePre st (offset := 96) (len := 32)
      (by decide) (by decide)).mem
    rw [st.rsp] at h
    exact h
  · intro k hk
    have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases cases with rfl|rfl|rfl|rfl
    · have h := input.memLoad_limb 0 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_zero] at h ⊢
      exact h0.trans h
    · have h := input.memLoad_limb 1 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_assoc,BitVec.reduceAdd] at h ⊢
      exact h1.trans h
    · have h := input.memLoad_limb 2 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_assoc,BitVec.reduceAdd] at h ⊢
      exact h2.trans h
    · have h := input.memLoad_limb 3 (by decide)
      simp only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_assoc,BitVec.reduceAdd] at h ⊢
      exact h3.trans h

theorem second_byte {s t u : RamState} {offset len : Nat}
    (rsp : rspOf t = frameBase s) (effect : (SecondScalar.effect t).Holds t u)
    (bound : offset+len ≤ 1176) (apart : offset+len ≤ 96 ∨ 128 ≤ offset)
    {i : Nat} (hi : i < len) :
    u.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc covered
  simp only [SecondScalar.effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  all_goals obtain ⟨j,hj,eq⟩ := covered
  all_goals rw [rsp] at eq
  all_goals bv_omega

theorem first_memory [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t)
    (effect : (FirstScalar.effect t).Holds t u) :
    MemoryWriteFrame t u (prefixRegions s) := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a ha
  simp only [FirstScalar.effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact ha.elim
  all_goals exact prefix_local_contains pre state (by decide) ha

end P256.Proofs.Verifying.Core.Combine
