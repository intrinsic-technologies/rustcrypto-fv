import Sha2.Proofs.Common.SHA256.Instances.Digest.Finalize
import Sha2.Proofs.Common.SHA256.Instances.Digest.Entry

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions

theorem clone [bindings : Bindings] {initial s : RamState} {data : ByteArray}
    {hash : Array UInt32} {n : Nat} {regions : Vector MemoryRegion n} {p : BitVec 64}
    (stride : UnitStringStride bindings) (state : ExecutionState initial s regions)
    (avoids : ∀ region ∈ regions, region.Avoids InProgram)
    (code : CodeIn (codeRange p [0xf3, 0x48, 0xa5]) s)
    (pre : RepMovsq.RepMovsqPre p s) (count : (rcx.read s).toNat = 13)
    (start : p ≠ (returnBoundary initial).rip)
    (finish : p + 3 ≠ (returnBoundary initial).rip)
    (within : ∀ a, (Component.mem (rdi.read s) 104).Covers a →
      ∃ region ∈ regions, region.Contains a.toNat)
    (hasher : HasherAt s (rsi.read s) data hash) :
    let t := nextStates 13 s
    ExecutionState initial t regions ∧ (repMovsqEffect p s).Holds s t ∧
      HasherAt t (rdi.read s) data hash ∧ rspOf t = rspOf s ∧
      MemoryWriteFrame s t #v[⟨(rdi.read s).toNat, 104⟩] := by
  obtain ⟨run, ready, copy, bytes⟩ := RepMovsq.rep_movsq_execution stride
    (supportedMachine_readyToStep state.machine) code pre count start finish
  have writes : WritesWithin (repMovsqEffect p s).components
      #v[⟨(rdi.read s).toNat, 104⟩] := by
    intro comp hc a ha
    rw [repMovsqEffect_components, count] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨⟨(rdi.read s).toNat, 104⟩, by simp, ?_⟩
    obtain ⟨i, hi, rfl⟩ := ha
    have low := pre.dstLow
    rw [count] at low
    change (rdi.read s).toNat ≤ _ ∧ _ < (rdi.read s).toNat + 104
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨state.of_agrees avoids run ready copy.agrees ?_ (by
    simp only [repMovsqEffect_components]; simp), copy, hasher.of_bytes bytes, ?_,
    copy.agrees.memoryWriteFrame writes⟩
  · intro comp hc a ha
    rw [repMovsqEffect_components, count] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact within a ha
  · exact copy.agrees.read (n := 64) (r := 4) (by simp)

theorem cloned [bindings : Bindings] {initial s : RamState} {data : ByteArray} {v : Wrapper.Variant}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall (routine v) initial data)
    (state : ExecutionState initial s (regions initial v))
    (rip : s.RIP = (Segment.cloneSetup.pc v))
    (rsp : stackPtr s = stackPtr initial - 312)
    (hasher : HasherAt s (rspOf s + 168) data v.initialHash) :
    ∃ c q t, ExecutionState initial t (regions initial v) ∧
      (Blocks.Digest.CloneSetup.effect (Segment.cloneSetup.pc v) s).Holds s c ∧
      (repMovsqEffect (Segment.clone.pc v) c).Holds c q ∧
      (Blocks.Digest.Normalize.effect (Segment.normalize.pc v) q).Holds q t ∧
      Finalize.Prepared (Finalization.digest.layout v) ((Finalization.digest.layout v).sp initial) data t := by
  have outside := (valid_return_boundary machine call.stack call.returnAddress).2.2
  have avoid : (Stack.region initial 784).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    (call.separation.2 _ (by exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).2
  have avoidRegions : ∀ region ∈ regions initial v, region.Avoids InProgram := by
    intro region member a ha h
    have mem : region ∈ [OneShot.outputRegion (routine v) initial,
        Stack.region initial (routine v).minStackBytes] := by
      have stackSize : (routine v).minStackBytes = 784 := rfl
      simpa [regions, stackSize] using member
    exact (call.separation.2 region mem).2 a ha (.inl h)
  have rsp' : rspOf s = stackPtr initial - 312 := rsp
  obtain ⟨fuelC, c, runC, readyC, _, setup⟩ := Blocks.Digest.CloneSetup.run
    (Segment.cloneSetup.pc v) (returnBoundary initial) outside (Segment.inside .cloneSetup (v := v))
    s (supportedMachine_readyToStep state.machine) (Segment.code .cloneSetup state.loaded (v := v)) rip
  have stateC : ExecutionState initial c (regions initial v) :=
    state.of_agrees avoidRegions runC readyC setup.agrees
      (by
        intro comp hc a ha
        have nomem : ∀ comp ∈ (Blocks.Digest.CloneSetup.effect (Segment.cloneSetup.pc v) s).components,
            ∀ a, ¬ comp.Covers a := by
          simp [Blocks.Digest.CloneSetup.effect, Effect.components, Component.Covers]
        exact (nomem comp hc a ha).elim)
      (by simp [Blocks.Digest.CloneSetup.effect, Effect.components])
  have values : rdi.read c = rspOf s ∧ rsi.read c = rspOf s + 168 ∧ rcx.read c = 13 := setup.writes
  have count : (rcx.read c).toNat = 13 := by rw [values.2.2]; decide +kernel
  have source : MemReadable c (rsi.read c) 104 := by
    rw [values.2.1, rsp']
    exact stack_frame_readable call.stack (frame := 312) (offset := 168)
      (by (try dsimp only [routine]); decide +kernel) stateC.allocated (by (try dsimp only [routine]); decide +kernel)
  have target : CrossPageStore.Writable c (rdi.read c) 104 := by
    rw [values.1, rsp']
    apply CrossPageStore.Writable.of_memWritable
    have write := stack_frame_writable call.stack (frame := 312) (offset := 0) (len := 104)
      (by (try dsimp only [routine]); decide +kernel) (fun a ha h => avoid a ha (.inr h)) stateC.allocated (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    simpa [BitVec.ofNat_eq_ofNat] using write
  have apart : RangeApart (rdi.read c) 104 (Segment.clone.pc v) 3 := by
    rw [values.1, rsp']
    have ap := stack_frame_codeApart call.stack (frame := 312) (offset := 0) (len := 104)
      (p := (Segment.clone.pc v)) (size := 3) (by (try dsimp only [routine]); decide +kernel)
      (fun a ha h => avoid a ha (.inl h)) (by (try dsimp only [routine]); decide +kernel)
      (fun j hj => Segment.inside .clone (v := v) j (Nat.le_of_lt hj))
    simpa [BitVec.ofNat_eq_ofNat] using ap
  have disjoint : (rsi.read c).toNat + 104 ≤ (rdi.read c).toNat ∨
      (rdi.read c).toNat + 104 ≤ (rsi.read c).toNat := by
    right
    rw [values.1, values.2.1, rsp']
    change (stackPtr initial - BitVec.ofNat 64 312).toNat + 104 ≤
      (stackPtr initial - BitVec.ofNat 64 312 + BitVec.ofNat 64 168).toNat
    rw [stack_valid_sub_toNat call.stack (offset := 312) (by (try dsimp only [routine]); decide +kernel)]
    rw [stack_frame_toNat call.stack (frame := 312) (offset := 168) (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)]
    omega
  have cloneNext : Segment.cloneSetup.pc v + 16 = Segment.clone.pc v := by
    cases v <;> decide +kernel
  have normalizeNext : Segment.clone.pc v + 3 = Segment.normalize.pc v := by
    cases v <;> decide +kernel
  have pre : RepMovsq.RepMovsqPre (Segment.clone.pc v) c :=
    RepMovsq.pre_of_memory (setup.rip.trans cloneNext) stateC.directionFlag.df count source target disjoint apart
  have chasher : HasherAt c (rsi.read c) data v.initialHash := by
    rw [values.2.1]
    exact hasher.of_bytes (fun i _ => congrArg
      (fun m => m[rspOf s + 168 + BitVec.ofNat 64 i]?)
      (setup.agrees.external (by
        simp [Blocks.Digest.CloneSetup.effect, Effect.components, Component.Covers])))
  obtain ⟨stateQ, copy, qhasher, qrspC, _⟩ := clone stride stateC avoidRegions
    (Segment.code .clone stateC.loaded (v := v)) pre count
    (boundary_ne_program outside (by
      simpa only [BitVec.add_zero] using Segment.inside .clone (v := v) 0 (by change 0 ≤ 3; decide)))
    (boundary_ne_program outside (Segment.inside .clone (v := v) 3 (by change 3 ≤ 3; decide)))
    (by
      intro a ha
      refine ⟨Stack.region initial 784, by simp [regions], ?_⟩
      rw [values.1, rsp'] at ha
      apply stack_frame_contains call.stack (frame := 312) (offset := 0) (len := 104)
        (by dsimp only [routine]; decide +kernel) (by decide +kernel)
      simpa [BitVec.ofNat_eq_ofNat] using ha) chasher
  let q := nextStates 13 c
  have readyQ := supportedMachine_readyToStep stateQ.machine
  have qrsp : rspOf q = rspOf s := qrspC.trans
    (setup.agrees.read (n := 64) (r := 4) (by
      simp [Blocks.Digest.CloneSetup.effect, Effect.components]))
  have qhasher : HasherAt q (rspOf q) data v.initialHash := by
    rw [qrsp]
    simpa only [values.1] using qhasher
  have read (offset len : Nat) (bound : offset + len ≤ 312) :
      MemReadable q (rspOf q + BitVec.ofNat 64 offset) len := by
    rw [qrsp, rsp']
    exact stack_frame_readable call.stack (frame := 312) (by (try dsimp only [routine]); decide +kernel) stateQ.allocated bound
  obtain ⟨fuelT, t, runT, readyT, _, normalize⟩ := Blocks.Digest.Normalize.run
    (Segment.normalize.pc v) (returnBoundary initial) outside (Segment.inside .normalize (v := v))
    q readyQ (Segment.code .normalize stateQ.loaded (v := v))
    ⟨copy.rip.trans normalizeNext, read 63 1 (by (try dsimp only [routine]); decide +kernel), read 96 8 (by (try dsimp only [routine]); decide +kernel)⟩
  have stateT : ExecutionState initial t (regions initial v) :=
    stateQ.of_agrees avoidRegions runT readyT normalize.agrees
      (by
        intro comp hc a ha
        have nomem : ∀ comp ∈ (Blocks.Digest.Normalize.effect (Segment.normalize.pc v) q).components,
            ∀ a, ¬ comp.Covers a := by
          simp [Blocks.Digest.Normalize.effect, Effect.components, Component.Covers]
        exact (nomem comp hc a ha).elim)
      (by simp [Blocks.Digest.Normalize.effect, Effect.components])
  refine ⟨c, q, t, stateT, setup, copy, normalize, ?_⟩
  have prep := normalized (v := v) qhasher normalize
  rw [qrsp, rsp'] at prep
  exact prep

end Sha2.Proofs.Common.SHA256.Instances.Digest
