import P256.Proofs.Verifying.Core.Digest.Finish.CopyBlock
import P256.Proofs.Verifying.Core.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

theorem copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Core.Pre s boundary) (state : Frame s t) (offset : Nat)
    (bound : offset+51 ≤ 118431)
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 offset) :
    CopyBlock.Pre (Extracted.textAddress+BitVec.ofNat 64 offset) t := by
  refine ⟨rip,?_,?_,?_⟩
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    exact stack_readable (frameOffset := 1176) hp.toCalleePre state (by decide) (by omega)
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals exact local_writable8 hp state (by decide) (by decide)
  · intro i hi codeOffset len hl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact stack_code (frameOffset := 1176) hp.toCalleePre state
      (by decide) (by omega) (by omega)

theorem copy_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary} {p : BitVec 64}
    (hp : Core.Pre s boundary) (state : Frame s t) :
    WritesWithin (CopyBlock.effect p t).components #v[workRegion s 9992] := by
  intro c hc a covered
  simp only [CopyBlock.effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  all_goals exact ⟨_,by simp,local_work_contains hp state (by decide) covered⟩

theorem copy_slot {s t u : RamState} {p : BitVec 64} {offset x : Nat}
    (rsp : rspOf t = frameBase s) (effect : (CopyBlock.effect p t).Holds t u)
    (lo : 160 ≤ offset) (hi : offset+32 ≤ 1128)
    (value : Nat256At t (frameBase s+BitVec.ofNat 64 offset) x) :
    Nat256At u (frameBase s+BitVec.ofNat 64 offset) x := by
  refine ⟨value.1,fun i hi' => ?_⟩
  rw [effect.agrees.byte]
  · exact value.2 i hi'
  · intro c hc covered
    simp only [CopyBlock.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j,hj,eq⟩ := covered
    all_goals rw [rsp] at eq
    all_goals bv_omega

set_option maxHeartbeats 800000 in
theorem copy [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (hp : Core.Pre s boundary) (state : Frame s t)
    (offset : Nat) (bound : offset+51 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 51 = CopyBlock.bytes)
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 offset)
    (input : Nat256At t (frameBase s) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (CopyBlock.effect (Extracted.textAddress+BitVec.ofNat 64 offset) t).Holds t u ∧
      Nat256At u (frameBase s+128#64) x ∧ MemoryWriteFrame t u #v[Stack.region s 9992] := by
  obtain ⟨n,u,run,ready,_,effect⟩ := CopyBlock.block
    (Extracted.textAddress+BitVec.ofNat 64 offset) boundary
    (fun i hi => by
      rw [BitVec.add_assoc,← BitVec.ofNat_add]
      exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset _ (by omega)))
    t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset CopyBlock.bytes
      (by simpa only [CopyBlock.bytes,List.length_cons,List.length_nil] using Nat.le_of_lt bound)
      bytes) (copy_pre hp state offset (Nat.le_of_lt bound) rip)
  have st := state.after_effect hp.toCalleePre (by decide) ready effect.agrees (by
    intro c hc a ha
    obtain ⟨region,hr,hin⟩ := copy_writes hp state c hc a ha
    exact ⟨region,by simpa using Or.inr hr,hin⟩)
    (by simp [CopyBlock.effect,Effect.components])
  refine ⟨n,u,run,st,effect,?_,
    work_memory_stack hp (effect.agrees.memoryWriteFrame (copy_writes hp state))⟩
  have sp : rspOf t = frameBase s := state.rsp
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_,_,h0,h1,h2,h3⟩
  simp only [Write.AllHold,sp] at h0 h1 h2 h3
  change memLoad u.external (frameBase s+128#64) 64 =
    memLoad t.external (frameBase s+0#64) 64 at h0
  change memLoad u.external (frameBase s+136#64) 64 =
    memLoad t.external (frameBase s+8#64) 64 at h1
  change memLoad u.external (frameBase s+144#64) 64 =
    memLoad t.external (frameBase s+16#64) 64 at h2
  change memLoad u.external (frameBase s+152#64) 64 =
    memLoad t.external (frameBase s+24#64) 64 at h3
  rw [BitVec.add_zero] at h0
  apply nat256At_of_memLoad_limbs input.1
  · have h := (stack_readable hp.toCalleePre st (offset := 128) (len := 32)
      (by decide) (by decide)).mem
    rw [st.rsp] at h
    exact h
  · intro k hk
    have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases cases with rfl|rfl|rfl|rfl
    · simpa only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_zero] using
        h0.trans (by simpa only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_zero]
          using input.memLoad_limb 0 (by decide))
    · simpa only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_assoc,BitVec.reduceAdd]
        using h1.trans (input.memLoad_limb 1 (by decide))
    · simpa only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_assoc,BitVec.reduceAdd]
        using h2.trans (input.memLoad_limb 2 (by decide))
    · simpa only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_assoc,BitVec.reduceAdd]
        using h3.trans (input.memLoad_limb 3 (by decide))

end P256.Proofs.Verifying.Core.Digest.Finish
