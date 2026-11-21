import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy.Packed
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy.Correct
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy.Packed

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open NextNonce (scalarFrame coreFrame)

set_option maxRecDepth 2048 in
theorem writes [Bindings] {s t : RamState} (frame : Frame s t) :
    WordWrites (frameBase s) [1360,1368,1376,1384] (effect t).components := by
  intro c hc a ha
  simp only [effect,ScalarFrame.Copy32.effect,Effect.components,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,Write.component_reg,Write.component_mem,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i,hi,rfl⟩ := ha
  · exact ⟨1360,by simp,i,hi,congrArg (fun b => b+1360+BitVec.ofNat 64 i) frame.rsp⟩
  · refine ⟨1368,by simp,i,hi,?_⟩
    change stackPtr t+1360+8+_ = _
    rw [frame.rsp]
    exact congrArg (fun b : BitVec 64 => b+BitVec.ofNat 64 i)
      (by rw [BitVec.add_assoc]; rfl)
  · refine ⟨1376,by simp,i,hi,?_⟩
    change stackPtr t+1360+16+_ = _
    rw [frame.rsp]
    exact congrArg (fun b : BitVec 64 => b+BitVec.ofNat 64 i)
      (by rw [BitVec.add_assoc]; rfl)
  · refine ⟨1384,by simp,i,hi,?_⟩
    change stackPtr t+1360+24+_ = _
    rw [frame.rsp]
    exact congrArg (fun b : BitVec 64 => b+BitVec.ofNat 64 i)
      (by rw [BitVec.add_assoc]; rfl)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {y : Nat}
    (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d05e)
    (value : Field.MontgomeryAt t (frameBase s+400) y) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10d095 ∧
      Field.MontgomeryAt u (frameBase s+1360) y ∧ (effect t).Holds t u := by
  have src : source t = frameBase s+400 := congrArg (·+400) frame.rsp
  have dst : destination t = frameBase s+1360 := congrArg (·+1360) frame.rsp
  have input := Copy.prepared pre frame rip (sourceOffset := 400) (destinationOffset := 1360)
    (by decide) (by decide) (.inl (by decide)) src dst
  obtain ⟨n,u,run,ready,_,ef⟩ := copy boundary pre.outerBoundary t
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd05e bytes (by decide) (by decide +kernel)) input
  have fu := after_effect pre frame ready ef.agrees (writes frame)
    (by intro off ho; simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega)
    (by simp [effect,ScalarFrame.Copy32.effect,Effect.components])
    (by simp [effect,ScalarFrame.Copy32.effect,Effect.components])
    (by simp [effect,ScalarFrame.Copy32.effect,Effect.components])
    (by simp [effect,ScalarFrame.Copy32.effect,Effect.components])
  refine ⟨n,u,run,fu,ef.rip,?_,ef⟩
  apply Field.montgomeryAt_of_memLoad_limbs value.1 (local_readable pre fu (by decide)).mem
  intro j hj
  apply Eq.trans _ (value.memLoad_limb j hj)
  have values := ef.writes
  simp only [effect,ScalarFrame.Copy32.effect,List.cons_append,List.nil_append,Write.AllHold] at values
  have h0 := values.2.2.1
  have h8 := values.2.2.2.1
  have h16 := values.2.2.2.2.1
  have h24 := values.2.2.2.2.2.1
  change memLoad u.external (destination t) 64 = memLoad t.external (source t) 64 at h0
  change memLoad u.external (destination t+8) 64 = memLoad t.external (source t+8) 64 at h8
  change memLoad u.external (destination t+16) 64 = memLoad t.external (source t+16) 64 at h16
  change memLoad u.external (destination t+24) 64 = memLoad t.external (source t+24) 64 at h24
  rw [dst,src] at h0 h8 h16 h24
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl|rfl|rfl|rfl
  · simpa only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h0
  · exact h8
  · exact h16
  · exact h24

theorem byte [Bindings] {s t u : RamState} {offset : Nat}
    (frame : Frame s t) (ef : (effect t).Holds t u) (bound : offset < 2^64)
    (apart : offset < 1360 ∨ 1392 ≤ offset) :
    u.external[frameBase s+BitVec.ofNat 64 offset]? = t.external[frameBase s+BitVec.ofNat 64 offset]? := by
  apply word_writes_byte (writes frame) ef.agrees bound
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  omega

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy.Packed
