import Sha1.Proofs.Common.Instructions.MovStore.StackStep
import Sha1.Proofs.Common.Instructions.MemoryWriteFrame
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Call.Triple

namespace Sha1.Proofs.Common.Instructions.MovStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem readyToStep_afterStep_push [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (v nextIP : BitVec 64)
    (htables : ∀ i, i < 8 →
      ¬ Sha1.Spec.Program.InPageTables (pushAddr s + BitVec.ofNat 64 i)) :
    ReadyToStep (afterStep s length fun t ↦ pushState { t with Next_IP := nextIP } v) := by
  apply h.of_agreesExcept (AgreesExcept.afterStep_push s length v nextIP)
  rw [afterStep_push_external]
  exact Sha1.Proofs.Common.Instructions.MemoryWriteFrame.identityPageTableMemory_memStore
    h.memory.tables _ _ htables

theorem readyToStep_afterStep_call [Bindings] {s : RamState} (h : ReadyToStep s)
    (load : Bool) (length : Nat) (nextIP target : BitVec 64)
    (htables : ∀ i, i < 8 →
      ¬ Sha1.Spec.Program.InPageTables (pushAddr s + BitVec.ofNat 64 i)) :
    ReadyToStep (afterStep s length fun t ↦
      callState (callFrom load t nextIP) nextIP target) := by
  apply h.of_agreesExcept (AgreesExcept.afterStep_call s load length nextIP target)
  rw [afterStep_call_external]
  exact Sha1.Proofs.Common.Instructions.MemoryWriteFrame.identityPageTableMemory_memStore
    h.memory.tables _ _ htables

theorem pushEffect_avoids {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (hlen : bytes.length = len) (rip v : RamState → BitVec 64) {s : RamState}
    (h : Sha1.Proofs.Common.Instructions.StorePre.PushPre p len s) : (pushEffect rip v s).Avoids (codeRange p bytes) := by
  subst hlen
  exact Effect.avoids_of_components_reg_mem_rip (pushEffect_components _ v s) h.code

theorem pushEffect_step [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (v : RamState → BitVec 64)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → Sha1.Proofs.Common.Instructions.StorePre.PushPre p len s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        pushState { t with Next_IP := BitVec.add p (BitVec.ofNat 64 len) } (v s)))) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.PushPre p len) (codeRange p bytes)
      (pushEffect (fun _ => p + BitVec.ofNat 64 len) v) := by
  intro s h hcode hpre
  exact ⟨_, hstep s h hcode hpre,
    readyToStep_afterStep_push h _ _ _ hpre.write.tables,
    ⟨afterStep_push_rip h _ _ _, ⟨Operand.read_afterStep_push_rsp _ _ _ _,
      Operand.read_afterStep_push_mem _ _ _ _⟩, trivial,
      (pushEffect_components _ v s).symm ▸ AgreesExcept.afterStep_push _ _ _ _⟩⟩

theorem callEffect_step [Bindings] {pre : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len : Nat} (load : Bool) (target : RamState → BitVec 64)
    (hpush : ∀ s, pre s → Sha1.Proofs.Common.Instructions.StorePre.PushPre p len s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → pre s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        callState (callFrom load t (BitVec.add p (BitVec.ofNat 64 len)))
          (BitVec.add p (BitVec.ofNat 64 len)) (target s)))) :
    StepEffect pre (codeRange p bytes) (callEffect target (p + BitVec.ofNat 64 len)) := by
  intro s h hcode hpre
  have hp := hpush s hpre
  exact ⟨_, hstep s h hcode hpre,
    readyToStep_afterStep_call h load _ _ _ hp.write.tables,
    ⟨afterStep_call_rip _ _ _ _ _, ⟨Operand.read_afterStep_call_rsp _ _ _ _ _,
      Operand.read_afterStep_call_mem _ _ _ _ _⟩, trivial,
      (pushEffect_components _ _ s).symm ▸ AgreesExcept.afterStep_call _ _ _ _ _⟩⟩

theorem push_r64_effect_step [Bindings] (p : BitVec 64) (op : UInt8) (hop : PushOpcode op) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.PushPre p 1) (codeRange p [op])
      (pushR64Effect p 1 (gprNumber 0 0 (opcodeReg op))) := by
  refine pushEffect_step _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  exact push_r64_step s h op hop hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.write

theorem push_r64_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8) (hop : PushOpcode op) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.PushPre p 1) (codeRange p [op])
      (Effect.post (pushR64Effect p 1 (gprNumber 0 0 (opcodeReg op)))) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids rfl _ _ hpre) (push_r64_effect_step p op hop)

theorem push_r64_rex_effect_step [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PushOpcode op) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.PushPre p 2) (codeRange p [rex, op])
      (pushR64Effect p 2 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))) := by
  refine pushEffect_step _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  exact push_r64_rex_step s h rex op hrex hop hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.write

theorem push_r64_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PushOpcode op) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.PushPre p 2) (codeRange p [rex, op])
      (Effect.post (pushR64Effect p 2 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)))) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids rfl _ _ hpre)
    (push_r64_rex_effect_step p rex op hrex hop)

theorem push_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.PushPre p (encodePushR64 src).length) (codeRange p (encodePushR64 src))
      (Effect.post (pushR64Effect p (encodePushR64 src).length (src.setWidth 5))) := by
  rcases encodePushR64_spec src with ⟨op, hbytes, hop, hsrc⟩ |
    ⟨rex, op, hbytes, hrex, hop, hsrc⟩
  · rw [hbytes, ← hsrc]
    exact push_r64_triple_of_bytes p op hop
  · rw [hbytes, ← hsrc]
    exact push_r64_rex_triple_of_bytes p rex op hrex hop

theorem call_rel32_effect_step [Bindings] (p : BitVec 64) (disp : BitVec 32)
    (htarget : (branchTarget p 5 (disp.signExtend 64)).toNat < 2^32) :
    StepEffect (Sha1.Proofs.Common.Instructions.StorePre.PushPre p 5) (codeRange p (encodeCallRel32 disp))
      (callEffect (fun _ => branchTarget p 5 (disp.signExtend 64))
        (p + BitVec.ofNat 64 5)) :=
  callEffect_step false _ (fun _ h => h) fun s h hcode hpre => by
    have hp := hpre.rip
    subst hp
    exact call_rel32_step s h disp hcode.bytesAt (hcode.low (by simp [encodeCallRel32])
      (by simp [encodeCallRel32])) htarget hpre.write

theorem call_rel32_triple [Bindings] (p : BitVec 64) (disp : BitVec 32)
    (htarget : (branchTarget p 5 (disp.signExtend 64)).toNat < 2^32) :
    Triple (Sha1.Proofs.Common.Instructions.StorePre.PushPre p 5) (codeRange p (encodeCallRel32 disp))
      (Effect.post (callEffect (fun _ => branchTarget p 5 (disp.signExtend 64))
        (p + BitVec.ofNat 64 5))) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids (by simp [encodeCallRel32]) _ _ hpre)
    (call_rel32_effect_step p disp htarget)

end Sha1.Proofs.Common.Instructions.MovStore
