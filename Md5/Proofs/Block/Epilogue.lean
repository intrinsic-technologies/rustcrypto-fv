import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Control
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple
import Md5.Proofs.MemoryRoutines.Ranges

namespace Md5.Proofs.Block
open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem popR64Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    Effect.Local (popR64Effect p len dst) := by
  refine ⟨fun _ _ _ ↦ rfl, ?_, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro t t' h
    have hsp : stackPtr t = stackPtr t' := congrArg (fun g ↦ g[gprIndex 4]) h.gpr
    simp only [popR64Effect, hsp, h.read_mem]
  · intro t t' _ i hi
    exact congrArg some hi
  · intro t
    simp [popR64Effect, Write.Full, Operand.Full]

attribute [local x86_local] popR64Effect_local
private theorem stackPtr_read (s : RamState) : stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] popR64Effect addR64Imm32Effect stackPtr_read

private theorem pop_effect [Bindings] (p : BitVec 64) (dst : BitVec 4) (hdst : dst ≠ 4) :
    StepEffect (PopPre p) (codeRange p (encodePopR64 dst))
      (popR64Effect p (encodePopR64 dst).length (dst.setWidth 5)) := by
  have hdst5 : dst.setWidth 5 ≠ 4 := by
    revert dst
    decide +kernel
  rcases encodePopR64_spec dst with ⟨op, hbytes, hop, hsrc⟩ |
    ⟨rex, op, hbytes, hrex, hop, hsrc⟩
  · rw [hbytes, ← hsrc]
    exact pop_r64_effect_step p op hop (hsrc ▸ hdst5)
  · rw [hbytes, ← hsrc]
    exact pop_r64_rex_effect_step p rex op hrex hop (hsrc ▸ hdst5)

structure EpiloguePre (s : RamState) : Prop where
  rip : s.RIP = 0x102447
  read : MemReadable s (stackPtr s + 0x88) 56

def epilogueEffect (s : RamState) : Effect :=
  { rip := 0x102458
    writes := [
      ⟨.reg 3, (Operand.mem (stackPtr s + 136) : Operand 64).read s⟩,
      ⟨.reg 12, (Operand.mem (stackPtr s + 144) : Operand 64).read s⟩,
      ⟨.reg 13, (Operand.mem (stackPtr s + 152) : Operand 64).read s⟩,
      ⟨.reg 14, (Operand.mem (stackPtr s + 160) : Operand 64).read s⟩,
      ⟨.reg 15, (Operand.mem (stackPtr s + 168) : Operand 64).read s⟩,
      ⟨.reg 5, (Operand.mem (stackPtr s + 176) : Operand 64).read s⟩,
      ⟨.reg 4, stackPtr s + 184⟩]
    flags := some (.ofStatusFlags (addSpec (stackPtr s) 136).2) }

private theorem pop_pre_of_holds {s t : RamState} {e : Effect} {p : BitVec 64}
    (h : e.Holds s t) (ho : Obs (e.after s true) t) (hp : e.rip = p)
    (hr : MemReadable s (stackPtr (e.after s true)) 8) : PopPre p t := by
  refine ⟨h.rip_of hp, ?_⟩
  have hsp : stackPtr (e.after s true) = stackPtr t :=
    ho.read (.reg 4 : Operand 64) trivial
  rw [← hsp]
  exact hr.of_holds h

set_option maxHeartbeats 400000 in
theorem compression_epilogue [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    AdvancesBlock boundary EpiloguePre
      (codeRange 0x102447 [0x48, 0x81, 0xc4, 0x88, 0x00, 0x00, 0x00,
        0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]) epilogueEffect := by
  have hAdd : StepEffect (fun s ↦ s.RIP = 0x102447)
      (codeRange 0x102447 [0x48, 0x81, 0xc4, 0x88, 0x00, 0x00, 0x00])
      (addR64Imm32Effect 0x102447 4 136) :=
    add_r64_imm32_effect_step 0x102447 0x48 0xc4 136 (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hPop0 : StepEffect (PopPre (0x102447 + 7)) (codeRange (0x102447 + 7) [0x5b])
      (popR64Effect (0x102447 + 7) 1 3) :=
    pop_effect (0x102447 + 7) 3 (by decide)
  have hPop1 : StepEffect (PopPre (0x102447 + 8)) (codeRange (0x102447 + 8) [0x41, 0x5c])
      (popR64Effect (0x102447 + 8) 2 12) :=
    pop_effect (0x102447 + 8) 12 (by decide)
  have hPop2 : StepEffect (PopPre (0x102447 + 10)) (codeRange (0x102447 + 10) [0x41, 0x5d])
      (popR64Effect (0x102447 + 10) 2 13) :=
    pop_effect (0x102447 + 10) 13 (by decide)
  have hPop3 : StepEffect (PopPre (0x102447 + 12)) (codeRange (0x102447 + 12) [0x41, 0x5e])
      (popR64Effect (0x102447 + 12) 2 14) :=
    pop_effect (0x102447 + 12) 14 (by decide)
  have hPop4 : StepEffect (PopPre (0x102447 + 14)) (codeRange (0x102447 + 14) [0x41, 0x5f])
      (popR64Effect (0x102447 + 14) 2 15) :=
    pop_effect (0x102447 + 14) 15 (by decide)
  have hPop5 : StepEffect (PopPre (0x102447 + 16)) (codeRange (0x102447 + 16) [0x5d])
      (popR64Effect (0x102447 + 16) 1 5) :=
    pop_effect (0x102447 + 16) 5 (by decide)
  md5_run_begin hAdd
  md5_run_then hPop0
  md5_run_then hPop1
  md5_run_then hPop2
  md5_run_then hPop3
  md5_run_then hPop4
  md5_run_then hPop5
  md5_run_finish [epilogueEffect]
  all_goals first
    | (intro t _; dsimp only [popR64Effect, addR64Imm32Effect];
       exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
    | (intro s t hP hH hO
       refine ⟨pop_pre_of_holds hH (hO true) (by x86_norm) ?_, popR64Effect_avoids _ _ _ _ _⟩
       x86_norm
       first
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_zero] using MemoryRoutines.memReadable_slice hP.read 0 8 (by decide +kernel)
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc, BitVec.reduceAdd] using MemoryRoutines.memReadable_slice hP.read 8 8 (by decide +kernel)
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc, BitVec.reduceAdd] using MemoryRoutines.memReadable_slice hP.read 16 8 (by decide +kernel)
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc, BitVec.reduceAdd] using MemoryRoutines.memReadable_slice hP.read 24 8 (by decide +kernel)
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc, BitVec.reduceAdd] using MemoryRoutines.memReadable_slice hP.read 32 8 (by decide +kernel)
         | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc, BitVec.reduceAdd] using MemoryRoutines.memReadable_slice hP.read 40 8 (by decide +kernel))

theorem compression_epilogue_return [Bindings] (boundary : ReturnBoundary) {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hPre : EpiloguePre s) (hOutside : OutsideCompression boundary.rip)
    (hLow : ((Operand.mem (stackPtr s + 184) : Operand 64).read s).toNat < 2^32) :
    ∃ fuel mid final,
      (boundary.rip = (Operand.mem (stackPtr s + 184) : Operand 64).read s ∧
        boundary.rsp = stackPtr s + 192 → Returns boundary fuel s final) ∧
      (boundary.rip ≠ (Operand.mem (stackPtr s + 184) : Operand 64).read s →
        Advances boundary fuel s final) ∧
      ReadyToStep final ∧ CodeIn Extracted.programImage final ∧
      (epilogueEffect s).Holds s mid ∧ (retEffect mid).Holds mid final ∧
      final.RIP = (Operand.mem (stackPtr s + 184) : Operand 64).read s ∧
      stackPtr final = stackPtr s + 192 := by
  have hBytes : CodeIn (codeRange 0x102447
      [0x48, 0x81, 0xc4, 0x88, 0x00, 0x00, 0x00,
        0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]) s :=
    program_text_slice hCode 0x2447 17 (by decide +kernel)
  obtain ⟨fuel, mid, hAdvance, hMidReady, _, hEffect⟩ :=
    compression_epilogue boundary hOutside s hReady hBytes hPre
  have hMidCode := hEffect.codeIn
    (Effect.Avoids.of_noMem (by simp [epilogueEffect, Effect.components, Component.Covers]) _) hCode
  have hMemory := hEffect.agrees.external
    (by simp [epilogueEffect, Effect.components, Component.Covers])
  have hStack : stackPtr mid = stackPtr s + 184 := by
    have hw := hEffect.writes
    simp only [epilogueEffect, Write.AllHold] at hw
    simpa [stackPtr, Operand.read_reg64, gprIndex] using hw.2.2.2.2.2.2
  have hTop : stackTop mid = (Operand.mem (stackPtr s + 184) : Operand 64).read s := by
    simp only [stackTop, hStack, Operand.read, hMemory]
  have hRead : MemReadable mid (stackPtr mid) 8 := by
    rw [hStack]
    apply MemReadable.of_holds hEffect
    simpa [BitVec.add_assoc] using
      MemoryRoutines.memReadable_slice hPre.read 48 8 (by decide +kernel)
  obtain ⟨final, hStep, hFinalReady, hRet⟩ := ret_effect_step 0x102458 mid hMidReady
    (program_text_slice hMidCode 0x2458 1 (by decide +kernel))
    ⟨⟨hEffect.rip, hRead⟩, by rw [hTop]; exact hLow⟩
  have hRip : final.RIP = (Operand.mem (stackPtr s + 184) : Operand 64).read s :=
    hRet.rip.trans hTop
  have hRsp : stackPtr final = stackPtr s + 192 := by
    have hw := hRet.writes
    change stackPtr final = stackPtr mid + 8 at hw
    simpa [hStack, BitVec.add_assoc] using hw
  refine ⟨fuel + 1, mid, final, ?_, ?_, hFinalReady,
    hRet.codeIn (Effect.avoids_of_components_reg_rip (retEffect_components mid) _) hMidCode,
    hEffect, hRet, hRip, hRsp⟩
  · rintro ⟨hRipBoundary, hRspBoundary⟩
    exact hAdvance.returns (Returns.of_step hStep (hRip.trans hRipBoundary.symm)
      (hRsp.trans hRspBoundary.symm))
  · intro hDifferent
    exact hAdvance.trans (Advances.of_step hStep
      (.inl (by rw [hRip]; exact Ne.symm hDifferent)))

theorem epilogueEffect_saved {s t : RamState} (h : (epilogueEffect s).Holds s t)
    (i : Fin 6) :
    (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val]! : Operand 64).read t =
      memLoad s.external (stackPtr s + BitVec.ofNat 64 (136 + 8 * i.val)) 64 := by
  apply Write.allHold_iff.mp h.writes
    ⟨(.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val]! : Operand 64),
      memLoad s.external (stackPtr s + BitVec.ofNat 64 (136 + 8 * i.val)) 64⟩
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
    have := i.isLt
    omega
  rcases hi with hi | hi | hi | hi | hi | hi <;>
    simp [epilogueEffect, hi, Operand.read]

end Md5.Proofs.Block
