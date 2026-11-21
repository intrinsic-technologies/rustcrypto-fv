import Sha1.Proofs.Compress.Routine.Finish
import Sha1.Proofs.Streaming.Invariant

namespace Sha1.Proofs.Entry.UpdateFinalize

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine Sha1.Proofs.Streaming.UpdateFinalize

private def restoreEffect : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (addR64Imm32Effect 0x101fb9 4 312)
    (popR64Effect 0x101fc0 1 3))
    (popR64Effect 0x101fc1 2 12))
    (popR64Effect 0x101fc3 2 13))
    (popR64Effect 0x101fc5 2 14))
    (popR64Effect 0x101fc7 2 15))
    (popR64Effect 0x101fc9 1 5)

local macro "restore_pop " step:term ", " stack:term ", " offset:num : tactic => `(tactic| (
  sha1_run_then_manual $step
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of rfl, ?_⟩, popR64Effect_avoids _ _ _ _ _⟩
    have hs : stackPtr t = $stack + $offset := by
      change (Operand.reg 4 : Operand 64).read t = _
      rw [← (hO true).read_reg]
      sha1_norm
      exact congrArg (fun x : BitVec 64 ↦ x + $offset) hP.2.1
    rw [hs]
    exact (memReadable_slice hP.2.2 $offset 8 (by decide)).of_holds hH))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
private theorem restore_block [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) (base : BitVec 64) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x101fb9 ∧ stackPtr s = base ∧ MemReadable s base 368)
      (codeRange 0x101fb9 [0x48,0x81,0xc4,0x38,1,0,0,0x5b,0x41,0x5c,0x41,0x5d,
        0x41,0x5e,0x41,0x5f,0x5d]) restoreEffect := by
  have hBoundary (i : Nat) (hi : i < 18) :
      (0x101fb9 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip := by
    intro he
    exact hout (he ▸ program_text_range 0x1fb9 18 (by decide +kernel) i hi)
  have hAdd : StepEffect (fun s ↦ s.RIP = 0x101fb9)
      (codeRange 0x101fb9 [0x48,0x81,0xc4,0x38,1,0,0]) (addR64Imm32Effect 0x101fb9 4 312) :=
    add_r64_imm32_effect_step 0x101fb9 0x48 0xc4 312 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hPop3 : StepEffect (PopPre 0x101fc0) (codeRange 0x101fc0 [0x5b])
      (popR64Effect 0x101fc0 1 3) := pop_r64_effect_step 0x101fc0 0x5b (by decide) (by decide)
  have hPop12 : StepEffect (PopPre 0x101fc1) (codeRange 0x101fc1 [0x41,0x5c])
      (popR64Effect 0x101fc1 2 12) := pop_r64_rex_effect_step 0x101fc1 0x41 0x5c (by decide) (by decide) (by decide)
  have hPop13 : StepEffect (PopPre 0x101fc3) (codeRange 0x101fc3 [0x41,0x5d])
      (popR64Effect 0x101fc3 2 13) := pop_r64_rex_effect_step 0x101fc3 0x41 0x5d (by decide) (by decide) (by decide)
  have hPop14 : StepEffect (PopPre 0x101fc5) (codeRange 0x101fc5 [0x41,0x5e])
      (popR64Effect 0x101fc5 2 14) := pop_r64_rex_effect_step 0x101fc5 0x41 0x5e (by decide) (by decide) (by decide)
  have hPop15 : StepEffect (PopPre 0x101fc7) (codeRange 0x101fc7 [0x41,0x5f])
      (popR64Effect 0x101fc7 2 15) := pop_r64_rex_effect_step 0x101fc7 0x41 0x5f (by decide) (by decide) (by decide)
  have hPop5 : StepEffect (PopPre 0x101fc9) (codeRange 0x101fc9 [0x5d])
      (popR64Effect 0x101fc9 1 5) := pop_r64_effect_step 0x101fc9 0x5d (by decide) (by decide)
  unfold restoreEffect
  sha1_run_begin hAdd
  restore_pop hPop3, base, 312
  restore_pop hPop12, base, 320
  restore_pop hPop13, base, 328
  restore_pop hPop14, base, 336
  restore_pop hPop15, base, 344
  restore_pop hPop5, base, 352
  intro h
  exact h

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
private theorem restore_values {base : BitVec 64} {s t : RamState}
    (hsp : stackPtr s = base) (he : (restoreEffect s).Holds s t) :
    (∀ i : Fin 6, (Operand.reg (#[3,12,13,14,15,5][i.val]) : Operand 64).read t =
      memLoad s.external (base + BitVec.ofNat 64 (312 + 8 * i.val)) 64) ∧
    stackPtr t = base + 360 ∧ t.RIP = 0x101fca ∧
    AgreesExcept [.reg 3,.reg 4,.reg 5,.reg 12,.reg 13,.reg 14,.reg 15,.flags,.rip] s t := by
  have hfull : ∀ w ∈ (restoreEffect s).writes, w.Full := by
    apply Effect.Local.full
    unfold restoreEffect
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  refine ⟨?_, ?_, he.rip.trans rfl, ?_⟩
  · intro ⟨i,hi⟩
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      change (Operand.reg _ : Operand 64).read t = _
      rw [← ho.read_reg]
      sha1_norm [restoreEffect]
    all_goals
      change memLoad s.external ((Operand.reg 4 : Operand 64).read s + _) 64 = _
      change (Operand.reg 4 : Operand 64).read s = base at hsp
      rw [hsp]
    all_goals rfl
  · change (Operand.reg 4 : Operand 64).read t = _
    rw [← ho.read_reg]
    sha1_norm [restoreEffect]
    change (Operand.reg 4 : Operand 64).read s + 360 = base + 360
    exact congrArg (fun x : BitVec 64 ↦ x + 360) hsp
  · apply he.agrees.mono
    intro c hc
    sha1_norm [restoreEffect] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide +kernel

theorem epilogue [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x101fb9)
    (hm : MemReadable s (stackPtr s) 368) (ho : ¬ InProgram boundary.rip)
    (hslot : stackWord s 360 = boundary.rip) (hsp : stackPtr s + 368 = boundary.rsp)
    (hLow : boundary.rip.toNat < userAddressLimit) :
    ∃ fuel final, Returns boundary fuel s final ∧ ReadyToStep final ∧
      AgreesExcept [.reg 3,.reg 4,.reg 5,.reg 12,.reg 13,.reg 14,.reg 15,.flags,.rip] s final ∧
      ∀ i : Fin 6, (Operand.reg (#[3,12,13,14,15,5][i.val]) : Operand 64).read final =
        stackWord s (312 + 8 * i.val) := by
  obtain ⟨n, t, ha, ht, _, he⟩ := restore_block boundary ho (stackPtr s) s hr
    (program_text_slice hc 0x1fb9 17 (by decide +kernel)) ⟨hip, rfl, hm⟩
  obtain ⟨hv, htsp, htrip, hag⟩ := restore_values rfl he
  have hmem := hag.external (by simp [Component.Covers])
  have htop : stackTop t = boundary.rip := by
    change memLoad t.external (stackPtr t) 64 = _
    rw [hmem, htsp]
    exact hslot
  have hret : RetPre 0x101fca t := by
    refine ⟨⟨htrip, ?_⟩, htop ▸ hLow⟩
    rw [htsp]
    exact (memReadable_slice hm 360 8 (by decide)).of_external_eq hmem
  obtain ⟨final, hstep, hready, hresult⟩ := ret_effect_step 0x101fca t ht
    (program_text_slice (CodeIn.of_external_eq hmem hc) 0x1fca 1 (by decide +kernel)) hret
  have hreturns : Returns boundary 1 t final := by
    apply Returns.of_step hstep (hresult.rip.trans htop)
    have hfinal : stackPtr final = stackPtr t + 8 := hresult.writes
    change stackPtr final = boundary.rsp
    rw [hfinal, htsp, BitVec.add_assoc]
    exact hsp
  refine ⟨n + 1, final, ha.returns hreturns, hready, (hag.trans hresult.agrees).mono (by simp), ?_⟩
  intro i
  have regne : Component.reg (#[3,12,13,14,15,5][i.val]) ∉ [Component.reg 4, .rip] := by
    revert i
    decide
  exact (hresult.agrees.read (n := 64) regne).trans (hv i)

end Sha1.Proofs.Entry.UpdateFinalize
