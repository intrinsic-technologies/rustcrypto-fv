import P256.Proofs.Sec1Serialize.Prologue
import P256.Proofs.Sec1Serialize.State
import P256.Proofs.Common.Encoding.Serialize.Store32
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open P256.Proofs.Common.Instructions (mov_m32_r32_no_rex_effect_step)

theorem save_compression_mode [Bindings] {s t : RamState} {boundary : ReturnBoundary} {mode : BitVec 64}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (state : FrameState s t 65 328 312) (rip : t.RIP = 0x110d81)
    (rdx : t.regValue .rdx = mode) :
    ∃ u, Advances boundary 1 t u ∧ FrameState s u 65 328 312 ∧
      u.RIP = 0x110d85 ∧ (Operand.mem (stackPtr s - 300) : Operand 32).read u = mode.setWidth 32 ∧
      AgreesExcept [.mem (stackPtr s - 300) 4, .rip] t u := by
  let am : AddrMode := .sib 4 none 0 (.d8 12)
  have address : storeAddrAt 0x110d81 am (2 + am.tail.length) t = stackPtr s - 300 := by
    change stackPtr t + 12 = stackPtr s - 300
    exact scalar_stack_address (frameOffset := 312) state.rsp (by decide) (by decide)
  have writable : MemWritable t (stackPtr s - 300) 4 := by
    apply writable_of_grow (s := s) _ state.allocated
    apply stack_sub_writable pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
      (offset := 300) (by decide) (by decide) (by decide)
    rw [stack_sub_toNat pre.stack (offset := 300) (by decide)]
    have hs : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
    have hn := (stack_bounds pre.stack).1
    have ha : ((stackPtr s).toNat - 300) % 4 = 0 := by omega
    have hm := Nat.mod_mod_of_dvd ((stackPtr s).toNat - 300) (show 4 ∣ 4096 by decide)
    omega
  have apart : RangeApart (stackPtr s - 300) 4 0x110d81 4 := by
    have h := stack_code pre state (offset := 12) (len := 4)
      (codeOffset := 0x10d81) (codeLen := 4) (by decide) (by decide) (by decide)
    rw [scalar_stack_address (frameOffset := 312) state.rsp (by decide) (by decide)] at h
    exact h
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_m32_r32_no_rex_effect_step 0x110d81 2 am (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x10d81 _
        (by decide) (by decide +kernel))
      ⟨rip, address ▸ writable, address ▸ apart⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10d85 (by decide)))
  have frame : AgreesExcept [.mem (stackPtr s - 300) 4, .rip] t u := by
    have h := effect.agrees
    rw [storeEffect_components, address] at h
    exact h
  have writes : WritesWithin [.mem (stackPtr s - 300) 4, .rip]
      #v[registerRegion s .rdi 65, workRegion s 328] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨workRegion s 328, by simp, work_contains pre (by decide) (by decide) ha⟩
    · exact ha.elim
  refine ⟨u, run, state.after_effect pre (by decide) ready frame writes (by simp),
    effect.rip, ?_, frame⟩
  have h := effect.writes
  change (Operand.mem (storeAddrAt 0x110d81 am (2 + am.tail.length) t) : Operand 32).read u =
    (t.regValue .rdx).setWidth 32 at h
  rw [address, rdx] at h
  exact h

theorem save_compressionFlag [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (state : FrameState s t 65 328 312) (rip : t.RIP = 0x110d81)
    (rdx : t.regValue .rdx = 0) :
    ∃ u, Advances boundary 1 t u ∧ FrameState s u 65 328 312 ∧
      u.RIP = 0x110d85 ∧ compressionFlag s u ∧
      AgreesExcept [.mem (stackPtr s - 300) 4, .rip] t u :=
  save_compression_mode pre state rip rdx

theorem entry_mode [Bindings] {s : RamState} {boundary : ReturnBoundary} {mode : BitVec 64}
    (pre : CalleePre s boundary 0x110d70 72 65 328) (rdx : s.regValue .rdx = mode) :
    ∃ t, Advances boundary 9 s t ∧ FrameState s t 65 328 312 ∧
      t.RIP = 0x110d88 ∧ t.regValue .rsi = s.regValue .rsi ∧
      t.regValue .r14 = s.regValue .rsi ∧ t.regValue .rdi = s.regValue .rdi ∧
      (Operand.mem (stackPtr s - 300) : Operand 32).read t = mode.setWidth 32 := by
  obtain ⟨a, runA, stateA, ripA, _, frameA⟩ := frame_entry pre
  have rdxA : a.regValue .rdx = mode :=
    (frameA.read (n := 64) (r := 2) (by simp [saveFrame])).trans rdx
  obtain ⟨b, runB, stateB, ripB, flagB, frameB⟩ := save_compression_mode pre stateA ripA rdxA
  obtain ⟨t, run, ready, effect⟩ :=
    (mov_r64_r64_effect_step 0x110d85 0x49 0xf6
      (by simp [RexWPrefix]) (by decide)).advances
      (readyToStep stateB.machine stateB.bindingsSupported)
      (programText_slice (programLoaded_codeIn stateB.loaded) 0x10d85 _
        (by decide) (by decide +kernel)) ripB
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10d88 (by decide)))
  have frame : AgreesExcept [.reg 14, .rip] b t := effect.agrees
  have memory := frame.external (by simp [Component.Covers])
  have rsiB : b.regValue .rsi = s.regValue .rsi :=
    ((frameA.trans frameB).read (n := 64) (r := 6) (by simp [saveFrame]))
  have rdiB : b.regValue .rdi = s.regValue .rdi :=
    ((frameA.trans frameB).read (n := 64) (r := 7) (by simp [saveFrame]))
  refine ⟨t, (runA.trans runB).trans run,
    stateB.after_registers ready frame (by simp [Component.Covers]) (by simp), effect.rip,
    (frame.read (n := 64) (r := 6) (by simp)).trans rsiB,
    effect.writes.trans rsiB, (frame.read (n := 64) (r := 7) (by simp)).trans rdiB, ?_⟩
  change memLoad t.external _ 32 = mode.setWidth 32
  rw [memory]
  exact flagB

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328) (rdx : s.regValue .rdx = 0) :
    ∃ t, Advances boundary 9 s t ∧ FrameState s t 65 328 312 ∧
      t.RIP = 0x110d88 ∧ t.regValue .rsi = s.regValue .rsi ∧
      t.regValue .r14 = s.regValue .rsi ∧ t.regValue .rdi = s.regValue .rdi ∧
      compressionFlag s t :=
  entry_mode pre rdx

end P256.Proofs.Sec1Serialize
