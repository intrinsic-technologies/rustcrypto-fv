import P256.Proofs.Verifying.Combination.Preparation.Naf.FirstScalar
import P256.Proofs.Verifying.Combination.Preparation.Tables
import P256.Proofs.Verifying.Combination.Input
import P256.Proofs.Program.CalleeStackInput

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem reload_input [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x106646) :
    ∃ a, Advances boundary 1 t a ∧ State s a ∧ a.RIP = 0x10664b ∧
      a.regValue .rsi = memLoad t.external (stackPtr s - 6544) 64 ∧
      AgreesExcept [.reg 6, .rip] t a := by
  have addr : (AddrMode.sib 4 none 0 (.d8 8)).addr t 0x10664b = stackPtr s - 6544 :=
    scalar_stack_address state.rsp (offset := 8) (by decide) (by decide)
  have readable : MemReadable t (stackPtr s - 6544) 8 :=
    readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) state.allocated
  obtain ⟨a, run, ready, effect⟩ :=
    (mov_r64_m64_effect_step 0x106646 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x6646 _
        (by decide) (by decide +kernel)) ⟨rip, addr ▸ readable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x664b (by decide)))
  have agrees : AgreesExcept [.reg 6, .rip] t a := effect.agrees
  refine ⟨a, run, state.after_registers ready agrees (by simp [Component.Covers])
    (by simp), effect.rip, ?_, agrees⟩
  have h := effect.writes
  change a.regValue .rsi = memLoad t.external
    ((AddrMode.sib 4 none 0 (.d8 8)).addr t 0x10664b) 64 at h
  rwa [addr] at h

structure ScalarInput [Bindings] (s t : RamState) (p q : Projective) (u v : Nat) : Prop
    extends FrameState s t 96 8808 6552 where
  rip : t.RIP = 0x10664e
  values : InputAt t (stackPtr s - 6496) p q u v
  leftTable : Table.TableAt t (stackPtr s - 3120) (Table.oddTable p)
  rightTable : Table.TableAt t (stackPtr s - 2352) (Table.oddTable q)
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi
  pair : t.regValue .rbx = stackPtr s - 6496
  target : t.regValue .r14 = 0x11c930
  cursor : t.regValue .r15 = stackPtr s - 6520

theorem scalar_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p q : Projective} {u v : Nat} (pre : Pre s boundary)
    (input : InputAt s (s.regValue .rsi) p q u v) (packed : PackedTablesOutput s t p q) :
    ∃ fuel w, Advances boundary fuel t w ∧ ScalarInput s w p q u v := by
  obtain ⟨n, a, runA, readyA, _, effectA⟩ := FirstScalar.run boundary pre.outerBoundary t
    (readyToStep packed.machine packed.bindingsSupported)
    (programText_slice (programLoaded_codeIn packed.loaded) 0x6639 FirstScalar.bytes
      (by decide) (by decide +kernel)) packed.rip
  have agreesA : AgreesExcept [.reg 2, .reg 3, .reg 7, .rip] t a := effectA.agrees
  have stateA := packed.toFrameState.after_registers readyA agreesA
    (by simp [Component.Covers]) (by simp)
  have memoryA := agreesA.external (by simp [Component.Covers])
  have dstA : a.regValue .rdi = stackPtr s - 6496 :=
    effectA.writes.2.2.trans (scalar_stack_address packed.rsp (offset := 56) (by decide) (by decide))
  have bxA : a.regValue .rbx = stackPtr s - 6496 :=
    effectA.writes.2.1.trans (scalar_stack_address packed.rsp (offset := 56) (by decide) (by decide))
  obtain ⟨b, runB, stateB, ripB, sourceB, agreesB⟩ := reload_input pre stateA effectA.rip
  have source : b.regValue .rsi = s.regValue .rsi := by
    rw [sourceB, memoryA]
    exact packed.savedInput
  have dstB : b.regValue .rdi = stackPtr s - 6496 :=
    (agreesB.read (n := 64) (r := 7) (by simp)).trans dstA
  have targetB : b.regValue .r14 = 0x11c930 :=
    (agreesB.read (n := 64) (r := 14) (by simp)).trans
      ((agreesA.read (n := 64) (r := 14) (by simp)).trans packed.target)
  obtain ⟨c, runC, stateC, effectC⟩ := call_copy pre stateB 0x664b
    (by decide) (by decide +kernel) ripB targetB
  have sourceC : c.regValue .rsi = s.regValue .rsi :=
    (effectC.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have dstC : c.regValue .rdi = stackPtr s - 6496 :=
    (effectC.agrees.read (n := 64) (r := 7) (by simp)).trans dstB
  have ret : (returnBoundary c).rip = 0x10664e := (callEffect_stack effectC).1
  have cp : CalleePre c boundary 0x11c930 256 256 8 :=
    CalleePre.of_input_and_stack pre
      (⟨6560, 6496, by decide, by decide, by decide, by decide⟩ : StackBufferLayout 8808 256 8)
      stateC.bindingsSupported stateC.machine stateC.directionFlag stateC.loaded stateC.allocated
      effectC.rip stateC.rsp sourceC dstC (ret ▸ inProgram_of_textOffset 0x664e (by decide))
  have count : c.regValue .rdx = 256 :=
    (effectC.agrees.read (n := 64) (r := 2) (by simp)).trans
      ((agreesB.read (n := 64) (r := 2) (by simp)).trans effectA.writes.1)
  obtain ⟨w, result, bytes, _⟩ := memcpy_correct cp count (by decide)
  have work := FieldCall.stack_result_work_frame (frameOffset := 6552) pre stateC result dstC
    (by decide) (by decide) (by decide) (by decide)
  have stateW : State s w := FieldCall.after_result pre stateC result (by decide) work
  have kept (off len : Nat) (ho : off ≤ 6552) (hl : len ≤ off + 8)
      (apart : off + 256 ≤ 6496 ∨ 6496 + len ≤ off) :
      ∀ i < len, w.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (FieldCall.stack_result_byte (frameOffset := 6552) pre stateC result dstC
      (by decide) (by decide) ho hl apart hi).trans
      ((scalar_call_byte (frameOffset := 6552) (by decide) stateB effectC ho hl hi).trans
        (congrArg (fun ram : Ram => ram[_]?)
          ((agreesB.external (by simp [Component.Covers])).trans memoryA)))
  obtain ⟨m, runW⟩ := result.execution
  refine ⟨n+1+1+m, w, ((runA.trans runB).trans runC).trans runW,
    stateW, result.rip.trans ret, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply input.of_bytes_eq
    intro i hi
    have h := bytes i hi
    rw [sourceC, dstC] at h
    exact h.trans (input_byte pre stateC.frame hi)
  · exact packed.leftTable.of_copy (kept 3120 768 (by decide) (by decide) (Or.inl (by decide)))
  · exact packed.rightTable.of_copy (kept 2352 768 (by decide) (by decide) (Or.inl (by decide)))
  · refine Eq.trans ?_ packed.savedOutput
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0)
      (kept 6536 8 (by decide) (by decide) (Or.inr (by decide)) i hi)
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((effectC.agrees.read (n := 64) (r := 3) (by simp)).trans
        ((agreesB.read (n := 64) (r := 3) (by simp)).trans bxA))
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((effectC.agrees.read (n := 64) (r := 14) (by simp)).trans targetB)
  · exact (result.calleeSaved .r15 (by simp)).trans
      ((effectC.agrees.read (n := 64) (r := 15) (by simp)).trans
        ((agreesB.read (n := 64) (r := 15) (by simp)).trans
          ((agreesA.read (n := 64) (r := 15) (by simp)).trans packed.input)))

end P256.Proofs.Verifying.Combination.Preparation.Naf
