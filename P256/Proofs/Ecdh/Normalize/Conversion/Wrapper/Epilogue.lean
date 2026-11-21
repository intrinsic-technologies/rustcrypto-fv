import P256.Proofs.Ecdh.Normalize.Conversion.Wrapper.Entry
import P256.Proofs.Program.Pop
import P256.Proofs.Program.State
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Conversion.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

structure ReturnState [Bindings] (s t : RamState) (cs : List Component) : Prop where
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  rip : t.RIP = 0x107e24
  rsp : stackPtr t = stackPtr s - 40
  saved : ∀ e ∈ ([(3,40),(12,32),(13,24),(14,16),(15,8)] : List (BitVec 5 × Nat)),
    memLoad t.external (stackPtr s - BitVec.ofNat 64 e.2) 64 =
      (Operand.reg e.1 : Operand 64).read s
  returnSlot : memLoad t.external (stackPtr s) 64 = (returnBoundary s).rip
  agrees : AgreesExcept cs s t
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 32, Stack.region s 40]

set_option maxHeartbeats 800000 in
theorem epilogue_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {fuel : Nat} (pre : Pre s boundary)
    (stage : ReturnState s t cs) (run : Advances boundary fuel s t)
    (bp : Component.reg 5 ∉ cs) (df : Component.df ∉ cs)
    (mxcsr : Component.mxcsr ∉ cs) (fcw : Component.fcw ∉ cs) :
    ∃ u, CalleeResult s u boundary 32 40 ∧ u.external = t.external := by
  have code := programLoaded_codeIn stage.loaded
  have readable (off : Nat) (ho : off ≤ 40) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 off) 8 :=
    readable_of_grow (stack_sub_readable pre.stack ho (by omega)) stage.agrees.grow
  obtain ⟨t0, a0, r0, e0⟩ :=
    (mov_r64_r64_effect_step 0x107e24 0x48 0xf8
      (by simp [RexWPrefix]) (by decide)).advances stage.ready
      (programText_slice code 0x7e24 _ (by decide) (by decide +kernel)) stage.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7e27 (by decide)))
  change (movR64R64Effect 0x107e24 0 7 t).Holds t t0 at e0
  have m0 : t0.external = t.external := e0.agrees.external (by simp [Component.Covers])
  have sp0 : stackPtr t0 = stackPtr s - 40 :=
    (e0.agrees.read (n := 64) (r := 4) (by simp)).trans stage.rsp
  obtain ⟨t1, a1, r1, e1⟩ :=
    (pop_register_effect_step 0x107e27 3 (by decide)).advances r0
      (programText_slice (code.of_external_eq m0) 0x7e27 _
        (by decide +kernel) (by decide +kernel))
      ⟨e0.rip, by rw [sp0]; exact (readable 40 (by decide)).of_external_eq m0⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7e28 (by decide)))
  change (popR64Effect 0x107e27 1 3 t0).Holds t0 t1 at e1
  have m1 : t1.external = t.external :=
    (e1.agrees.external (by simp [Component.Covers])).trans m0
  have sp1 : stackPtr t1 = stackPtr s - 32 := by
    have hw : stackPtr t1 = stackPtr t0 + 8 := e1.writes.2
    rw [hw, sp0]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have v1 : (Operand.reg 3 : Operand 64).read t1 =
      (Operand.reg 3 : Operand 64).read s := by
    have hw : (Operand.reg 3 : Operand 64).read t1 =
        memLoad t0.external (stackPtr t0) 64 := e1.writes.1
    rw [hw, sp0, m0]
    exact stage.saved (3,40) (by simp)
  obtain ⟨t2, a2, r2, e2⟩ :=
    (pop_register_effect_step 0x107e28 12 (by decide)).advances r1
      (programText_slice (code.of_external_eq m1) 0x7e28 _
        (by decide +kernel) (by decide +kernel))
      ⟨e1.rip, by rw [sp1]; exact (readable 32 (by decide)).of_external_eq m1⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7e2a (by decide)))
  change (popR64Effect 0x107e28 2 12 t1).Holds t1 t2 at e2
  have m2 : t2.external = t.external :=
    (e2.agrees.external (by simp [Component.Covers])).trans m1
  have sp2 : stackPtr t2 = stackPtr s - 24 := by
    have hw : stackPtr t2 = stackPtr t1 + 8 := e2.writes.2
    rw [hw, sp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have v2 : (Operand.reg 12 : Operand 64).read t2 =
      (Operand.reg 12 : Operand 64).read s := by
    have hw : (Operand.reg 12 : Operand 64).read t2 =
        memLoad t1.external (stackPtr t1) 64 := e2.writes.1
    rw [hw, sp1, m1]
    exact stage.saved (12,32) (by simp)
  obtain ⟨t3, a3, r3, e3⟩ :=
    (pop_register_effect_step 0x107e2a 13 (by decide)).advances r2
      (programText_slice (code.of_external_eq m2) 0x7e2a _
        (by decide +kernel) (by decide +kernel))
      ⟨e2.rip, by rw [sp2]; exact (readable 24 (by decide)).of_external_eq m2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7e2c (by decide)))
  change (popR64Effect 0x107e2a 2 13 t2).Holds t2 t3 at e3
  have m3 : t3.external = t.external :=
    (e3.agrees.external (by simp [Component.Covers])).trans m2
  have sp3 : stackPtr t3 = stackPtr s - 16 := by
    have hw : stackPtr t3 = stackPtr t2 + 8 := e3.writes.2
    rw [hw, sp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have v3 : (Operand.reg 13 : Operand 64).read t3 =
      (Operand.reg 13 : Operand 64).read s := by
    have hw : (Operand.reg 13 : Operand 64).read t3 =
        memLoad t2.external (stackPtr t2) 64 := e3.writes.1
    rw [hw, sp2, m2]
    exact stage.saved (13,24) (by simp)
  obtain ⟨t4, a4, r4, e4⟩ :=
    (pop_register_effect_step 0x107e2c 14 (by decide)).advances r3
      (programText_slice (code.of_external_eq m3) 0x7e2c _
        (by decide +kernel) (by decide +kernel))
      ⟨e3.rip, by rw [sp3]; exact (readable 16 (by decide)).of_external_eq m3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7e2e (by decide)))
  change (popR64Effect 0x107e2c 2 14 t3).Holds t3 t4 at e4
  have m4 : t4.external = t.external :=
    (e4.agrees.external (by simp [Component.Covers])).trans m3
  have sp4 : stackPtr t4 = stackPtr s - 8 := by
    have hw : stackPtr t4 = stackPtr t3 + 8 := e4.writes.2
    rw [hw, sp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have v4 : (Operand.reg 14 : Operand 64).read t4 =
      (Operand.reg 14 : Operand 64).read s := by
    have hw : (Operand.reg 14 : Operand 64).read t4 =
        memLoad t3.external (stackPtr t3) 64 := e4.writes.1
    rw [hw, sp3, m3]
    exact stage.saved (14,16) (by simp)
  obtain ⟨t5, a5, r5, e5⟩ :=
    (pop_register_effect_step 0x107e2e 15 (by decide)).advances r4
      (programText_slice (code.of_external_eq m4) 0x7e2e _
        (by decide +kernel) (by decide +kernel))
      ⟨e4.rip, by rw [sp4]; exact (readable 8 (by decide)).of_external_eq m4⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7e30 (by decide)))
  change (popR64Effect 0x107e2e 2 15 t4).Holds t4 t5 at e5
  have m5 : t5.external = t.external :=
    (e5.agrees.external (by simp [Component.Covers])).trans m4
  have sp5 : stackPtr t5 = stackPtr s := by
    have hw : stackPtr t5 = stackPtr t4 + 8 := e5.writes.2
    rw [hw, sp4]
    exact BitVec.sub_add_cancel _ _
  have v5 : (Operand.reg 15 : Operand 64).read t5 =
      (Operand.reg 15 : Operand 64).read s := by
    have hw : (Operand.reg 15 : Operand 64).read t5 =
        memLoad t4.external (stackPtr t4) 64 := e5.writes.1
    rw [hw, sp4, m4]
    exact stage.saved (15,8) (by simp)
  have top : stackTop t5 = (returnBoundary s).rip := by
    rw [stackTop, sp5]
    change memLoad t5.external (stackPtr s) 64 = _
    rw [m5]
    exact stage.returnSlot
  obtain ⟨u, a6, r6, e6⟩ := (ret_effect_step 0x107e30).advances r5
    (programText_slice (code.of_external_eq m5) 0x7e30 [0xc3]
      (by decide) (by decide +kernel))
    ⟨⟨e5.rip, by rw [sp5]; simpa only [BitVec.sub_zero] using (readable 0 (by decide)).of_external_eq m5⟩,
      top ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop t5 ≠ boundary.rip
        rw [top]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have mem : u.external = t.external :=
    (e6.agrees.external (by simp [Component.Covers])).trans m5
  have tail := (((((e0.agrees.trans e1.agrees).trans e2.agrees).trans e3.agrees).trans
    e4.agrees).trans e5.agrees).trans e6.agrees
  have all := stage.agrees.trans tail
  refine ⟨u, {
    execution := ⟨_, ((((((run.trans a0).trans a1).trans a2).trans a3).trans a4).trans a5).trans a6⟩
    rip := e6.rip.trans top
    rsp := ?_
    bindingsSupported := bindingsSupported_of_ready_agrees pre.bindingsSupported r6 all
    machine := supportedMachine_of_ready_agrees pre.machine r6 all
    calleeSaved := ?_
    directionFlag := all.directionFlagClear (by simpa using df) pre.directionFlag
    mxcsr := all.mxcsr (by simpa using mxcsr)
    fp87 := all.fcw (by simpa using fcw)
    frame := ?_
    loaded := ?_
    allocated := all.grow
  }, mem⟩
  · have hw : stackPtr u = stackPtr t5 + 8 := e6.writes
    change stackPtr u = stackPtr s + 8
    rw [hw, sp5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ((e2.agrees.trans (e3.agrees.trans (e4.agrees.trans (e5.agrees.trans e6.agrees)))).read (n := 64) (r := 3) (by simp)).trans v1
    · exact all.read (n := 64) (r := 5) (by simpa using bp)
    · exact ((e3.agrees.trans (e4.agrees.trans (e5.agrees.trans e6.agrees))).read (n := 64) (r := 12) (by simp)).trans v2
    · exact ((e4.agrees.trans (e5.agrees.trans e6.agrees)).read (n := 64) (r := 13) (by simp)).trans v3
    · exact ((e5.agrees.trans e6.agrees).read (n := 64) (r := 14) (by simp)).trans v4
    · exact (e6.agrees.read (n := 64) (r := 15) (by simp)).trans v5
  · intro a ha
    rw [mem]
    exact stage.frame a ha
  · intro a b hb
    rw [mem]
    exact stage.loaded a b hb

end P256.Proofs.Ecdh.Normalize.Conversion.Wrapper
