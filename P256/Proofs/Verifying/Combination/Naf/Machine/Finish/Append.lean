import P256.Proofs.Verifying.Combination.Naf.Machine.Finish.Memory
import X86Proofs.Instructions.Inc.Generated.R.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Iterator.Advance (step_nomem branch8)
open P256.Proofs.Common.Instructions (mov_m8_imm8_rex_effect_step)

theorem finish_append [Bindings] {s t : RamState} {boundary : ReturnBoundary} {ds : List Int}
    (pre : Pre s boundary) (state : FrameState s t) (rip : t.RIP = 0x10f4df)
    (bound : ds.length ≤ 256) (value : t.regValue .r14 = BitVec.ofNat 64 ds.length)
    (length : memLoad t.external (stackPtr s-136) 64 = 257)
    (pointer : memLoad t.external (stackPtr s-120) 64 = s.regValue .rdi)
    (output : DigitsAt t (s.regValue .rdi) ds) :
    ∃ u, Advances boundary 6 t u ∧ FrameState s u ∧ u.RIP = 0x10f4f5 ∧
      u.regValue .r14 = BitVec.ofNat 64 (ds.length+1) ∧ DigitsAt u (s.regValue .rdi) (ds ++ [1]) := by
  obtain ⟨t1, run1, ready1, loaded1, effect1⟩ := step_nomem (offset := 0xf4df)
    (mov_r64_m64_effect_step 0x10f4df 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
    (readyToStep state.machine state.bindingsSupported) state.loaded
    ⟨rip, by
      change MemReadable t (stackPtr t+0#64) 8
      exact stack_readable pre.toCalleePre state (offset := 0) (by decide)⟩
    (by decide) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4e3 (by decide)))
    (by simp [Component.Covers])
  have agrees1 : AgreesExcept [.reg 6,.rip] t t1 := effect1.agrees
  have state1 := state.after_registers ready1 agrees1 (by simp [Component.Covers]) (by simp)
  have length1 : t1.regValue .rsi = 257 := by
    have h := effect1.writes
    change t1.regValue .rsi = memLoad t.external (stackPtr t+0#64) 64 at h
    simpa only [BitVec.add_zero, state.rsp] using h.trans (by simpa only [state.rsp, BitVec.add_zero] using length)
  have index1 : t1.regValue .r14 = BitVec.ofNat 64 ds.length :=
    (agrees1.read (n := 64) (r := 14) (by simp)).trans value
  obtain ⟨t2, run2, ready2, loaded2, effect2⟩ := step_nomem (offset := 0xf4e3)
    (cmp_r64_r64_effect_step 0x10f4e3 0x49 0xf6 (by simp [RexWPrefix]) rfl)
    ready1 loaded1 effect1.rip (by decide) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4e6 (by decide)))
    (by simp [Component.Covers])
  have condition : condHolds 3 (StatusFlags.ofRFLAGS t2.RFLAGS) = false := by
    have h := effect2.flags.1
    change (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (t1.regValue .r14).ult (t1.regValue .rsi) at h
    rw [index1, length1] at h
    have lt : (BitVec.ofNat 64 ds.length).ult 257#64 = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : ds.length < 2^64), decide_eq_true_eq]
      omega
    simp [condHolds, h, lt]
  obtain ⟨t3, run3, ready3, loaded3, rip3, agrees3⟩ := branch8 (offset := 0xf4e6) 3 0x58 false
    ready2 loaded2 effect2.rip condition (by decide) (by decide +kernel) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4e8 (by decide)))
  have total3 : AgreesExcept [.reg 6,.flags,.rip] t t3 :=
    ((agrees1.trans effect2.agrees).trans agrees3).mono (by simp)
  have state3 := state.after_registers ready3 total3 (by simp [Component.Covers]) (by simp)
  obtain ⟨t4, run4, ready4, _, effect4⟩ := step_nomem (offset := 0xf4e8)
    (mov_r64_m64_effect_step 0x10f4e8 0x48 (by simp [RexWPrefix]) 0
      (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
    ready3 loaded3 ⟨rip3, by
      change MemReadable t3 (stackPtr t3+16#64) 8
      exact stack_readable pre.toCalleePre state3 (offset := 16) (by decide)⟩
    (by decide) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4ed (by decide)))
    (by simp [Component.Covers])
  have agrees4 : AgreesExcept [.reg 0,.rip] t3 t4 := effect4.agrees
  have state4 := state3.after_registers ready4 agrees4 (by simp [Component.Covers]) (by simp)
  have pointer4 : t4.regValue .rax = s.regValue .rdi := by
    have h := effect4.writes
    change t4.regValue .rax = memLoad t3.external (stackPtr t3+16#64) 64 at h
    have address : stackPtr t3+16#64 = stackPtr s-120 := stack_address state3.rsp (offset := 16) (by decide)
    rw [address, total3.external (by simp [Component.Covers])] at h
    exact h.trans pointer
  have index4 : t4.regValue .r14 = BitVec.ofNat 64 ds.length :=
    ((total3.trans agrees4).read (n := 64) (r := 14) (by simp)).trans value
  have output4 : DigitsAt t4 (s.regValue .rdi) ds :=
    digits_of_external_eq output ((total3.trans agrees4).external (by simp [Component.Covers]))
  obtain ⟨t5, run5, ready5, effect5⟩ :=
    (P256.Proofs.Common.Instructions.mov_m8_imm8_rex_effect_step 0x10f4ed 0x42 (by simp [RexNoWPrefix])
      (.sib 0 (some 14) 0 .none) (by decide +kernel) rfl rfl 1).advances ready4
      (programText_slice (programLoaded_codeIn state4.loaded) 0xf4ed
        [0x42,0xc6,0x04,0x30,0x01] (by decide) (by decide +kernel))
      ⟨effect4.rip, by
        change MemWritable t4 (t4.regValue .rax+(t4.regValue .r14 <<< 0)+0#64) 1
        rw [BitVec.shiftLeft_zero, pointer4, index4, BitVec.add_zero]
        exact output_byte_writable pre.toCalleePre state4 (by omega)
      , by
        change RangeApart (t4.regValue .rax+(t4.regValue .r14 <<< 0)+0#64) 1 0x10f4ed 5
        rw [BitVec.shiftLeft_zero, pointer4, index4, BitVec.add_zero]
        exact output_byte_code pre.toCalleePre (by omega)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4f2 (by decide)))
  change ({rip := 0x10f4f2, writes := [⟨(Operand.mem (t4.regValue .rax+(t4.regValue .r14 <<< 0)+0#64) : Operand 8),1⟩]} : Effect).Holds t4 t5 at effect5
  rw [BitVec.shiftLeft_zero, pointer4, index4, BitVec.add_zero] at effect5
  have agrees5 : AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 ds.length) 1,.rip] t4 t5 := by
    simpa [Effect.components] using effect5.agrees
  have state5 := FrameState.after_output_byte pre.toCalleePre state4 (by omega) ready5 agrees5
  have output5 := digits_append_one output4 bound agrees5 effect5.writes
  have index5 : t5.regValue .r14 = BitVec.ofNat 64 ds.length :=
    (agrees5.read (n := 64) (r := 14) (by simp)).trans index4
  obtain ⟨u, run6, ready6, _, effect6⟩ := step_nomem (offset := 0xf4f2)
    (inc_r64_effect_step 0x10f4f2 0x49 0xc6 (by simp [RexWPrefix]) rfl rfl)
    ready5 state5.loaded effect5.rip (by decide) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4f5 (by decide)))
    (by simp [Component.Covers])
  have agrees6 : AgreesExcept [.reg 14,.flags,.rip] t5 u := effect6.agrees
  refine ⟨u, ((((run1.trans run2).trans run3).trans run4).trans run5).trans run6,
    state5.after_registers ready6 agrees6 (by simp [Component.Covers]) (by simp), effect6.rip, ?_,
    digits_of_external_eq output5 (agrees6.external (by simp [Component.Covers]))⟩
  have h := effect6.writes
  change u.regValue .r14 = t5.regValue .r14+1 at h
  rw [index5] at h
  change u.regValue .r14 = BitVec.ofNat 64 ds.length+1#64 at h
  simpa only [BitVec.ofNat_add] using h

end P256.Proofs.Verifying.Combination.Naf.Machine
