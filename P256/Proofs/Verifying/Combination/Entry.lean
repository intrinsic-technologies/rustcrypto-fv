import P256.Proofs.Verifying.Combination.Prologue
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

theorem save_input_pointer [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (state : State s t) (rip : t.RIP = 0x106520) :
    ∃ u, Advances boundary 1 t u ∧ State s u ∧ u.RIP = 0x106525 ∧
      (Operand.mem (stackPtr s - 6544) : Operand 64).read u = t.regValue .rsi ∧
      AgreesExcept [.mem (stackPtr s - 6544) 8, .rip] t u := by
  let am : AddrMode := .sib 4 none 0 (.d8 8)
  have address : storeAddrAt 0x106520 am 5 t = stackPtr s - 6544 :=
    scalar_stack_address state.rsp (offset := 8) (by decide) (by decide)
  have writable : MemWritable t (stackPtr s - 6544) 8 :=
    writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids (Stack.region s 8808) (by simp) a ha (.inr hp)) (offset := 6544) (by decide) (by decide)) state.allocated
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_m64_r64_effect_step 0x106520 0x48 (by simp [RexWPrefix]) 6 am
      (by constructor <;> decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x6520 _ (by decide) (by decide +kernel))
      ⟨rip, address ▸ writable, address ▸
        (by
          have h := stack_code pre state (offset := 8) (len := 8)
            (codeOffset := 0x6520) (codeLen := 5) (by decide) (by decide) (by decide)
          rw [scalar_stack_address state.rsp (offset := 8) (by decide) (by decide)] at h
          exact h)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6525 (by decide)))
  have agrees : AgreesExcept [.mem (stackPtr s - 6544) 8, .rip] t u := by
    have h := effect.agrees
    rw [movM64R64Effect_components] at h
    change AgreesExcept [.mem (storeAddrAt 0x106520 am 5 t) 8, .rip] t u at h
    rwa [address] at h
  refine ⟨u, run, FrameState.after_effect pre (by decide) state ready agrees ?_ (by simp), effect.rip, ?_, agrees⟩
  · intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, by simp, work_contains pre (offset := 6544) (by decide) (by decide) covered⟩
    · exact covered.elim
  · have h := effect.writes
    change (Operand.mem (storeAddrAt 0x106520 am 5 t) : Operand 64).read u = t.regValue .rsi at h
    rwa [address] at h

theorem save_output_pointer [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary)
    (state : State s t) (rip : t.RIP = 0x106525) :
    ∃ u, Advances boundary 1 t u ∧ State s u ∧ u.RIP = 0x10652a ∧
      (Operand.mem (stackPtr s - 6536) : Operand 64).read u = t.regValue .rdi ∧
      AgreesExcept [.mem (stackPtr s - 6536) 8, .rip] t u := by
  let am : AddrMode := .sib 4 none 0 (.d8 16)
  have address : storeAddrAt 0x106525 am 5 t = stackPtr s - 6536 :=
    scalar_stack_address state.rsp (offset := 16) (by decide) (by decide)
  have writable : MemWritable t (stackPtr s - 6536) 8 :=
    writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids (Stack.region s 8808) (by simp) a ha (.inr hp)) (offset := 6536) (by decide) (by decide)) state.allocated
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_m64_r64_effect_step 0x106525 0x48 (by simp [RexWPrefix]) 7 am
      (by constructor <;> decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x6525 _ (by decide) (by decide +kernel))
      ⟨rip, address ▸ writable, address ▸
        (by
          have h := stack_code pre state (offset := 16) (len := 8)
            (codeOffset := 0x6525) (codeLen := 5) (by decide) (by decide) (by decide)
          rw [scalar_stack_address state.rsp (offset := 16) (by decide) (by decide)] at h
          exact h)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x652a (by decide)))
  have agrees : AgreesExcept [.mem (stackPtr s - 6536) 8, .rip] t u := by
    have h := effect.agrees
    rw [movM64R64Effect_components] at h
    change AgreesExcept [.mem (storeAddrAt 0x106525 am 5 t) 8, .rip] t u at h
    rwa [address] at h
  refine ⟨u, run, FrameState.after_effect pre (by decide) state ready agrees ?_ (by simp), effect.rip, ?_, agrees⟩
  · intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, by simp, work_contains pre (offset := 6536) (by decide) (by decide) covered⟩
    · exact covered.elim
  · have h := effect.writes
    change (Operand.mem (storeAddrAt 0x106525 am 5 t) : Operand 64).read u = t.regValue .rdi at h
    rwa [address] at h

def inputCopySetupBytes : List UInt8 :=
  [0x48, 0x8d, 0x9c, 0x24, 0x38, 0x4, 0x0, 0x0, 0x4c, 0x8d, 0x35, 0xf7, 0x63, 0x1, 0x0, 0xba, 0x0, 0x1, 0x0, 0x0, 0x48, 0x89, 0xdf]

def inputCopySetupEffect (s : RamState) : Effect :=
  { rip := 0x106541
    writes := [⟨(Operand.reg 3 : Operand 64), stackPtr s + 1080⟩,
      ⟨(Operand.reg 14 : Operand 64), 0x11c930⟩,
      ⟨(Operand.reg 2 : Operand 64), 256⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 1080⟩] }

theorem inputCopySetup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10652a)
      (codeRange 0x10652a inputCopySetupBytes) (Effect.post inputCopySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10652a 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 1080)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x6532 (by decide))
  advance_then (lea_r64_effect_step 0x106532 0x4c (by simp [RexWPrefix]) 6
    (.rip 0x163f7) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10652a inputCopySetupBytes 8 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6539 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x106539 0xba (by decide) 256)
  case sub => exact codeRange_slice_subset 0x10652a inputCopySetupBytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x653e (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10653e 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10652a inputCopySetupBytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x6541 (by decide))⟩
  advance_finish [inputCopySetupEffect]

theorem entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ fuel t, Advances boundary fuel s t ∧ State s t ∧ t.RIP = 0x106541 ∧
      t.regValue .rsi = s.regValue .rsi ∧ (Operand.mem (stackPtr s - 6544) : Operand 64).read t = s.regValue .rsi ∧
      t.regValue .rdi = stackPtr s - 5472 ∧ t.regValue .rbx = stackPtr s - 5472 ∧
      t.regValue .r14 = 0x11c930 ∧ t.regValue .rdx = 256 ∧
      (Operand.mem (stackPtr s - 6536) : Operand 64).read t = s.regValue .rdi := by
  obtain ⟨t0, run0, state0, rip0, agrees0⟩ := prologue pre
  obtain ⟨t1, run1, state1, rip1, r15, agrees1⟩ := save_input_pointer pre state0 rip0
  obtain ⟨t2, run2, state2, rip2, output, agrees2⟩ := save_output_pointer pre state1 rip1
  obtain ⟨n, t3, run3, ready3, _, effect⟩ := inputCopySetup_correct boundary pre.outerBoundary
    t2 (readyToStep state2.machine state2.bindingsSupported)
    (programText_slice (programLoaded_codeIn state2.loaded) 0x652a inputCopySetupBytes
      (by decide) (by decide +kernel)) rip2
  have components : (inputCopySetupEffect t2).components = [.reg 3, .reg 14, .reg 2, .reg 7, .rip] := by rfl
  have agrees3 : AgreesExcept [.reg 3, .reg 14, .reg 2, .reg 7, .rip] t2 t3 := by
    simpa only [components] using effect.agrees
  have rsi0 : t0.regValue .rsi = s.regValue .rsi := agrees0.read (n := 64) (r := 6) (by simp [saveFrame])
  have rdi1 : t1.regValue .rdi = s.regValue .rdi :=
    (agrees1.read (n := 64) (r := 7) (by simp)).trans (agrees0.read (n := 64) (r := 7) (by simp [saveFrame]))
  have address : stackPtr t2 + 1080#64 = stackPtr s - 5472 :=
    scalar_stack_address state2.rsp (offset := 1080) (by decide) (by decide)
  refine ⟨11 + n, t3, ((run0.trans run1).trans run2).trans run3,
    state2.after_registers ready3 agrees3 (by simp [Component.Covers]) (by simp), effect.rip,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((agrees3.read (n := 64) (r := 6) (by simp)).trans
      (agrees2.read (by simp))).trans ((agrees1.read (by simp)).trans rsi0)
  · change memLoad t3.external _ 64 = _
    rw [agrees3.external (by simp [Component.Covers])]
    refine Eq.trans ?_ (r15.trans rsi0)
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    apply agrees2.byte
    intro c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, he⟩ := covered
      have addr : stackPtr s - 6536 = (stackPtr s - 6544) + 8 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [addr, BitVec.add_assoc] at he
      exact RangeApart.offsets (stackPtr s - 6544) (a := 0) (b := 8)
        (len := 8) (count := 8) (by decide) (by decide) (.inl (by decide))
        i hi j hj (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc] using he)
    · exact covered.elim
  · exact effect.writes.2.2.2.trans address
  · exact effect.writes.1.trans address
  · exact effect.writes.2.1
  · exact effect.writes.2.2.1
  · have memory := agrees3.external (by simp [Component.Covers])
    change memLoad t3.external _ 64 = _
    rw [memory]
    exact output.trans rdi1

end P256.Proofs.Verifying.Combination
