import Sha3.Proofs.InputSlices
import Sha3.Proofs.Image
import Sha3.Proofs.Frame
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution

namespace Sha3.Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open Prelude Sha3.Spec.Program

theorem push_r_form_of_readable [Bindings] (t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (opcode : BitVec 8)
    (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hw : MemReadable t (pushAddr t) 8)
    (hpage : (pushAddr t).toNat % 4096 + 8 ≤ 4096) :
    (X86.Instructions.PUSH_GPRv_50_0 ip ctx opcode).run t =
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))
      (.ok (), pushState { t with Next_IP := ip } (src.read t)) := by
  have hpush := push_operation_of_readable { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
  simp only [Operand.read_reg64]
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = w
  rcases hw1 w with rfl | rfl <;>
  · unfold X86.Instructions.PUSH_GPRv_50_0
    spec_run [Read_GPR => readGPR64_run _ _ hmode,
      X86.Instructions.Operations.PUSH => hpush _ (hw.of_external_eq rfl) hpage]

theorem push_r64_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s) (op : UInt8)
    (hop : PushOpcode op) (hcode : BytesAt s s.RIP [op]) (hlow : s.RIP.toNat + 1 ≤ 2^32)
    (hw : MemReadable s (pushAddr s) 8) (hpage : (pushAddr s).toNat % 4096 + 8 ≤ 4096) :
    let src : Operand 64 := .reg (gprNumber 0 0 (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 1 fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP 1#64 } (src.read s))) := by
  have hdecode := decodeLegacy0_run_of_push s h op hop hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 2) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hd : DataReady (afterFetches (beforeFetch s) 2) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl h.memory.tables
  rw [push_r_form_of_readable _ _ _ _ rfl rfl rfl hmode hd h.cpu.ss
    (hw.of_external_eq rfl) hpage] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h op [] hop.legacyOpcode hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem push_r64_rex_step_of_readable [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex op : UInt8) (hrex : RexPrefix rex.toBitVec) (hop : PushOpcode op)
    (hcode : BytesAt s s.RIP [rex, op]) (hlow : s.RIP.toNat + 2 ≤ 2^32)
    (hw : MemReadable s (pushAddr s) 8) (hpage : (pushAddr s).toNat % 4096 + 8 ≤ 4096) :
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP 2#64 } (src.read s))) := by
  have hdecode := decodeLegacy0_run_of_rex_push s h rex op hop hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hd : DataReady (afterFetches (beforeFetch s) 3) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl h.memory.tables
  rw [push_r_form_of_readable _ _ _ _ rfl rfl rfl hmode hd h.cpu.ss
    (hw.of_external_eq rfl) hpage] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex op [] hrex hop.legacyOpcode hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem push_r64_step_of_register_readable [Bindings] (s : RamState) (h : ReadyToStep s)
    (src : BitVec 4) (hcode : BytesAt s s.RIP (encodePushR64 src))
    (hlow : s.RIP.toNat + (encodePushR64 src).length ≤ 2^32)
    (hw : MemReadable s (pushAddr s) 8) (hpage : (pushAddr s).toNat % 4096 + 8 ≤ 4096) :
    X86.Machine.step s = some (.next (pushAfter s src)) := by
  unfold pushAfter
  rcases encodePushR64_spec src with ⟨op, hb, hop, hs⟩ | ⟨rex, op, hb, hr, hop, hs⟩
  · simp only [hb, List.length_singleton] at hcode hlow ⊢
    simpa only [hs] using push_r64_step_of_readable s h op hop hcode hlow hw hpage
  · simp only [hb, List.length_cons, List.length_nil] at hcode hlow ⊢
    simpa only [hs] using push_r64_rex_step_of_readable s h rex op hr hop hcode hlow hw hpage

theorem pushAfter_memoryWriteFrame {s : RamState} {budget : Nat}
    (hStack : Stack.Valid s budget) (hBudget : 8 ≤ budget) (src : BitVec 4) :
    MemoryWriteFrame s (pushAfter s src) #v[Stack.region s budget] := by
  intro address hout
  change (memStore s.external (pushAddr s)
    ((Operand.reg (src.setWidth 5) : Operand 64).read s))[address]? = _
  apply memStore_getElem?_of_ne
  intro i hi he
  have hc := stack_sub_contains hStack hBudget hi
  change (Stack.region s budget).Contains (pushAddr s + BitVec.ofNat 64 i).toNat at hc
  rw [he] at hc
  exact hout (Stack.region s budget) (by simp) hc

theorem pushAfter_readyToStep [Bindings] {s : RamState} {budget : Nat}
    (h : ReadyToStep s) (hStack : Stack.Valid s budget)
    (hAvoid : (Stack.region s budget).Avoids InPageTables)
    (hBudget : 8 ≤ budget) (src : BitVec 4) : ReadyToStep (pushAfter s src) := by
  have hFrame := pushAfter_memoryWriteFrame hStack hBudget src
  have hMemory := identityMappedMemory_of_memoryWriteFrame hFrame
    (by simpa using hAvoid) rfl h.memory
  exact h.of_agreesExcept (AgreesExcept.afterStep_push s _ _ _) hMemory.tables

theorem pushAfter_programLoaded {s : RamState} {budget : Nat}
    (hLoaded : ProgramLoaded s) (hStack : Stack.Valid s budget)
    (hAvoid : (Stack.region s budget).Avoids InProgram)
    (hBudget : 8 ≤ budget) (src : BitVec 4) : ProgramLoaded (pushAfter s src) :=
  programLoaded_of_memoryWriteFrame (pushAfter_memoryWriteFrame hStack hBudget src)
    (by simpa using hAvoid) hLoaded

theorem pushAfter_calleeSavedRegistersUnchanged (s : RamState) (src : BitVec 4) :
    CalleeSavedRegistersUnchanged s (pushAfter s src) := by
  intro register hregister
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hregister
  rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [State.regValue, pushAfter_gpr] <;>
    exact Vector.getElem_set_ne _ _ (by decide)

theorem pushAfter_supportedIntegerMachineState [bindings : Bindings]
    {s : RamState} {budget : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hEnvironment : MachineRamUnitStrideDecodable bindings s)
    (hStack : Stack.Valid s budget) (hAvoid : (Stack.region s budget).Avoids InPageTables)
    (hBudget : 8 ≤ budget) (src : BitVec 4) :
    SupportedIntegerMachineState bindings.processor (pushAfter s src) := by
  have hReady := pushAfter_readyToStep
    (machineRamUnitStrideDecodable_readyToStep hMachine hEnvironment) hStack hAvoid hBudget src
  refine ⟨hReady.cpu, ⟨?_, hMachine.sse.cr0, hMachine.sse.cr4⟩, hReady.memory, hReady.ready⟩
  exact reportsCPUFeature_of_sameControls (s := s) (t := pushAfter s src)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hMachine.sse.feature

theorem pushAfter_directionFlagUnset {s : RamState} (src : BitVec 4)
    (h : DirectionFlagUnset s) : DirectionFlagUnset (pushAfter s src) := h

theorem entry_initial_push_step [Bindings] {s : RamState} {budget : Nat}
    (hReady : ReadyToStep s) (hLoaded : ProgramLoaded s) (hStack : Stack.Valid s budget)
    (hBudget : 8 ≤ budget)
    (hByte : Extracted.programSections.fetchByte s.RIP = some 0x55)
    (hLow : s.RIP.toNat + 1 ≤ 2^32) :
    Machine.step s = some (.next (pushAfter s 5)) := by
  apply push_r64_step_of_register_readable s hReady 5
  · change BytesAt s s.RIP [0x55]
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst i
    simpa only [BitVec.add_zero (n := 64), List.getElem_cons_zero] using
      programLoaded_fetchByte hLoaded hByte
  · exact hLow
  · exact stack_push_readable hStack hBudget
  · exact stack_push_page hStack hBudget

theorem runner_step_of_step_inProgram [Bindings]
    {before after : RamState} {boundary : ReturnBoundary}
    (hStep : Machine.step before = some (.next after))
    (hProgram : InProgram after.RIP) (hReturn : ¬ InProgram boundary.rip) :
    Runner.step boundary before = some (.next after) := by
  have hne : after.RIP ≠ boundary.rip := fun he => hReturn (he ▸ hProgram)
  simp [Runner.step, hStep, hne]

theorem returnBoundary_rip_of_word64At {s : RamState} {address : BitVec 64}
    (hword : (Stack.returnSlot s).Word64At s.external address) :
    (returnBoundary s).rip = address := by
  change memLoad s.external (s.regValue .rsp) 64 = address
  simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    memLoad64_of_word64At hword

theorem entry_initial_push_advances [bindings : Bindings] {s : RamState} {budget : Nat}
    (hReady : ReadyToStep s) (hLoaded : ProgramLoaded s) (hStack : Stack.Valid s budget)
    (hReturn : ValidReturnAddress s) (hBudget : 8 ≤ budget)
    (hByte : Extracted.programSections.fetchByte s.RIP = some 0x55)
    (hNext : Extracted.programSections.fetchByte (BitVec.add s.RIP 1) = some 0x41)
    (hLow : s.RIP.toNat + 1 ≤ 2^32) :
    ∃ boundary, nearReturn64Boundary s = .ok boundary ∧
      Advances boundary 1 s (pushAfter s 5) := by
  obtain ⟨address, hword, _, houtside⟩ := hReturn
  have htop := returnBoundary_rip_of_word64At hword
  have hslot : (Stack.returnSlot s).Bounded := by
    have hbound := hStack.1
    have hunder := hStack.2.2.1
    simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Bounded] at hbound
    change budget ≤ (s.regValue .rsp).toNat at hunder
    change (s.regValue .rsp).toNat + 8 < userAddressLimit
    omega
  have hread : MemReadable s (stackPtr s) 8 := by
    change MemReadable s (s.regValue .rsp) 8
    simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      memReadable_of_word64At hword hslot
  have hboundary := nearReturn64Boundary_eq s hReady.dataReady hReady.cpu.ss hread
  have houtside' : ¬ InProgram (returnBoundary s).rip := by
    rw [htop]
    exact houtside
  have hRip : (pushAfter s 5).RIP = BitVec.add s.RIP 1#64 := by
    change (afterStep s 1 _).RIP = _
    rw [afterStep_push_rip hReady]
    rfl
  have hProgram : InProgram (pushAfter s 5).RIP := by
    rw [hRip]
    exact ⟨0x41, imageSections_mem_toCodeMap_of_fetchByte hNext⟩
  exact ⟨returnBoundary s, hboundary, advances_one (runner_step_of_step_inProgram
    (entry_initial_push_step hReady hLoaded hStack hBudget hByte hLow) hProgram houtside')⟩

end Sha3.Proofs
