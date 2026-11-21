import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Variants
import Sha2.Proofs.Common.Machine.FrameMemory
import Sha2.Proofs.Common.Memory.LoadBytes
import Sha2.Proofs.Wrapper512.Absorb.State
import Sha2.Proofs.Common.Machine.CallMemory
import Sha2.Proofs.Wrapper512.Dispatch.Branch
import Sha2.Proofs.Wrapper512.Dispatch.Loop

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Dispatch

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper

theorem returnBoundary_of_call [bindings : Bindings] {v : Variant} {initial : RamState}
    {inputs : Array Input} (machine : SupportedMachine bindings initial)
    (call : ValidCall v.routine initial inputs) :
    ¬ InProgram (returnBoundary initial).rip := by
  have readable : MemReadable initial (stackPtr initial) 8 := by
    apply memoryRegion_memReadable call.stack.1 call.stack.2.1
    · change (Stack.region initial v.routine.minStackBytes).start ≤
        (stackPtr initial).toNat
      change (stackPtr initial).toNat - v.routine.minStackBytes ≤
        (stackPtr initial).toNat
      omega
    · rw [stack_region_end]
      omega
  have near := nearReturn64Boundary_eq initial (supportedMachine_readyToStep machine).dataReady
    machine.supported.integer.ss readable
  obtain ⟨address, loaded, _low, outside⟩ := call.returnAddress
  have value : memLoad initial.external (stackPtr initial) 64 = address := by
    rw [stackPtr_eq_regValue_rsp]
    apply Sha2.Proofs.Common.Memory.memLoad_of_loadBytes64
    simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded.2
  have : Prelude.nearReturn64Boundary initial = .ok (returnBoundary initial) := near
  rw [show (returnBoundary initial).rip = memLoad initial.external (stackPtr initial) 64 by rfl,
    value]
  exact outside

theorem Buffered.after_loop [Bindings] {v : Variant} {initial s t : RamState}
    {message : ByteArray} (state : Buffered v initial s message)
    {fuel : Nat} (execution : Advances (returnBoundary initial) fuel s t)
    (ready : ReadyToStep t)
    (agrees : AgreesExcept [.reg 15, .reg 14, .flags, .rip] s t) :
    Buffered v initial t message := by
  have hmemory : t.external = s.external := agrees.external (by simp [Component.Covers])
  have writes : WritesWithin [.reg 15, .reg 14, .flags, .rip]
      #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact ha.elim
  obtain ⟨previous, previousExecution⟩ := state.execution
  have rspT : stackPtr t = stackPtr s :=
    agrees.read (n := 64) (r := 4) (by simp)
  have current : State v initial t := by
    refine ⟨⟨previous + fuel, previousExecution.trans execution⟩,
      supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
      fun a ha => agrees.grow a (state.allocated a ha), ?_,
      agrees.directionFlagClear (by simp) state.directionFlag,
      memoryWriteFrame_trans state.frame (agrees.memoryWriteFrame writes),
      rspT.trans state.rsp⟩
    · intro address byte fetch
      rw [hmemory]
      exact state.loaded address byte fetch
    · refine ⟨?_, ?_⟩
      · intro slot hs
        rw [hmemory]
        exact state.saved.words slot hs
      · rw [hmemory]
        exact state.saved.returnAddress
  have preserved : Preserved v initial t := by
    refine ⟨current, ?_, ?_, ?_⟩
    · simpa only [hmemory] using state.outputPointer
    · simpa only [hmemory] using state.pointerTable
    · simpa only [hmemory] using state.lengthTable
  refine ⟨preserved, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨state.hashWords.1, ?_⟩
    intro i hi
    rw [hmemory]
    exact state.hashWords.2 i hi
  · simpa only [hmemory] using state.tailBytes
  · simpa only [hmemory] using state.tailLength
  · simpa only [hmemory] using state.blockCount
  · simpa only [hmemory] using state.blockCountHigh

set_option maxHeartbeats 1000000 in
theorem loop_from_buffered [Bindings] {v : Variant}
    {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs) (state : Buffered v initial s ByteArray.empty)
    (rip : s.RIP = v.pc 0xd0)
    (count : s.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (positive : 0 < inputs.size) (outside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ t, LoopState v initial t inputs 0 := by
  obtain ⟨u, branchRun, branchReady, branchRip, branchAgrees⟩ :=
    branch (supportedMachine_readyToStep state.machine) state.loaded rip outside
  have countU : u.regValue .rsi = BitVec.ofNat 64 inputs.size :=
    (branchAgrees.read (n := 64) (r := 6) (by simp)).trans count
  have countNat : (s.regValue .rsi).toNat = inputs.size := by
    rw [count]
    simp only [BitVec.toNat_ofNat]
    have bound := validCall_count_bound ctx.call
    omega
  have nonzero : s.regValue .rsi ≠ 0 := by
    intro zero
    rw [zero] at countNat
    simp at countNat
    exact (Nat.ne_of_gt positive) countNat.symm
  have branchRip' : u.RIP = v.pc 0xd9 := by
    rw [branchRip]
    simp only [ite_eq_right nonzero]
  have loadedU : ProgramLoaded u := by
    intro address byte fetch
    rw [branchAgrees.external (by simp [Component.Covers])]
    exact state.loaded address byte fetch
  obtain ⟨fuel, t, loopRun, loopReady, _, loopEffect⟩ :=
    Loop.run (returnBoundary initial) outside u branchReady (Loop.code loadedU) branchRip'
  have bufferedU : Buffered v initial u ByteArray.empty :=
    Buffered.after_loop state branchRun branchReady
      (branchAgrees.mono (by simp))
  have bufferedT : Buffered v initial t ByteArray.empty :=
    Buffered.after_loop bufferedU loopRun loopReady loopEffect.agrees
  have writes : t.regValue .r15 = u.regValue .rsi ∧
      t.regValue .r14 = 0 := by
    have writes := loopEffect.writes
    simp only [Loop.effect, Write.AllHold, Operand.read] at writes
    exact writes
  have countT : t.regValue .r15 = BitVec.ofNat 64 inputs.size := writes.1.trans countU
  refine ⟨t, ?_⟩
  refine ⟨?_, loopEffect.rip, writes.2, countT, positive, ?_, ?_, trivial, ?_⟩
  · simpa only [prefixMessage_zero] using bufferedT
  · intro impossible; cases impossible
  · intro impossible; cases impossible
  · intro second impossible; cases impossible

set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs)
    (initialized : ∃ s, Buffered v initial s ByteArray.empty ∧
      s.RIP = v.pc 0xd0 ∧ s.regValue .rsi = BitVec.ofNat 64 inputs.size) :
    ∃ t, (Buffered v initial t (message inputs) ∧ t.RIP = v.pc 0x218) ∨
      LoopState v initial t inputs 0 := by
  obtain ⟨s, state, rip, count⟩ := initialized
  have outside := returnBoundary_of_call ctx.machine ctx.call
  have countNat : (s.regValue .rsi).toNat = inputs.size := by
    rw [count]
    simp only [BitVec.toNat_ofNat]
    have bound := validCall_count_bound ctx.call
    omega
  obtain ⟨u, branchRun, branchReady, branchRip, branchAgrees⟩ :=
    branch (supportedMachine_readyToStep state.machine) state.loaded rip outside
  have bufferedU : Buffered v initial u ByteArray.empty :=
    Buffered.after_loop state branchRun branchReady
      (branchAgrees.mono (by simp))
  by_cases empty : inputs.size = 0
  · have zero : s.regValue .rsi = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [countNat, empty]
      rfl
    have arrayEmpty : inputs = #[] := Array.eq_empty_of_size_eq_zero empty
    have target : u.RIP = v.pc 0x218 := by
      rw [branchRip]
      simp only [zero, ite_true]
    refine ⟨u, .inl ⟨?_, target⟩⟩
    simpa only [arrayEmpty, message, Array.foldl_empty] using bufferedU
  · have positive : 0 < inputs.size := Nat.pos_of_ne_zero empty
    obtain ⟨t, loopState⟩ := loop_from_buffered ctx state rip count positive outside
    exact ⟨t, .inr loopState⟩

set_option maxHeartbeats 1000000 in
theorem reset_first_loop [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.reset 0))
    (state : Buffered v initial s ByteArray.empty (.reset 0))
    (rip : s.RIP = v.pc 0xe9 (.reset 0))
    (count : s.regValue .r12 = BitVec.ofNat 64 inputs.size)
    (positive : 0 < inputs.size) : ∃ t, LoopState v initial t inputs 0 (.reset 0) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  let site : Nat × BitVec 4 × BitVec 32 :=
    ((ResetLayout.reset v).textOffset + 0xe9, 12, 0x2e3)
  have member : site ∈ resetBranchSites v := by cases v <;> decide
  have entry : s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.1 := by
    cases v <;> exact rip
  obtain ⟨fuel, u, run, readyU, post⟩ := reset_branch member
    (supportedMachine_readyToStep state.machine) state.loaded entry outside
  have countNe : s.regValue .r12 ≠ 0 := by
    rw [count]
    intro zero
    have eq : inputs.size % 2^64 = 0 := by simpa using congrArg BitVec.toNat zero
    have bound := ctx.count_bound
    omega
  have branchFrame : AgreesExcept [.flags, .rip] s u := post.agrees
  have stateU := Absorb.buffered_of_agrees ctx state run readyU branchFrame
    (by simp [Component.Covers]) (by simp)
  have entryU : u.RIP = Loop.resetFirstPC v := by
    have h := post.rip
    change u.RIP = (if s.regValue .r12 = 0 then _ else _) at h
    simp only [ite_eq_right countNe] at h
    cases v <;> exact h
  obtain ⟨fuelT, t, runT, readyT, _, postT⟩ :=
    Loop.reset_first_run (v := v) (returnBoundary initial) outside u readyU
      (Loop.resetFirst_code stateU.loaded) entryU
  have stateT := Absorb.buffered_of_agrees ctx stateU runT readyT postT.agrees
    (by simp [Loop.resetFirstEffect, Effect.components, Component.Covers])
    (by simp [Loop.resetFirstEffect, Effect.components])
    (by simp [Loop.resetFirstEffect, Effect.components])
  have countT : t.regValue .r12 = BitVec.ofNat 64 inputs.size :=
    (postT.agrees.read (n := 64) (r := 12) (by simp [Loop.resetFirstEffect, Effect.components])).trans
      ((branchFrame.read (n := 64) (r := 12) (by simp)).trans count)
  refine ⟨t, ?_, ⟨_, run.trans runT⟩, (postT.agrees.external (by cases v <;> simp [Loop.resetFirstEffect, Effect.components, Component.Covers])).trans (branchFrame.external (by simp [Component.Covers]))⟩
  refine ⟨?_, ?_, ?_, ?_, positive, ?_, ?_, ?_, ?_⟩
  · simpa only [prefixMessage_zero] using stateT
  · have h := postT.rip
    cases v <;> exact h
  · have h := postT.writes
    change t.regValue .r15 = 0 at h
    cases v <;> exact h
  · cases v <;> exact countT
  · intro impossible
    cases impossible

  · intro impossible; cases impossible
  · intro impossible; cases impossible
  · intro second impossible; cases impossible

set_option maxHeartbeats 1000000 in
theorem reset_first_dispatch [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.reset 0))
    (state : Buffered v initial s ByteArray.empty (.reset 0))
    (rip : s.RIP = v.pc 0xe9 (.reset 0))
    (count : s.regValue .r12 = BitVec.ofNat 64 inputs.size) :
    ∃ t, ((Buffered v initial t (message inputs) (.reset 0) ∧
      t.RIP = v.pc (v.dispatchOffset (.reset 0) inputs.isEmpty) (.reset 0) ∧ v.countValue (.reset 0) initial t = BitVec.ofNat 64 inputs.size ∧ ∀ r : BitVec 5, (.reg r : Operand 64).read t = (.reg r : Operand 64).read s) ∨ LoopState v initial t inputs 0 (.reset 0)) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  by_cases empty : inputs.size = 0
  · have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    let site : Nat × BitVec 4 × BitVec 32 :=
      ((ResetLayout.reset v).textOffset + 0xe9, 12, 0x2e3)
    have member : site ∈ resetBranchSites v := by cases v <;> decide
    have entry : s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.1 := by
      cases v <;> exact rip
    obtain ⟨fuel, t, run, readyT, post⟩ := reset_branch member
      (supportedMachine_readyToStep state.machine) state.loaded entry outside
    have branchFrame : AgreesExcept [.flags, .rip] s t := post.agrees
    have stateT := Absorb.buffered_of_agrees ctx state run readyT branchFrame
      (by simp [Component.Covers]) (by simp)
    have zero : s.regValue .r12 = 0 := by simpa [empty] using count
    have emptyBool : inputs.isEmpty = true := by simp [Array.isEmpty, empty]
    have target : t.RIP = v.pc (v.dispatchOffset (.reset 0) inputs.isEmpty) (.reset 0) := by
      have h := post.rip
      change t.RIP = (if s.regValue .r12 = 0 then _ else _) at h
      simp only [zero, ite_true] at h
      rw [emptyBool]
      cases v <;> exact h
    have arrayEmpty : inputs = #[] := Array.eq_empty_of_size_eq_zero empty
    refine ⟨t, .inl ⟨?_, target, by cases v <;> exact (branchFrame.read (n := 64) (r := 12) (by simp)).trans count, fun r => branchFrame.read (n := 64) (r := r) (by simp)⟩, ⟨_, run⟩, branchFrame.external (by simp [Component.Covers])⟩
    simpa only [arrayEmpty, message, Array.foldl_empty] using stateT
  · obtain ⟨t, stateT, localRun, memory⟩ := reset_first_loop ctx state rip count (Nat.pos_of_ne_zero empty)
    exact ⟨t, .inr stateT, localRun, memory⟩

set_option maxHeartbeats 1000000 in
theorem reset_next_loop [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.reset 1))
    (state : Buffered v initial s ByteArray.empty (.reset 1))
    (rip : s.RIP = v.pc 0x29e (.reset 1))
    (count : s.regValue .r12 = BitVec.ofNat 64 inputs.size)
    (positive : 0 < inputs.size) : ∃ t, LoopState v initial t inputs 0 (.reset 1) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have entry : s.RIP = Loop.resetNextPC v := by cases v <;> exact rip
  obtain ⟨fuel, t, run, readyT, _, post⟩ :=
    Loop.reset_next_run (v := v) (returnBoundary initial) outside s
      (supportedMachine_readyToStep state.machine) (Loop.resetNext_code state.loaded) entry
  have stateT := Absorb.buffered_of_agrees ctx state run readyT post.agrees
    (by simp [Loop.resetNextEffect, Effect.components, Component.Covers])
    (by simp [Loop.resetNextEffect, Effect.components])
    (by simp [Loop.resetNextEffect, Effect.components])
  have countT : t.regValue .r12 = BitVec.ofNat 64 inputs.size :=
    (post.agrees.read (n := 64) (r := 12)
      (by simp [Loop.resetNextEffect, Effect.components])).trans count
  have indexT : t.regValue .r15 = 0 := post.writes.1
  refine ⟨t, ?_, ⟨_, run⟩, post.agrees.external (by simp [Loop.resetNextEffect, Effect.components, Component.Covers])⟩
  refine ⟨?_, ?_, ?_, ?_, positive, ?_, ?_, ?_, ?_⟩
  · simpa only [prefixMessage_zero] using stateT
  · have h := post.rip
    cases v <;> exact h
  · cases v <;> exact indexT
  · cases v <;> exact countT
  · intro impossible
    cases impossible
  · intro _
    have h : t.regValue .rbx = stackPtr s := post.writes.2
    exact h.trans state.rsp
  · intro impossible; cases impossible
  · intro second impossible; cases impossible

set_option maxHeartbeats 1000000 in
theorem reset_last_loop [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.reset 2))
    (state : Buffered v initial s ByteArray.empty (.reset 2))
    (rip : s.RIP = v.pc (v.outputEndOffset (.reset 1)) (.reset 2))
    (count : s.regValue .r12 = BitVec.ofNat 64 inputs.size)
    (positive : 0 < inputs.size) : ∃ t, LoopState v initial t inputs 0 (.reset 2) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  let site : Nat × BitVec 4 × BitVec 32 :=
    (resetBranchSites v)[1]!
  have member : site ∈ resetBranchSites v := by cases v <;> decide
  have entry : s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.1 := by
    cases v <;> exact rip
  obtain ⟨fuel, u, run, readyU, post⟩ := reset_branch member
    (supportedMachine_readyToStep state.machine) state.loaded entry outside
  have countNe : s.regValue .r12 ≠ 0 := by
    rw [count]
    intro zero
    have eq : inputs.size % 2^64 = 0 := by simpa using congrArg BitVec.toNat zero
    have bound := ctx.count_bound
    omega
  have branchFrame : AgreesExcept [.flags, .rip] s u := post.agrees
  have stateU := Absorb.buffered_of_agrees ctx state run readyU branchFrame
    (by simp [Component.Covers]) (by simp)
  have entryU : u.RIP = Loop.resetLastPC v := by
    have h := post.rip
    have countReg : site.2.1 = 12 := by cases v <;> decide
    simp only [Reset.Dispatch.branchEffect, countReg] at h
    change u.RIP = (if s.regValue .r12 = 0 then _ else _) at h
    simp only [ite_eq_right countNe] at h
    cases v <;> exact h
  obtain ⟨fuelT, t, runT, readyT, _, postT⟩ :=
    Loop.reset_last_run (v := v) (returnBoundary initial) outside false u readyU
      (Loop.resetLast_code stateU.loaded) entryU
  have stateT := Absorb.buffered_of_agrees ctx stateU runT readyT postT.agrees
    (by simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components, Component.Covers])
    (by simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components])
    (by simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components])
  have countT : t.regValue .r12 = BitVec.ofNat 64 inputs.size :=
    (postT.agrees.read (n := 64) (r := 12) (by simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components])).trans
      ((branchFrame.read (n := 64) (r := 12) (by simp)).trans count)
  refine ⟨t, ?_, ⟨_, run.trans runT⟩, (postT.agrees.external (by cases v <;> simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components, Component.Covers])).trans (branchFrame.external (by simp [Component.Covers]))⟩
  refine ⟨?_, ?_, ?_, ?_, positive, ?_, ?_, ?_, ?_⟩
  · simpa only [prefixMessage_zero] using stateT
  · have h := postT.rip
    cases v <;> exact h
  · have indexT : t.regValue .r15 = 0 := postT.writes.1
    cases v <;> exact indexT
  · cases v <;> exact countT
  · intro impossible
    cases impossible

  · intro impossible; cases impossible
  · intro _
    have h := postT.writes.2
    cases v <;> exact h
  · intro second impossible; cases impossible

set_option maxHeartbeats 1000000 in
theorem reset_last_dispatch [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.reset 2))
    (state : Buffered v initial s ByteArray.empty (.reset 2))
    (rip : s.RIP = v.pc (v.outputEndOffset (.reset 1)) (.reset 2))
    (count : s.regValue .r12 = BitVec.ofNat 64 inputs.size) :
    ∃ t, ((Buffered v initial t (message inputs) (.reset 2) ∧
      t.RIP = v.pc (v.dispatchOffset (.reset 2) inputs.isEmpty) (.reset 2) ∧ v.countValue (.reset 2) initial t = BitVec.ofNat 64 inputs.size) ∨ LoopState v initial t inputs 0 (.reset 2)) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  by_cases empty : inputs.size = 0
  · have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    let site : Nat × BitVec 4 × BitVec 32 :=
      (resetBranchSites v)[1]!
    have member : site ∈ resetBranchSites v := by cases v <;> decide
    have entry : s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.1 := by
      cases v <;> exact rip
    obtain ⟨fuel, t, run, readyT, post⟩ := reset_branch member
      (supportedMachine_readyToStep state.machine) state.loaded entry outside
    have branchFrame : AgreesExcept [.flags, .rip] s t := post.agrees
    have stateT := Absorb.buffered_of_agrees ctx state run readyT branchFrame
      (by simp [Component.Covers]) (by simp)
    have zero : s.regValue .r12 = 0 := by simpa [empty] using count
    have emptyBool : inputs.isEmpty = true := by simp [Array.isEmpty, empty]
    have target : t.RIP = v.pc (v.dispatchOffset (.reset 2) inputs.isEmpty) (.reset 2) := by
      have h := post.rip
      have countReg : site.2.1 = 12 := by cases v <;> decide
      simp only [Reset.Dispatch.branchEffect, countReg] at h
      change t.RIP = (if s.regValue .r12 = 0 then _ else _) at h
      simp only [zero, ite_true] at h
      rw [emptyBool]
      cases v <;> exact h
    have arrayEmpty : inputs = #[] := Array.eq_empty_of_size_eq_zero empty
    refine ⟨t, .inl ⟨?_, target, by cases v <;> exact (branchFrame.read (n := 64) (r := 12) (by simp)).trans count⟩, ⟨_, run⟩, branchFrame.external (by simp [Component.Covers])⟩
    simpa only [arrayEmpty, message, Array.foldl_empty] using stateT
  · obtain ⟨t, stateT, localRun, memory⟩ := reset_last_loop ctx state rip count (Nat.pos_of_ne_zero empty)
    exact ⟨t, .inr stateT, localRun, memory⟩

set_option maxHeartbeats 1000000 in
theorem finalize_first_prepared [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.finalizeIntoReset false))
    (state : Buffered v initial s ByteArray.empty (.finalizeIntoReset false))
    (rip : s.RIP = Loop.finalizeFirstSetupPC v)
    (count : s.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (countTruncated : Loop.finalizeFirstCopiesCount v = false →
      s.regValue .r15 = BitVec.ofNat 64 inputs.size)
    : ∃ u, Buffered v initial u ByteArray.empty (.finalizeIntoReset false) ∧
      u.RIP = finalizeFirstBranchPC v ∧
      u.regValue .rsi = BitVec.ofNat 64 inputs.size ∧ u.regValue .r14 = 0 ∧
      v.countValue (.finalizeIntoReset false) initial u = BitVec.ofNat 64 inputs.size ∧ (∃ fuel, Advances (returnBoundary initial) fuel s u) ∧ u.external = s.external := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside : BlockInProgram (Loop.finalizeFirstSetupPC v) 6 := by
    apply blockInProgram_of_textOffset
    cases v <;> decide
  obtain ⟨fuel, u, run, readyU, _, post⟩ := Loop.finalize_first_setup _ _
    (returnBoundary initial) outside inside s (supportedMachine_readyToStep state.machine)
    (Loop.finalizeFirstSetup_code state.loaded) rip
  have noMem : ∀ c ∈ (Loop.finalizeFirstSetupEffect
      (Loop.finalizeFirstSetupPC v) (Loop.finalizeFirstCopiesCount v) s).components,
      ∀ a, ¬ c.Covers a := by cases v <;> simp [Loop.finalizeFirstSetupEffect,
        Loop.finalizeFirstCopiesCount, Effect.components, Component.Covers]
  have stateU := Absorb.buffered_of_agrees ctx state run readyU post.agrees noMem
    (by cases v <;> simp [Loop.finalizeFirstSetupEffect, Loop.finalizeFirstCopiesCount, Effect.components])
    (by cases v <;> simp [Loop.finalizeFirstSetupEffect, Loop.finalizeFirstCopiesCount, Effect.components])
  have countU : u.regValue .rsi = BitVec.ofNat 64 inputs.size :=
    (post.agrees.read (n := 64) (r := 6) (by cases v <;>
      simp [Loop.finalizeFirstSetupEffect, Loop.finalizeFirstCopiesCount, Effect.components])).trans count
  have countReg : v.countValue (.finalizeIntoReset false) initial u = BitVec.ofNat 64 inputs.size := by
    cases v with
    | sha384 => exact post.writes.1.trans count
    | sha512 => exact post.writes.1.trans count
    | sha512_224 =>
      exact (post.agrees.read (n := 64) (r := 15) (by simp [Loop.finalizeFirstSetupEffect, Loop.finalizeFirstCopiesCount, Effect.components])).trans (countTruncated rfl)
    | sha512_256 =>
      exact (post.agrees.read (n := 64) (r := 15) (by simp [Loop.finalizeFirstSetupEffect, Loop.finalizeFirstCopiesCount, Effect.components])).trans (countTruncated rfl)
  have indexU : u.regValue .r14 = 0 := by
    cases v with
    | sha384 => exact post.writes.2
    | sha512 => exact post.writes.2
    | sha512_224 => exact post.writes
    | sha512_256 => exact post.writes
  have entryU : u.RIP = finalizeFirstBranchPC v := by
    have h := post.rip
    cases v <;> exact h
  exact ⟨u, stateU, entryU, countU, indexU, countReg, ⟨_, run⟩, post.agrees.external noMem⟩


set_option maxHeartbeats 1000000 in
theorem finalize_first_loop [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.finalizeIntoReset false))
    (state : Buffered v initial s ByteArray.empty (.finalizeIntoReset false))
    (rip : s.RIP = Loop.finalizeFirstSetupPC v)
    (count : s.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (countTruncated : Loop.finalizeFirstCopiesCount v = false →
      s.regValue .r15 = BitVec.ofNat 64 inputs.size)
    (positive : 0 < inputs.size) :
    ∃ t, LoopState v initial t inputs 0 (.finalizeIntoReset false) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  obtain ⟨u, stateU, entryU, countU, indexU, countReg, ⟨fuelU, runU⟩, memoryU⟩ :=
    finalize_first_prepared ctx state rip count countTruncated
  have readyU := supportedMachine_readyToStep stateU.machine
  obtain ⟨t, runT, readyT, ripT, frameT⟩ := finalize_first_branch readyU stateU.loaded entryU outside
  have stateT := Absorb.buffered_of_agrees ctx stateU runT readyT frameT
    (by simp [Component.Covers]) (by simp)
  have nonzero : u.regValue .rsi ≠ 0 := by
    rw [countU]
    intro zero
    have eq : inputs.size % 2^64 = 0 := by simpa using congrArg BitVec.toNat zero
    have bound := ctx.count_bound
    omega
  simp only [ite_eq_right nonzero] at ripT
  refine ⟨t, ?_, ⟨_, runU.trans runT⟩, (frameT.external (by simp [Component.Covers])).trans memoryU⟩
  refine ⟨?_, ?_, ?_, ?_, positive, ?_, ?_, trivial, ?_⟩
  · simpa only [prefixMessage_zero] using stateT
  · cases v <;> exact ripT
  · have indexT := (frameT.read (n := 64) (r := 14) (by simp)).trans indexU
    cases v <;> exact indexT
  · cases v
    · exact (frameT.read (n := 64) (r := 12) (by simp)).trans countReg
    · exact (frameT.read (n := 64) (r := 12) (by simp)).trans countReg
    · exact (frameT.read (n := 64) (r := 15) (by simp)).trans countReg
    · exact (frameT.read (n := 64) (r := 15) (by simp)).trans countReg
  · intro impossible; cases impossible
  · intro impossible; cases impossible
  · intro second impossible; cases impossible

set_option maxHeartbeats 1000000 in
theorem finalize_first_dispatch [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.finalizeIntoReset false))
    (state : Buffered v initial s ByteArray.empty (.finalizeIntoReset false))
    (rip : s.RIP = Loop.finalizeFirstSetupPC v)
    (count : s.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (countTruncated : Loop.finalizeFirstCopiesCount v = false →
      s.regValue .r15 = BitVec.ofNat 64 inputs.size) :
    ∃ t, ((Buffered v initial t (message inputs) (.finalizeIntoReset false) ∧
      t.RIP = v.pc (v.dispatchOffset (.finalizeIntoReset false) inputs.isEmpty)
        (.finalizeIntoReset false) ∧
      v.countValue (.finalizeIntoReset false) initial t = BitVec.ofNat 64 inputs.size ∧
      t.regValue .rax = 0 ∧ t.regValue .r12 = 0 ∧ t.regValue .r14 = 0 ∧ t.regValue .r15 = 0) ∨ LoopState v initial t inputs 0 (.finalizeIntoReset false)) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  by_cases empty : inputs.size = 0
  · have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    obtain ⟨u, stateU, entryU, countU, _indexU, _countReg, ⟨fuelU, runU⟩, memoryU⟩ :=
      finalize_first_prepared ctx state rip count countTruncated
    obtain ⟨a, runA, readyA, ripA, frameA⟩ := finalize_first_branch
      (supportedMachine_readyToStep stateU.machine) stateU.loaded entryU outside
    have stateA := Absorb.buffered_of_agrees ctx stateU runA readyA frameA
      (by simp [Component.Covers]) (by simp)
    have zero : u.regValue .rsi = 0 := by simpa [empty] using countU
    have entryA : a.RIP = Loop.finalizeFirstEmptyPC v := by
      simp only [zero, ite_true] at ripA
      cases v <;> exact ripA
    have inside : BlockInProgram (Loop.finalizeFirstEmptyPC v) 327 := by
      apply blockInProgram_of_textOffset
      cases v <;> decide
    obtain ⟨fuel, t, run, readyT, _, post⟩ := Loop.finalize_first_empty _ _
      (returnBoundary initial) outside inside a readyA (Loop.finalizeFirstEmpty_code stateA.loaded) entryA
    have stateT := Absorb.buffered_of_agrees ctx stateA run readyT post.agrees
      (by cases v <;> simp [Loop.finalizeFirstEmptyEffect, Loop.finalizeFirstCopiesCount,
        Effect.components, Component.Covers])
      (by cases v <;> simp [Loop.finalizeFirstEmptyEffect, Loop.finalizeFirstCopiesCount, Effect.components])
      (by cases v <;> simp [Loop.finalizeFirstEmptyEffect, Loop.finalizeFirstCopiesCount, Effect.components])
    have rax : t.regValue .rax = 0 := post.writes.2
    have r14 : t.regValue .r14 = 0 :=
      (post.agrees.read (n := 64) (r := 14) (by cases v <;> simp [Loop.finalizeFirstEmptyEffect, Loop.finalizeFirstCopiesCount, Effect.components])).trans
        ((frameA.read (n := 64) (r := 14) (by simp)).trans _indexU)
    have r12 : t.regValue .r12 = 0 := by
      cases v
      all_goals first
      | exact post.writes.1
      | have h := (post.agrees.read (n := 64) (r := 12) (by simp [Loop.finalizeFirstEmptyEffect, Loop.finalizeFirstCopiesCount, Effect.components])).trans
          ((frameA.read (n := 64) (r := 12) (by simp)).trans _countReg)
        simp only [empty, BitVec.ofNat_eq_ofNat] at h
        exact h
    have r15 : t.regValue .r15 = 0 := by
      cases v
      all_goals first
      | exact post.writes.1
      | have h := (post.agrees.read (n := 64) (r := 15) (by simp [Loop.finalizeFirstEmptyEffect, Loop.finalizeFirstCopiesCount, Effect.components])).trans
          ((frameA.read (n := 64) (r := 15) (by simp)).trans _countReg)
        simp only [empty, BitVec.ofNat_eq_ofNat] at h
        exact h
    have countT : v.countValue (.finalizeIntoReset false) initial t = BitVec.ofNat 64 inputs.size := by
      rw [empty]
      cases v <;> first | exact r12 | exact r15
    have emptyBool : inputs.isEmpty = true := by simp [Array.isEmpty, empty]
    have arrayEmpty : inputs = #[] := Array.eq_empty_of_size_eq_zero empty
    refine ⟨t, .inl ⟨?_, ?_, countT, rax, r12, r14, r15⟩, ⟨_, (runU.trans runA).trans run⟩, (post.agrees.external (by cases v <;> simp [Loop.finalizeFirstEmptyEffect, Effect.components, Component.Covers])).trans ((frameA.external (by simp [Component.Covers])).trans memoryU)⟩
    · simpa only [arrayEmpty, message, Array.foldl_empty] using stateT
    · rw [emptyBool]
      have h := post.rip
      cases v <;> exact h
  · obtain ⟨t, stateT, localRun, memory⟩ := finalize_first_loop ctx state rip count countTruncated
      (Nat.pos_of_ne_zero empty)
    exact ⟨t, .inr stateT, localRun, memory⟩

set_option maxHeartbeats 1000000 in
theorem finalize_last_loop [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.finalizeIntoReset true))
    (state : Buffered v initial s ByteArray.empty (.finalizeIntoReset true))
    (rip : s.RIP = v.pc (ResetLayout.finalizeIntoResetInitializationEnds v)[1]! (.finalizeIntoReset true))
    (count : v.countValue (.finalizeIntoReset true) initial s = BitVec.ofNat 64 inputs.size)
    (positive : 0 < inputs.size) : ∃ t, LoopState v initial t inputs 0 (.finalizeIntoReset true) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  let site : Nat × BitVec 4 × BitVec 32 :=
    (resetBranchSites v)[2]!
  have member : site ∈ resetBranchSites v := by cases v <;> decide
  have entry : s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.1 := by
    cases v <;> exact rip
  obtain ⟨fuel, u, run, readyU, post⟩ := reset_branch member
    (supportedMachine_readyToStep state.machine) state.loaded entry outside
  have siteCount : (.reg (site.2.1.setWidth 5) : Operand 64).read s = BitVec.ofNat 64 inputs.size := by
    cases v <;> exact count
  have countNe : (.reg (site.2.1.setWidth 5) : Operand 64).read s ≠ 0 := by
    rw [siteCount]
    intro zero
    have eq : inputs.size % 2^64 = 0 := by simpa using congrArg BitVec.toNat zero
    have bound := ctx.count_bound
    omega
  have branchFrame : AgreesExcept [.flags, .rip] s u := post.agrees
  have stateU := Absorb.buffered_of_agrees ctx state run readyU branchFrame
    (by simp [Component.Covers]) (by simp)
  have entryU : u.RIP = Loop.resetLastPC v true := by
    have h := post.rip
    change u.RIP = (if (.reg (site.2.1.setWidth 5) : Operand 64).read s = 0 then _ else _) at h
    simp only [ite_eq_right countNe] at h
    cases v <;> exact h
  obtain ⟨fuelT, t, runT, readyT, _, postT⟩ :=
    Loop.reset_last_run (v := v) (returnBoundary initial) outside true u readyU
      (Loop.resetLast_code stateU.loaded true) entryU
  have stateT := Absorb.buffered_of_agrees ctx stateU runT readyT postT.agrees
    (by cases v <;> simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components, Component.Covers])
    (by cases v <;> simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components])
    (by cases v <;> simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components])
  have countT : v.countValue (.finalizeIntoReset true) initial t = BitVec.ofNat 64 inputs.size := by
    cases v with
    | sha384 =>
      exact (postT.agrees.read (n := 64) (r := 12) (by simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components])).trans
        ((branchFrame.read (n := 64) (r := 12) (by simp)).trans count)
    | sha512 =>
      exact (postT.agrees.read (n := 64) (r := 12) (by simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components])).trans
        ((branchFrame.read (n := 64) (r := 12) (by simp)).trans count)
    | sha512_224 =>
      exact (postT.agrees.read (n := 64) (r := 15) (by simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components])).trans
        ((branchFrame.read (n := 64) (r := 15) (by simp)).trans count)
    | sha512_256 =>
      exact (postT.agrees.read (n := 64) (r := 15) (by simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components])).trans
        ((branchFrame.read (n := 64) (r := 15) (by simp)).trans count)
  refine ⟨t, ?_, ⟨_, run.trans runT⟩, (postT.agrees.external (by cases v <;> simp [Loop.resetLastEffect, Loop.resetLastIndex, Loop.resetLastPointer, Effect.components, Component.Covers])).trans (branchFrame.external (by simp [Component.Covers]))⟩
  refine ⟨?_, ?_, ?_, ?_, positive, ?_, ?_, ?_, ?_⟩
  · simpa only [prefixMessage_zero] using stateT
  · have h := postT.rip
    cases v <;> exact h
  · have indexT : t.regValue .r14 = 0 := postT.writes.1
    cases v <;> exact indexT
  · cases v <;> exact countT
  · intro impossible
    cases impossible

  · intro impossible; cases impossible
  · have h := postT.writes.2
    cases v <;> exact h
  · intro second impossible; cases impossible

set_option maxHeartbeats 1000000 in
theorem finalize_last_dispatch [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.finalizeIntoReset true))
    (state : Buffered v initial s ByteArray.empty (.finalizeIntoReset true))
    (rip : s.RIP = v.pc (ResetLayout.finalizeIntoResetInitializationEnds v)[1]! (.finalizeIntoReset true))
    (count : v.countValue (.finalizeIntoReset true) initial s = BitVec.ofNat 64 inputs.size) :
    ∃ t, ((Buffered v initial t (message inputs) (.finalizeIntoReset true) ∧
      t.RIP = v.pc (v.dispatchOffset (.finalizeIntoReset true) inputs.isEmpty) (.finalizeIntoReset true) ∧ v.countValue (.finalizeIntoReset true) initial t = BitVec.ofNat 64 inputs.size) ∨ LoopState v initial t inputs 0 (.finalizeIntoReset true)) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  by_cases empty : inputs.size = 0
  · have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    let site : Nat × BitVec 4 × BitVec 32 :=
      (resetBranchSites v)[2]!
    have member : site ∈ resetBranchSites v := by cases v <;> decide
    have entry : s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.1 := by
      cases v <;> exact rip
    obtain ⟨fuel, t, run, readyT, post⟩ := reset_branch member
      (supportedMachine_readyToStep state.machine) state.loaded entry outside
    have branchFrame : AgreesExcept [.flags, .rip] s t := post.agrees
    have stateT := Absorb.buffered_of_agrees ctx state run readyT branchFrame
      (by simp [Component.Covers]) (by simp)
    have siteCount : (.reg (site.2.1.setWidth 5) : Operand 64).read s = BitVec.ofNat 64 inputs.size := by
      cases v <;> exact count
    have zero : (.reg (site.2.1.setWidth 5) : Operand 64).read s = 0 := by
      simpa [empty] using siteCount
    have emptyBool : inputs.isEmpty = true := by simp [Array.isEmpty, empty]
    have target : t.RIP = v.pc (v.dispatchOffset (.finalizeIntoReset true) inputs.isEmpty) (.finalizeIntoReset true) := by
      have h := post.rip
      change t.RIP = (if (.reg (site.2.1.setWidth 5) : Operand 64).read s = 0 then _ else _) at h
      simp only [zero, ite_true] at h
      rw [emptyBool]
      cases v <;> exact h
    have arrayEmpty : inputs = #[] := Array.eq_empty_of_size_eq_zero empty
    refine ⟨t, .inl ⟨?_, target, by cases v <;> first | exact (branchFrame.read (n := 64) (r := 12) (by simp)).trans count | exact (branchFrame.read (n := 64) (r := 15) (by simp)).trans count⟩, ⟨_, run⟩, branchFrame.external (by simp [Component.Covers])⟩
    simpa only [arrayEmpty, message, Array.foldl_empty] using stateT
  · obtain ⟨t, stateT, localRun, memory⟩ := finalize_last_loop ctx state rip count (Nat.pos_of_ne_zero empty)
    exact ⟨t, .inr stateT, localRun, memory⟩

set_option maxHeartbeats 1000000 in
theorem trait_loop [Bindings] {v : Variant} {second : Bool} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (state : Buffered v initial s ByteArray.empty (.traitFinalizeIntoReset second))
    (rip : s.RIP = Loop.traitLoopPC v second)
    (count : v.countValue (.traitFinalizeIntoReset second) initial s = BitVec.ofNat 64 inputs.size)
    (outputSaved : second = false →
      memLoad s.external (outputSavePointer initial (.traitFinalizeIntoReset second)) 64 = initial.regValue .rcx)
    (positive : 0 < inputs.size) :
    ∃ t, LoopState v initial t inputs 0 (.traitFinalizeIntoReset second) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside : BlockInProgram (Loop.traitLoopPC v second) 16 := by
    apply blockInProgram_of_textOffset
    cases second <;> cases v <;> decide
  obtain ⟨fuel, u, run, readyU, _, post⟩ := Loop.trait_clone_setup _ second
    (returnBoundary initial) outside inside s (supportedMachine_readyToStep state.machine)
    (Loop.traitClone_code state.loaded) rip
  have noMem : ∀ c ∈ (Loop.traitCloneEffect (Loop.traitLoopPC v second) second s).components,
      ∀ a, ¬ c.Covers a := by cases second <;> simp [Loop.traitCloneEffect, Effect.components, Component.Covers]
  have stateU := Absorb.buffered_of_agrees ctx state run readyU post.agrees noMem
    (by cases second <;> simp [Loop.traitCloneEffect, Effect.components])
    (by cases second <;> simp [Loop.traitCloneEffect, Effect.components])
    (keptFrameOutput := by
      intro h
      cases second
      · exact .inr (outputSaved rfl)
      · cases h)
  have memoryU : u.external = s.external := post.agrees.external noMem
  have insideT : BlockInProgram (Loop.traitLoopPC v second + 16) 9 := by
    have h := blockInProgram_of_textOffset (Loop.traitLoopOffset v second + 16) 9
      (by cases second <;> cases v <;> decide)
    simpa [Loop.traitLoopPC, BitVec.ofNat_add, BitVec.add_assoc] using h
  have target : InProgram (Loop.traitLoopPC v second + 16 + 9 +
      (Loop.traitLoopJump v second).signExtend 64) := by
    have h := inProgram_of_textOffset ((ResetLayout.traitFinalizeIntoReset v).textOffset +
      ((ResetLayout.traitFinalizeIntoReset v).traversals.map ResetLayout.Traversal.head)[if second then 1 else 0]!)
      (by cases second <;> cases v <;> decide)
    cases second <;> cases v <;> exact h
  obtain ⟨fuelT, t, runT, readyT, _, postT⟩ := Loop.memcpy_jump _ (if second then 5 else 13)
    (Loop.traitMemcpyDisplacement v second) (Loop.traitLoopJump v second)
    (returnBoundary initial) outside insideT target u readyU (Loop.traitMemcpy_code stateU.loaded) post.rip
  have noMemT : ∀ c ∈ (Loop.memcpyJumpEffect (Loop.traitLoopPC v second + 16)
      (if second then 5 else 13) (Loop.traitMemcpyDisplacement v second) (Loop.traitLoopJump v second) u).components,
      ∀ a, ¬ c.Covers a := by cases second <;> simp [Loop.memcpyJumpEffect, Effect.components, Component.Covers]
  have stateT := Absorb.buffered_of_agrees ctx stateU runT readyT postT.agrees noMemT
    (by cases second <;> simp [Loop.memcpyJumpEffect, Effect.components])
    (by cases second <;> simp [Loop.memcpyJumpEffect, Effect.components])
    (keptFrameOutput := by
      intro h
      cases second
      · exact .inr (by simpa only [memoryU] using outputSaved rfl)
      · cases h)
  have memoryT : t.external = s.external := (postT.agrees.external noMemT).trans memoryU
  have indexU : u.regValue .r15 = 0 := post.writes.1
  have indexT : t.regValue .r15 = 0 :=
    (postT.agrees.read (n := 64) (r := 15) (by cases second <;>
      simp [Loop.memcpyJumpEffect, Effect.components])).trans indexU
  have active : rspOf s + 32 = bufferPointer initial (.traitFinalizeIntoReset second)
      (Form.activeMemory (.traitFinalizeIntoReset second)) := by
    change stackPtr s + 32 = stackPtr initial - 616
    rw [state.rsp]
    simp [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have persistent : rspOf s + 256 = bufferPointer initial (.traitFinalizeIntoReset second) := by
    change stackPtr s + 256 = stackPtr initial - 392
    rw [state.rsp]
    simp [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  refine ⟨t, ?_, ⟨_, run.trans runT⟩, memoryT⟩
  refine ⟨?_, ?_, ?_, ?_, positive, ?_, ?_, ?_, ?_⟩
  · simpa only [prefixMessage_zero] using stateT
  · have h := postT.rip
    cases second <;> cases v <;> exact h
  · cases second <;> cases v <;> exact indexT
  · cases second <;> cases v <;>
      change memLoad t.external (stackPtr initial - 640) 64 = _
    all_goals (rw [memoryT]; exact count)
  · intro h
    cases second
    · simpa only [memoryT] using outputSaved rfl
    · cases h
  · intro h; cases h
  · have h := postT.writes
    cases second <;> cases v <;> exact h
  · intro second' eq
    have same : second = second' := by cases eq; rfl
    subst second'
    constructor
    · exact ((postT.agrees.read (n := 64) (r := 3) (by cases second <;>
        simp [Loop.memcpyJumpEffect, Effect.components])).trans post.writes.2.1).trans active
    · cases second
      · exact ((postT.agrees.read (n := 64) (r := 12) (by
          simp [Loop.memcpyJumpEffect, Effect.components])).trans post.writes.2.2).trans persistent
      · exact ((postT.agrees.read (n := 64) (r := 14) (by
          simp [Loop.memcpyJumpEffect, Effect.components])).trans post.writes.2.2).trans persistent

set_option maxHeartbeats 1000000 in
theorem trait_buffered_after_store [Bindings] {v : Variant} {initial s t : RamState}
    {inputs : Array Input} {slot fuel : Nat}
    (ctx : Context v initial inputs (.traitFinalizeIntoReset false))
    (state : Buffered v initial s ByteArray.empty (.traitFinalizeIntoReset false))
    (slotAllowed : slot = 640 ∨ slot = 408)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 slot) 8, .rip] s t)
    (output : memLoad t.external (stackPtr initial - 408) 64 = initial.regValue .rcx ∨
      t.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx) :
    Buffered v initial t ByteArray.empty (.traitFinalizeIntoReset false) := by
  have apartCover (offset len : Nat) (small : len ≤ 64)
      (apart : OffsetsApart (-(BitVec.ofNat 64 offset)) len (-(BitVec.ofNat 64 slot)) 8) :
      ∀ a, (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a →
        ¬ (Component.mem (stackPtr initial - BitVec.ofNat 64 slot) 8).Covers a := by
    intro a ⟨i, hi, heq⟩ ⟨j, hj, eq⟩
    subst a
    exact OffsetsApart.ne apart (stackPtr initial) hi hj (by omega)
      (by simp only [BitVec.sub_eq_add_neg] at eq; exact eq)
  have bytes (offset len : Nat) (small : len ≤ 64)
      (apart : OffsetsApart (-(BitVec.ofNat 64 offset)) len (-(BitVec.ofNat 64 slot)) 8) :
      ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    apply frame.memory
    intro c member covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact apartCover offset len small apart _ ⟨i, hi, rfl⟩ covered
    · exact covered
  have word (offset : Nat)
      (apart : OffsetsApart (-(BitVec.ofNat 64 offset)) 8 (-(BitVec.ofNat 64 slot)) 8) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 :=
    by
      apply memLoad_congr
      intro i hi
      simpa only [memByte, PhysicalMemory.read] using congrArg (fun x : Option UInt8 => x.getD 0) (bytes offset 8 (by decide) apart i hi)
  have writes : WritesWithin [.mem (stackPtr initial - BitVec.ofNat 64 slot) 8, .rip]
      (v.writeRegions initial (.traitFinalizeIntoReset false)) := by
    intro c member a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · refine ⟨Stack.region initial (v.routine (.traitFinalizeIntoReset false)).minStackBytes,
        by apply Vector.mem_iff_getElem.mpr; exact ⟨2, by decide, rfl⟩, ?_⟩
      exact stackRegion_contains_sub ctx.stack.2.2.1
        (by rcases slotAllowed with rfl | rfl <;> cases v <;> decide)
        (by rcases slotAllowed with rfl | rfl <;> cases v <;> decide) covered
    · exact covered.elim
  have current := Absorb.State.of_agrees state.toState ctx run ready frame writes (by simp)
    (by
      intro c member a covered
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · apply apartCover 48 56 (by decide) _ a covered
        rcases slotAllowed with rfl | rfl <;> unfold OffsetsApart <;> decide +kernel
      · intro h; exact h)
    (by simp)
  have preserved : Preserved v initial t (.traitFinalizeIntoReset false) := by
    refine ⟨current, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rcases output with h | h
        · exact .inl h
        · exact .inr ⟨rfl, h⟩
      · exact (word 400 (by rcases slotAllowed with rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)).trans state.outputPointer.2
    · exact (word 632 (by rcases slotAllowed with rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)).trans state.pointerTable
    · exact (word 624 (by rcases slotAllowed with rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)).trans state.lengthTable
  refine ⟨preserved, ⟨state.hashWords.1, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Common.Memory.loadBytes_congr (before := s.external) (after := t.external) (by
      intro j hj
      change t.external[(stackPtr initial - 264 + BitVec.ofNat 64 (8 * i)) + BitVec.ofNat 64 j]? = s.external[(stackPtr initial - 264 + BitVec.ofNat 64 (8 * i)) + BitVec.ofNat 64 j]?
      simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact bytes 264 64 (by decide) (by rcases slotAllowed with rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) (8 * i + j) (by omega))]
    exact state.hashWords.2 i hi
  · refine ⟨state.tailBytes.1, ?_⟩
    intro i
    have bound := i.isLt
    simp [tailData] at bound
  · change t.external[stackPtr initial - 265]? = _
    have same := bytes 265 1 (by decide) (by rcases slotAllowed with rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) 0 (by decide)
    have eq : t.external[stackPtr initial - 265]? = s.external[stackPtr initial - 265]? := by simpa using same
    exact eq.trans state.tailLength
  · exact (word 200 (by rcases slotAllowed with rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)).trans state.blockCount
  · exact (word 192 (by rcases slotAllowed with rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)).trans state.blockCountHigh

set_option maxHeartbeats 1000000 in
theorem trait_store [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs (.traitFinalizeIntoReset false))
    (state : Buffered v initial s ByteArray.empty (.traitFinalizeIntoReset false))
    (output : Bool) (rip : s.RIP = Loop.traitSavePC v output)
    (source : s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx) :
    ∃ t, Buffered v initial t ByteArray.empty (.traitFinalizeIntoReset false) ∧
      t.RIP = Loop.traitSavePC v output + (if output then (8 : BitVec 64) else 5) ∧
      AgreesExcept [.mem (stackPtr initial - (if output then 408 else 640)) 8, .rip] s t ∧
      memLoad t.external (stackPtr initial - (if output then 408 else 640)) 64 =
        (if output then initial.regValue .rcx else s.regValue .rsi) ∧ Advances (returnBoundary initial) 1 s t := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside : BlockInProgram (Loop.traitSavePC v output) (if output then 8 else 5) := by
    apply blockInProgram_of_textOffset
    cases output <;> cases v <;> decide
  have avoidsPages : (Stack.region initial (v.routine (.traitFinalizeIntoReset false)).minStackBytes).Avoids InPageTables := by
    intro a ha hp
    exact (ctx.separation.2 _ (by change _ ∈ [_, _, _]; simp)).2 a ha (.inr hp)
  have avoidsProgram : (Stack.region initial (v.routine (.traitFinalizeIntoReset false)).minStackBytes).Avoids InProgram := by
    intro a ha hp
    exact (ctx.separation.2 _ (by change _ ∈ [_, _, _]; simp)).2 a ha (.inl hp)
  have writable : MemWritable s (rspOf s + (if output then 240 else 8)) 8 := by
    change MemWritable s (stackPtr s + _) 8
    rw [state.rsp]
    cases output <;> apply stack_frame_writable (frame := 648) ctx.stack (by cases v <;> decide) avoidsPages state.allocated
    all_goals first | decide | (intro j hj; exact inside j (by omega))
  have apart : RangeApart (rspOf s + (if output then 240 else 8)) 8
      (Loop.traitSavePC v output) (if output then 8 else 5) := by
    change RangeApart (stackPtr s + _) 8 _ _
    rw [state.rsp]
    cases output <;> apply stack_frame_codeApart (frame := 648) ctx.stack (by cases v <;> decide) avoidsProgram
    all_goals first | decide | (intro j hj; exact inside j (by omega))
  have pre : Common.Instructions.CrossPageStore.Pre (Loop.traitSavePC v output)
      (Loop.traitSaveBytes v output).length
      (storeAddrAt (Loop.traitSavePC v output) (.sib 4 none 0 (Loop.traitSaveSlot output))
        (Loop.traitSaveBytes v output).length) 8 s := by
    refine ⟨rip, ?_, ?_⟩
    · apply Common.Instructions.CrossPageStore.Writable.of_memWritable
      cases output <;> simpa [Loop.traitSaveSlot, AddrMode.addr, AddrMode.reg64, Disp.value, AddrMode.tail, Disp.bytes, rspOf] using writable
    · cases output <;> cases v <;> simpa [Loop.traitSaveSlot, Loop.traitSaveBytes,
        Loop.traitSaveSource, encodeMovM64R64, AddrMode.addr, AddrMode.reg64, Disp.value, AddrMode.tail, Disp.bytes, rspOf] using apart
  obtain ⟨t, run, readyT, post⟩ := (Common.SHA256.Absorb.Blocks.spill_step
    (Loop.traitSavePC v output) (Loop.traitSaveSource v output) (Loop.traitSaveSlot output)
    (by cases output <;> decide)).advances (supportedMachine_readyToStep state.machine)
    (Loop.traitSave_code state.loaded) pre (by
      apply boundary_ne_program outside
      have h := inside (if output then 8 else 5) (Nat.le_refl _)
      cases output <;> simpa [movM64R64Effect, storeEffect, Loop.traitSaveSlot, AddrMode.tail, Disp.bytes] using h)
  have addr : rspOf s + (if output then 240 else 8) =
      stackPtr initial - (if output then 408 else 640) := by
    change stackPtr s + _ = _
    rw [state.rsp]
    cases output <;> simp [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have frame : AgreesExcept [.mem (stackPtr initial - (if output then 408 else 640)) 8, .rip] s t := by
    rw [← addr]
    have h := post.agrees
    cases output <;> simp only [Bool.false_eq_true, ite_false, ite_true] at addr <;> simpa [movM64R64Effect, storeEffect, Loop.traitSaveSlot,
      Effect.components, AddrMode.addr, AddrMode.reg64, Disp.value, AddrMode.tail, Disp.bytes, rspOf, Write.AllHold, Operand.read, X86.State.regValue, gprIndex, Syntax.Reg.fin] using h
  have written : memLoad t.external (stackPtr initial - (if output then 408 else 640)) 64 =
        (if output then initial.regValue .rcx else s.regValue .rsi) := by
    rw [← addr]
    have h := post.writes
    cases output
    · simp only [Bool.false_eq_true, ite_false] at addr
      simp only [movM64R64Effect, storeEffect, Loop.traitSaveSlot, Loop.traitSaveSource,
        AddrMode.addr, AddrMode.reg64, Disp.value, AddrMode.tail, Disp.bytes, Write.AllHold, Operand.read, gprIndex] at h
      exact h
    · simp only [ite_true] at addr
      have eq : memLoad t.external (rspOf s + 240) 64 =
          s.regValue (if v = .sha512 then .r13 else .rbp) := by
        cases v <;> simp only [movM64R64Effect, storeEffect, Loop.traitSaveSlot, Loop.traitSaveSource,
          AddrMode.addr, AddrMode.reg64, Disp.value, AddrMode.tail, Disp.bytes, Write.AllHold, Operand.read, gprIndex] at h <;> exact h
      exact eq.trans source
  have stateT := trait_buffered_after_store ctx state
    (slot := if output then 408 else 640) (by cases output <;> simp) run readyT
    (by cases output <;> exact frame) (by
      cases output
      · right
        have preserved := frame.read (n := 64) (r := if v = .sha512 then 13 else 5) (by simp)
        cases v <;> exact preserved.trans source
      · exact .inl written)
  refine ⟨t, stateT, ?_, frame, written, run⟩
  have h := post.rip
  cases output <;> simpa [movM64R64Effect, storeEffect, Loop.traitSaveSlot, AddrMode.tail, Disp.bytes] using h

set_option maxHeartbeats 1000000 in
theorem trait_last_dispatch [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.traitFinalizeIntoReset true))
    (state : Buffered v initial s ByteArray.empty (.traitFinalizeIntoReset true))
    (rip : s.RIP = v.pc (ResetLayout.traitFinalizeIntoResetInitializationEnds v)[1]! (.traitFinalizeIntoReset true))
    (count : v.countValue (.traitFinalizeIntoReset true) initial s = BitVec.ofNat 64 inputs.size) :
    ∃ t, ((Buffered v initial t (message inputs) (.traitFinalizeIntoReset true) ∧
      t.RIP = v.pc (v.dispatchOffset (.traitFinalizeIntoReset true) inputs.isEmpty) (.traitFinalizeIntoReset true) ∧ v.countValue (.traitFinalizeIntoReset true) initial t = BitVec.ofNat 64 inputs.size) ∨ LoopState v initial t inputs 0 (.traitFinalizeIntoReset true)) ∧ (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have entry : s.RIP = Extracted.textAddress + BitVec.ofNat 64 (traitSecondBranchOffset v) := by
    cases v <;> exact rip
  have address : rspOf s + 8 = stackPtr initial - 640 := by
    change stackPtr s + 8 = _
    rw [state.rsp]
    simp [Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have readable : MemReadable s (rspOf s + 8) 8 := by
    rw [address]
    exact Common.Encoding.Serialize.readable_of_grow
      (stack_valid_sub_readable ctx.stack (by cases v <;> decide) (by decide)) state.allocated
  obtain ⟨fuel, u, run, readyU, post⟩ := trait_second_branch
    (supportedMachine_readyToStep state.machine) state.loaded entry readable outside
  have frame : AgreesExcept [.flags, .rip] s u := post.agrees
  have stateU := Absorb.buffered_of_agrees ctx state run readyU frame
    (by simp [Component.Covers]) (by simp)
  have memory : u.external = s.external := frame.external (by simp [Component.Covers])
  have countS : memLoad s.external (rspOf s + 8) 64 = BitVec.ofNat 64 inputs.size := by
    rw [address]
    cases v <;> exact count
  by_cases empty : inputs.size = 0
  · have zero : memLoad s.external (rspOf s + 8) 64 = 0 := by simpa [empty] using countS
    have target := post.rip
    change u.RIP = (if memLoad s.external (rspOf s + 8) 64 = 0 then _ else _) at target
    simp only [zero, ite_true] at target
    have emptyBool : inputs.isEmpty = true := by simp [Array.isEmpty, empty]
    refine ⟨u, .inl ⟨?_, ?_, ?_⟩, ⟨_, run⟩, memory⟩
    · have arrayEmpty := Array.eq_empty_of_size_eq_zero empty
      simpa only [arrayEmpty, message, Array.foldl_empty] using stateU
    · rw [emptyBool]
      cases v <;> exact target
    · cases v <;> change memLoad u.external (stackPtr initial - 640) 64 = _
      all_goals (rw [memory]; exact count)
  · have nonzero : memLoad s.external (rspOf s + 8) 64 ≠ 0 := by
      rw [countS]
      intro zero
      have eq : inputs.size % 2^64 = 0 := by simpa using congrArg BitVec.toNat zero
      have bound := ctx.count_bound
      omega
    have target := post.rip
    change u.RIP = (if memLoad s.external (rspOf s + 8) 64 = 0 then _ else _) at target
    simp only [ite_eq_right nonzero] at target
    have loopEntry : u.RIP = Loop.traitLoopPC v true := by cases v <;> exact target
    have countU : v.countValue (.traitFinalizeIntoReset true) initial u = BitVec.ofNat 64 inputs.size := by
      cases v <;> change memLoad u.external (stackPtr initial - 640) 64 = _
      all_goals (rw [memory]; exact count)
    obtain ⟨t, result, ⟨fuelT, runT⟩, memoryT⟩ := trait_loop ctx stateU loopEntry countU (by intro h; cases h)
      (Nat.pos_of_ne_zero empty)
    exact ⟨t, .inr result, ⟨_, run.trans runT⟩, memoryT.trans memory⟩

set_option maxHeartbeats 1000000 in
theorem trait_first_dispatch [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.traitFinalizeIntoReset false))
    (state : Buffered v initial s ByteArray.empty (.traitFinalizeIntoReset false))
    (rip : s.RIP = Loop.traitSavePC v false)
    (count : s.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (source : s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx) :
    ∃ t, ((Buffered v initial t (message inputs) (.traitFinalizeIntoReset false) ∧
      t.RIP = v.pc (v.dispatchOffset (.traitFinalizeIntoReset false) inputs.isEmpty) (.traitFinalizeIntoReset false) ∧
      v.countValue (.traitFinalizeIntoReset false) initial t = BitVec.ofNat 64 inputs.size ∧
      t.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx ∧ inputs.isEmpty = true) ∨
        LoopState v initial t inputs 0 (.traitFinalizeIntoReset false)) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine (.traitFinalizeIntoReset false)).minStackBytes] := by
  have storeFrame {a b : RamState} {slot : Nat} (bound : slot = 640 ∨ slot = 408)
      (h : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 slot) 8, .rip] a b) :
      MemoryWriteFrame a b #v[Stack.region initial (v.routine (.traitFinalizeIntoReset false)).minStackBytes] := by
    apply h.memoryWriteFrame
    intro c hc address covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨_, by apply Vector.mem_iff_getElem.mpr; exact ⟨0, by decide, rfl⟩, ?_⟩
      exact stackRegion_contains_sub ctx.stack.2.2.1
        (by rcases bound with rfl | rfl <;> cases v <;> decide)
        (by rcases bound with rfl | rfl <;> decide) covered
    · exact covered.elim
  obtain ⟨u, stateU, ripU, frameU, writtenU, runU⟩ := trait_store ctx state false rip source
  have countU : u.regValue .rsi = BitVec.ofNat 64 inputs.size :=
    (frameU.read (n := 64) (r := 6) (by simp)).trans count
  have sourceU : u.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx := by
    have h := frameU.read (n := 64) (r := if v = .sha512 then 13 else 5) (by simp)
    cases v <;> exact h.trans source
  let site : Nat × BitVec 4 × BitVec 32 := (resetBranchSites v)[3]!
  have member : site ∈ resetBranchSites v := by cases v <;> decide
  have entry : u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.1 := by cases v <;> exact ripU
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  obtain ⟨fuelA, a, runA, readyA, postA⟩ := reset_branch member
    (supportedMachine_readyToStep stateU.machine) stateU.loaded entry outside
  have frameA : AgreesExcept [.flags, .rip] u a := postA.agrees
  have stateA := Absorb.buffered_of_agrees ctx stateU runA readyA frameA
    (by simp [Component.Covers]) (by simp)
  have memoryA : a.external = u.external := frameA.external (by simp [Component.Covers])
  have narrowA : MemoryWriteFrame s a #v[Stack.region initial (v.routine (.traitFinalizeIntoReset false)).minStackBytes] := by
    have h := storeFrame (slot := 640) (.inl rfl) frameU
    simpa only [MemoryWriteFrame, memoryA] using h
  have branchRip := postA.rip
  have selected : (.reg (site.2.1.setWidth 5) : Operand 64).read u = u.regValue .rsi := by cases v <;> rfl
  change a.RIP = (if (.reg (site.2.1.setWidth 5) : Operand 64).read u = 0 then _ else _) at branchRip
  rw [selected, countU] at branchRip
  by_cases empty : inputs.size = 0
  · simp only [empty, BitVec.ofNat_eq_ofNat, ite_true] at branchRip
    have emptyBool : inputs.isEmpty = true := by simp [Array.isEmpty, empty]
    refine ⟨a, .inl ⟨?_, ?_, ?_, ?_, emptyBool⟩, ⟨_, runU.trans runA⟩, narrowA⟩
    · have eq := Array.eq_empty_of_size_eq_zero empty
      simpa only [eq, message, Array.foldl_empty] using stateA
    · rw [emptyBool]
      cases v <;> exact branchRip
    · cases v <;> change memLoad a.external (stackPtr initial - 640) 64 = _
      all_goals (rw [memoryA]; exact writtenU.trans count)
    · have h := frameA.read (n := 64) (r := if v = .sha512 then 13 else 5) (by simp)
      cases v <;> exact h.trans sourceU
  · have nz : BitVec.ofNat 64 inputs.size ≠ 0 := by
      intro zero
      have eq : inputs.size % 2^64 = 0 := by simpa using congrArg BitVec.toNat zero
      have bound := ctx.count_bound
      omega
    simp only [ite_eq_right nz] at branchRip
    have outputEntry : a.RIP = Loop.traitSavePC v true := by cases v <;> exact branchRip
    have sourceA : a.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx := by
      have h := frameA.read (n := 64) (r := if v = .sha512 then 13 else 5) (by simp)
      cases v <;> exact h.trans sourceU
    obtain ⟨b, stateB, ripB, frameB, outputB, runB⟩ := trait_store ctx stateA true outputEntry sourceA
    have countMemory : memLoad b.external (stackPtr initial - 640) 64 = memLoad a.external (stackPtr initial - 640) 64 := by
      apply memLoad_congr
      intro i hi
      have bytes := frameB.memory (stackPtr initial - 640 + BitVec.ofNat 64 i) (by
        intro c hc covered
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · obtain ⟨j, hj, eq⟩ := covered
          exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel : OffsetsApart (-640#64) 8 (-408#64) 8)
            (stackPtr initial) hi hj (by decide) (by simp only [BitVec.sub_eq_add_neg, ite_true] at eq; exact eq)
        · exact covered)
      simpa only [memByte, PhysicalMemory.read] using congrArg (fun x : Option UInt8 => x.getD 0) bytes
    have countB : v.countValue (.traitFinalizeIntoReset false) initial b = BitVec.ofNat 64 inputs.size := by
      cases v <;> change memLoad b.external (stackPtr initial - 640) 64 = _
      all_goals (rw [countMemory, memoryA]; exact writtenU.trans count)
    have entryB : b.RIP = Loop.traitLoopPC v false := by cases v <;> exact ripB
    obtain ⟨t, loop, ⟨fuelT, runT⟩, memoryT⟩ := trait_loop ctx stateB entryB countB
      (by intro _; exact outputB) (Nat.pos_of_ne_zero empty)
    have narrowB := memoryWriteFrame_trans narrowA (storeFrame (slot := 408) (.inr rfl) frameB)
    refine ⟨t, .inr loop, ⟨_, ((runU.trans runA).trans runB).trans runT⟩, ?_⟩
    simpa only [MemoryWriteFrame, memoryT] using narrowB

end Sha2.Proofs.Wrapper512.Dispatch
