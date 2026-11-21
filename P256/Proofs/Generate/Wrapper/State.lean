import P256.Proofs.Generate.Wrapper.Interface
import P256.Proofs.Program.ScalarFrame.Work
import P256.Proofs.Program.State
import P256.Proofs.Program.Call

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

abbrev workRegion (initial : RamState) := ScalarFrame.Work.region initial 4024 24

theorem work_contains {initial : RamState}
    (stack : Stack.Valid initial 4024) {offset len : Nat} {a : BitVec 64}
    (bound : offset ≤ 4024) (below : len+24 ≤ offset)
    (covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion initial).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bounds := stack_bounds stack
  have low := stack_sub_toNat stack bound
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
    Nat.mod_eq_of_lt (by rw [low]; omega), low]
  change (stackPtr initial).toNat - 4024 ≤ _ ∧
    _ < (stackPtr initial).toNat - 4024 + (4024-24)
  constructor <;> omega

theorem work_frame {initial s t : RamState}
    (stack : Stack.Valid initial 4024)
    (memory : MemoryWriteFrame s t #v[workRegion initial]) :
    MemoryWriteFrame s t (wrapperRegions signingKeyGenerateFromRng initial) := by
  intro a ha
  apply memory a
  intro region hr hin
  have he : region = workRegion initial := by simpa using hr
  subst region
  apply ha (callStack signingKeyGenerateFromRng initial) (by simp [wrapperRegions])
  apply stack_contains_callStack
  have bounds := stack_bounds stack
  change (stackPtr initial).toNat - 4024 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 4024 + (4024 - 24) at hin
  change (stackPtr initial).toNat - 4024 ≤ a.toNat ∧
    a.toNat < (Stack.region initial 4024).start + (Stack.region initial 4024).size
  rw [stack_region_end]
  constructor <;> omega

theorem work_read {initial s t : RamState}
    (stack : Stack.Valid initial 4024)
    (memory : MemoryWriteFrame s t #v[workRegion initial])
    {offset : Nat} (bound : offset ≤ 24) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
  have bounds := stack_bounds stack
  have low := stack_sub_toNat stack (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [memory _]
  intro region hr hin
  have he : region = workRegion initial := by simpa using hr
  subst region
  change (stackPtr initial).toNat - 4024 ≤ _ ∧
    (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
      (stackPtr initial).toNat - 4024 + (4024 - 24) at hin
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, low] at hin
  have iBound : i < 8 := hi
  omega

theorem work_frame_regions {initial s t : RamState}
    (stack : Stack.Valid initial 4024)
    (memory : MemoryWriteFrame s t #v[workRegion initial]) (written : Option MemoryRegion) :
    MemoryWriteFrame s t (stateRegions initial written).2 := by
  intro a ha
  apply work_frame stack memory a
  intro r hr hin
  apply ha r ?_ hin
  have cases : r = allocatorStateRegion ∨ r = randomSourceRegion ∨
      r = callStack signingKeyGenerateFromRng initial := by simpa [wrapperRegions] using hr
  cases written with
  | none => exact hr
  | some region =>
    change r ∈ (#v[region,allocatorStateRegion,randomSourceRegion,
      callStack signingKeyGenerateFromRng initial] : Vector MemoryRegion 4)
    simpa using Or.inr cases

theorem work_loaded [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (loaded : ProgramLoaded s) (memory : MemoryWriteFrame s t #v[workRegion initial]) :
    ProgramLoaded t := by
  intro a b hb
  rw [work_frame call.stackAvailable.1 memory a]
  · exact loaded a b hb
  · intro r hr hin
    have member : r ∈ #v[heapRegion signingKeyGenerateFromRng initial,allocatorStateRegion,
        randomSourceRegion,callStack signingKeyGenerateFromRng initial] := by
      simp_all [wrapperRegions]
    exact (call.separation.2 r member).2 a hin (.inl ⟨b,hb⟩)

theorem State.after_effect [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input} {offset nextOffset fuel : Nat} {cs : List Component} {written : Option MemoryRegion}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (state : State initial s offset written)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t)
    (writes : WritesWithin cs #v[workRegion initial])
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 nextOffset)
    (kept : ∀ r ∈ [14,3,5,12,13], Component.reg r ∉ cs)
    (df : Component.df ∉ cs) : State initial t nextOffset written := by
  have memory := agrees.memoryWriteFrame writes
  have total := memoryWriteFrame_trans state.frame (work_frame_regions call.stackAvailable.1 memory written)
  obtain ⟨n, previous⟩ := state.execution
  refine ⟨⟨n+fuel, previous.trans run⟩,
    bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,
    work_loaded call state.loaded memory,
    agrees.directionFlagClear df state.directionFlag,
    rsp,
    (agrees.read (n := 64) (kept 14 (by simp))).trans state.output,
    (agrees.read (n := 64) (kept 3 (by simp))).trans state.capacity,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedRbx,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR14,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR15,
    ?_, ?_, fun a ha => agrees.grow a (state.allocated a ha), total⟩
  · have h := work_read call.stackAvailable.1 memory (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (agrees.read (n := 64) (kept 5 (by simp))).trans (state.otherRegisters .rbp (by simp))
    · exact (agrees.read (n := 64) (kept 12 (by simp))).trans (state.otherRegisters .r12 (by simp))
    · exact (agrees.read (n := 64) (kept 13 (by simp))).trans (state.otherRegisters .r13 (by simp))

theorem State.call_rel32 [Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input} {offset : Nat} {written : Option MemoryRegion}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (state : State initial s offset written) (outside : ¬ InProgram (returnBoundary initial).rip)
    (codeOffset : Nat) (disp : BitVec 32)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (capacity : offset+8 ≤ 4024) (below : 24 ≤ offset) (aligned : (offset+8)%8 = 0)
    (size : codeOffset+5 ≤ 118431)
    (bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (target : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
      5 (disp.signExtend 64))) :
    ∃ t, State initial t (offset+8) written ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
        5 (disp.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 codeOffset+5) s).Holds s t ∧
      t.external = memStore s.external (stackPtr initial - BitVec.ofNat 64 (offset+8))
        (Extracted.textAddress + BitVec.ofNat 64 codeOffset+5) := by
  obtain ⟨t,run,ready,_,effect,memory⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids call) outside (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated offset codeOffset disp state.rsp rip capacity aligned size bytes target
  have address : pushAddr s = stackPtr initial - BitVec.ofNat 64 (offset+8) := by
    rw [pushAddr,state.rsp,BitVec.sub_sub,BitVec.ofNat_add]
    rfl
  refine ⟨t,state.after_effect call run ready effect.agrees ?_ ?_ ?_ ?_,effect,memory⟩
  · intro c hc a ha
    simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨workRegion initial,by simp,?_⟩
      rw [address] at ha
      exact work_contains call.stackAvailable.1 capacity (by omega) ha
    · exact ha.elim
  · exact effect.writes.1.trans address
  · simp [pushEffect_components]
  · simp [pushEffect_components]


end P256.Proofs.Generate.Wrapper
