import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Frame
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Epilogue

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult memoryRegion_contains_add stack_region_end supportedMachine_of_ready_agrees)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field.SquareRoot.Multiply
open P256.Proofs.Program
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem saved_word_inside [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (pre : CalleePre s boundary entry 32 32 160)
    {offset i : Nat} (ho : offset ≤ 48) (hi : i < 8) :
    (Stack.region s 160).Contains
      (stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat := by
  apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
  · rw [stack_sub_toNat pre.stack (by omega)]
    change (stackPtr s).toNat-160 ≤ (stackPtr s).toNat-offset
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack (by omega)]
    have := (stack_bounds pre.stack).1
    omega

theorem saved_word_preserved [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (pre : CalleePre s boundary entry 32 32 160)
    (rsp : stackPtr t = stackPtr s-160#64) (rdi : t.regValue .rdi = s.regValue .rdi)
    (ag : AgreesExcept (Reduction.components t) t u) {offset : Nat} (ho : offset ≤ 48) :
    memLoad u.external (stackPtr s-BitVec.ofNat 64 offset) 64 =
      memLoad t.external (stackPtr s-BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  apply ag.memory
  intro c hc ha
  simp only [Reduction.components, Reduction.scratchComponents, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact ha.elim
  · rw [rsp] at ha
    obtain ⟨j, hj, he⟩ := ha
    have hb : stackPtr s-BitVec.ofNat 64 offset =
        stackPtr s-160#64+BitVec.ofNat 64 (160-offset) := by
      have h := scratch_address s (offset := 160-offset) (by omega)
      rw [Nat.sub_sub_self (by omega : offset ≤ 160)] at h
      exact h.symm
    have hap := RangeApart.offsets (stackPtr s-160#64) (a := 0) (len := 112)
      (b := 160-offset) (count := 8) (by decide) (by omega) (by omega)
    have hn := hap j hj i hi
    rw [BitVec.add_zero, ← hb] at hn
    exact hn he.symm
  · rw [rdi] at ha
    obtain ⟨j, hj, he⟩ := ha
    have hout := memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hj
    have hstack := saved_word_inside pre ho hi
    rw [he] at hstack
    exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hout hstack

theorem epilogue_pre_of_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (pre : CalleePre s boundary entry 32 32 160)
    (start : AgreesExcept (prologueComponents s) s t)
    (rsp : stackPtr t = stackPtr s-160#64) (mem : t.external = savedMemory s)
    (ag : AgreesExcept (Reduction.components t) t u)
    (ready : ReadyToStep u) (loaded : ProgramLoaded u) (rip : u.RIP = entry+0x5ab#64) :
    EpiloguePre s u boundary entry := by
  have rdi : t.regValue .rdi = s.regValue .rdi := start.read (r := 7) (n := 64) (by simp [prologueComponents])
  refine ⟨pre, ready, loaded, rip, (Reduction.components_rsp ag).trans rsp,
    fun a h => ag.grow a (start.grow a h), ?_, ?_⟩
  · intro item hitem
    have ho : item.2 ≤ 48 := by
      simp only [P256.Proofs.Common.Encoding.Serialize.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hitem
      rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [saved_word_preserved pre rsp rdi ag ho, mem]
    exact savedMemory_registers s item hitem
  · have h := saved_word_preserved pre rsp rdi ag (offset := 0) (by decide)
    rw [BitVec.sub_zero, mem, savedMemory_return] at h
    exact h

theorem epilogue_frame {s t u : RamState} (ag : AgreesExcept epilogueComponents t u) :
    AgreesExcept (frame s) t u := by
  apply ag.mono
  intro c hc
  simp only [epilogueComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [frame, List.range_succ]

theorem finish_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (he : Entry entry) (pre : EpiloguePre s t boundary entry)
    (run : ∃ fuel, Advances boundary fuel s t) (ag : AgreesExcept (frame s) s t) :
    ∃ u, CalleeResult s u boundary 32 160 ∧ u.external = t.external := by
  obtain ⟨u, endrun, ready, endframe, rip, rsp, regs⟩ := epilogue_correct he pre
  have fr := ag.trans (epilogue_frame (s := s) endframe)
  have fr' : AgreesExcept (frame s) s u := fr.mono (by simp)
  have ext : u.external = t.external := endframe.external (by simp [epilogueComponents, Component.Covers])
  refine ⟨u, {
    execution := ?_
    rip := rip
    rsp := rsp
    bindingsSupported := bindingsSupported_of_ready_agrees pre.pre.bindingsSupported ready fr'
    machine := supportedMachine_of_ready_agrees pre.pre.machine ready fr'
    calleeSaved := regs
    directionFlag := fr'.directionFlagClear (by simp [frame]) pre.pre.directionFlag
    mxcsr := fr'.mxcsr (by simp [frame])
    fp87 := fr'.fcw (by simp [frame])
    frame := fr'.memoryWriteFrame (frame_within pre.pre)
    loaded := loaded_of_frame pre.pre fr'
    allocated := fr'.grow
  }, ext⟩
  obtain ⟨fuel, run⟩ := run
  exact ⟨fuel+9, run.trans endrun⟩

end P256.Proofs.Sec1.SquareRoot.Montgomery
