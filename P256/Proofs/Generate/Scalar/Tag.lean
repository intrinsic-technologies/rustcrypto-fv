import P256.Proofs.Generate.Scalar.Output
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem output_tag [Bindings] {s t : RamState} {boundary : ReturnBoundary} {value : Nat} {valid : Bool}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x112fba)
    (output : t.regValue .rbx = s.regValue .rdi)
    (flag : t.regValue .rax = if valid then 1 else 0)
    (scalar : Nat256At t (s.regValue .rdi) value) :
    ∃ u, Advances boundary 2 t u ∧ State s u ∧ u.RIP = 0x112fc0 ∧
      stackPtr u = stackPtr t ∧ u.regValue .rax = s.regValue .rdi ∧
      Nat256At u (s.regValue .rdi) value ∧
      u.external[s.regValue .rdi + 32]? = some (if valid then 1 else 0) := by
  have writable := (ScalarFrame.output_writable pre (by decide) state.allocated).add 32 (len := 1) (by decide)
  have address (v : RamState) : storeAddrAt 0x112fba (.base 3 (.d8 32)) 3 v = v.regValue .rbx + 32 := rfl
  obtain ⟨u, run, ready, effect⟩ :=
    (Common.Instructions.mov_m8_r8_legacy_effect_step 0x112fba 0 (by decide)
      (.base 3 (.d8 32)) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x12fba [0x88,0x43,0x20]
        (by decide) (by decide +kernel))
      ⟨rip, by
        change MemWritable t (storeAddrAt 0x112fba (.base 3 (.d8 32)) 3 t) 1
        rw [address, output]
        exact ⟨writable.low, writable.mem, writable.tables⟩,
       by
        change RangeApart (storeAddrAt 0x112fba (.base 3 (.d8 32)) 3 t) 1 0x112fba 3
        rw [address, output]
        exact Common.Instructions.RangeApart.add_left
          (ScalarFrame.output_code pre (offset := 0x12fba) (len := 3) (by decide)) 32 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x12fbd (by decide)))
  have ag : AgreesExcept [.mem (s.regValue .rdi + 32) 1, .rip] t u := by
    have h : AgreesExcept [.mem (storeAddrAt 0x112fba (.base 3 (.d8 32)) 3 t) 1, .rip] t u := by simpa only [storeEffect_components, Nat.reduceDiv, AddrMode.tail, Disp.bytes, immBytes_length, Nat.reduceAdd] using effect.agrees
    simpa only [address, output] using h
  have stateU := state.after_agrees pre ready ag (by
    apply ag.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨registerRegion s .rdi 33, by simp, ScalarFrame.output_contains pre (offset := 32) (by decide) ha⟩
    · exact ha.elim) (by simp)
  have scalarU : Nat256At u (s.regValue .rdi) value := by
    refine ⟨scalar.1, ?_⟩
    intro i hi
    refine (ag.byte ?_).trans (scalar.2 i hi)
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j,hj,he⟩ := ha
      exact (show OffsetsApart 32 1 0 32 from by unfold OffsetsApart; decide +kernel).ne
        (s.regValue .rdi) hj hi (by decide) (by simpa using he.symm)
    · exact ha.elim
  have stored : u.external[s.regValue .rdi + 32]? = some (if valid then 1 else 0) := by
    have word := effect.writes
    change memLoad u.external (storeAddrAt 0x112fba (.base 3 (.d8 32)) 3 t) 8 =
      (t.regValue .rax).setWidth 8 at word
    rw [address, output, flag] at word
    change memLoad u.external (s.regValue .rdi + 32#64) 8 =
      ((if valid then 1 else 0) : BitVec 64).setWidth 8 at word
    have bytes := Bytes.of_memLoad (n := 8) (fun i hi => ag.grow _ (writable.mem i hi))
    rw [word] at bytes
    have byte := bytes 0 (by decide)
    cases valid <;> simpa [storedByte] using byte
  obtain ⟨v, runV, readyV, effectV⟩ :=
    (mov_r64_r64_effect_step 0x112fbd 0x48 0xd8 (by simp [RexWPrefix]) rfl).advances ready
      (programText_slice (programLoaded_codeIn stateU.loaded) 0x12fbd [0x48,0x89,0xd8]
        (by decide) (by decide +kernel)) effect.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x12fc0 (by decide)))
  change (movR64R64Effect 0x112fbd 0 3 u).Holds u v at effectV
  have stateV := stateU.after_registers pre readyV effectV.agrees
    (by simp [Component.Covers]) (by simp)
  have memory := effectV.agrees.external (by simp [Component.Covers])
  refine ⟨v, run.trans runV, stateV, effectV.rip,
    (effectV.agrees.read (n := 64) (r := 4) (by simp)).trans (ag.read (by simp)),
    effectV.writes.trans ((ag.read (n := 64) (r := 3) (by simp)).trans output), ?_, ?_⟩
  · simpa only [Nat256At, memory] using scalarU
  · simpa only [memory] using stored

end P256.Proofs.Generate.Scalar
