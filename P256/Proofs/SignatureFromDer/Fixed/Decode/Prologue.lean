import P256.Proofs.SignatureFromDer.Fixed.FrameLemmas
import P256.Proofs.SignatureFromDer.Fixed.Decode.Prologue.Steps
import P256.Proofs.Program.WrapperArena

set_option autoImplicit false

open P256.Proofs.Program (CalleePre memoryRegion_contains_add supportedMachine_of_ready_agrees)

namespace P256.Proofs.SignatureFromDer.Fixed.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure EntryState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x109ada
  rsi : t.regValue .rsi = s.regValue .rsi
  r14 : t.regValue .r14 = s.regValue .rsi
  memory : t.external = P256.Proofs.Program.SavePair.savedMemory s
  input : (registerRegion s .rsi 64).HasBytes t.external input

theorem prologue [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x109ac0 64 72 560)
    (length : s.regValue .rdx = 64)
    (bytes : (registerRegion s .rsi 64).HasBytes s.external input) :
    ∃ t, EntryState s t boundary input := by
  obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, frameU⟩ := stack_setup pre
  have lengthU : u.regValue .rdx = 64 :=
    (frameU.read (n := 64) (r := 2) (by simp [P256.Proofs.Program.SavePair.saveComponents])).trans length
  obtain ⟨t, runT, readyT, ripT, outputT, inputT, frameT⟩ :=
    length_gate readyU loadedU ripU lengthU pre.outerBoundary
  have agrees := frameU.trans frameT
  have ext : t.external = u.external := frameT.external (by simp [Component.Covers])
  have mem : t.external = P256.Proofs.Program.SavePair.savedMemory s := ext.trans memoryU
  have saved := P256.Proofs.Program.savedMemory_words s
  rw [← mem] at saved
  have writes : WritesWithin
      (P256.Proofs.Program.SavePair.saveComponents s ++ [.reg 3, .reg 14, .flags, .rip])
      #v[registerRegion s .rdi 72, Stack.region s 560] := by
    intro c hc a ha
    refine ⟨Stack.region s 560, by simp, ?_⟩
    simp only [P256.Proofs.Program.SavePair.saveComponents, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    all_goals try exact ha.elim
    all_goals exact Program.ScalarFrame.stack_contains pre (by decide +kernel) (by decide +kernel) ha
  have memory := agrees.memoryWriteFrame writes
  refine ⟨t, {
    bindingsSupported := Program.bindingsSupported_of_ready_agrees pre.bindingsSupported readyT agrees
    machine := supportedMachine_of_ready_agrees pre.machine readyT agrees
    loaded := ?_
    directionFlag := agrees.directionFlagClear (by component_not_mem) pre.directionFlag
    allocated := agrees.grow
    frame := memory
    rsp := (frameT.read (n := 64) (r := 4) (by simp)).trans rspU
    savedRbx := saved.1
    savedR14 := saved.2.1
    rbp := agrees.read (n := 64) (r := 5) (by simp [P256.Proofs.Program.SavePair.saveComponents])
    r12 := agrees.read (n := 64) (r := 12) (by simp [P256.Proofs.Program.SavePair.saveComponents])
    r13 := agrees.read (n := 64) (r := 13) (by simp [P256.Proofs.Program.SavePair.saveComponents])
    r15 := agrees.read (n := 64) (r := 15) (by simp [P256.Proofs.Program.SavePair.saveComponents])
    returnAddress := saved.2.2
    mxcsr := agrees.mxcsr (by component_not_mem)
    fp87 := agrees.fcw (by component_not_mem)
    execution := ⟨7, runU.trans runT⟩
    output := outputT.trans (frameU.read (n := 64) (r := 7) (by simp [P256.Proofs.Program.SavePair.saveComponents]))
    rip := ripT
    rsi := agrees.read (n := 64) (r := 6) (by simp [P256.Proofs.Program.SavePair.saveComponents])
    r14 := inputT.trans (frameU.read (n := 64) (r := 6) (by simp [P256.Proofs.Program.SavePair.saveComponents]))
    memory := mem
    input := ?_
  }⟩
  · intro a b h
    rw [ext]
    exact loadedU a b h
  · exact Program.ScalarFrame.input_bytes_of_frame pre memory bytes

theorem prologue_reject [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {inputBytes : Nat} (pre : CalleePre s boundary 0x109ac0 inputBytes 72 560)
    (length : s.regValue .rdx ≠ 64) :
    ∃ t, Stage s t boundary ∧ t.RIP = 0x109c57 := by
  obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, frameU⟩ := stack_setup pre
  have lengthU : u.regValue .rdx ≠ 64 := by
    exact fun h => length ((frameU.read (n := 64) (r := 2) (by simp [P256.Proofs.Program.SavePair.saveComponents])).symm.trans h)
  obtain ⟨t, runT, readyT, ripT, outputT, frameT⟩ :=
    length_reject readyU loadedU ripU lengthU pre.outerBoundary
  have agrees := frameU.trans frameT
  have ext : t.external = u.external := frameT.external (by simp [Component.Covers])
  have mem : t.external = P256.Proofs.Program.SavePair.savedMemory s := ext.trans memoryU
  have saved := P256.Proofs.Program.savedMemory_words s
  rw [← mem] at saved
  have writes : WritesWithin
      (P256.Proofs.Program.SavePair.saveComponents s ++ [.reg 3, .flags, .rip])
      #v[registerRegion s .rdi 72, Stack.region s 560] := by
    intro c hc a ha
    refine ⟨Stack.region s 560, by simp, ?_⟩
    simp only [P256.Proofs.Program.SavePair.saveComponents, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
    all_goals try exact ha.elim
    all_goals exact Program.ScalarFrame.stack_contains pre (by decide +kernel) (by decide +kernel) ha
  have memory := agrees.memoryWriteFrame writes
  refine ⟨t, {
    bindingsSupported := Program.bindingsSupported_of_ready_agrees pre.bindingsSupported readyT agrees
    machine := supportedMachine_of_ready_agrees pre.machine readyT agrees
    loaded := ?_
    directionFlag := agrees.directionFlagClear (by component_not_mem) pre.directionFlag
    allocated := agrees.grow
    frame := memory
    rsp := (frameT.read (n := 64) (r := 4) (by simp)).trans rspU
    savedRbx := saved.1
    savedR14 := saved.2.1
    rbp := agrees.read (n := 64) (r := 5) (by simp [P256.Proofs.Program.SavePair.saveComponents])
    r12 := agrees.read (n := 64) (r := 12) (by simp [P256.Proofs.Program.SavePair.saveComponents])
    r13 := agrees.read (n := 64) (r := 13) (by simp [P256.Proofs.Program.SavePair.saveComponents])
    r15 := agrees.read (n := 64) (r := 15) (by simp [P256.Proofs.Program.SavePair.saveComponents])
    returnAddress := saved.2.2
    mxcsr := agrees.mxcsr (by component_not_mem)
    fp87 := agrees.fcw (by component_not_mem)
    execution := ⟨6, runU.trans runT⟩
    output := outputT.trans (frameU.read (n := 64) (r := 7) (by simp [P256.Proofs.Program.SavePair.saveComponents]))
  }, ripT⟩
  intro a b h
  rw [ext]
  exact loadedU a b h

end P256.Proofs.SignatureFromDer.Fixed.Decode
