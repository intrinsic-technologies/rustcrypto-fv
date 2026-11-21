import P256.Proofs.Program.ScalarFrame.Input
import P256.Proofs.SignatureFromDer.Fixed.Memory

set_option autoImplicit false

open P256.Proofs.Program (CalleePre supportedMachine_of_ready_agrees bindingsSupported_of_ready_agrees)

namespace P256.Proofs.SignatureFromDer.Fixed

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem Frame.of_agrees [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {inputBytes : Nat} (pre : CalleePre s boundary 0x109ac0 inputBytes 72 560)
    (state : Frame s t) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 72, workRegion s])
    (rsp : stackPtr u = stackPtr s - 184)
    (preserve : ∀ r ∈ ([5, 12, 13, 15] : List (BitVec 5)), .reg r ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : Frame s u := by
  have memory := agrees.memoryWriteFrame writes
  have total := memoryWriteFrame_trans state.frame (Program.ScalarFrame.Work.frame pre memory)
  refine { bindingsSupported := bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees
           machine := supportedMachine_of_ready_agrees state.machine ready agrees
           loaded := Program.ScalarFrame.loaded_of_frame pre total
           directionFlag := agrees.directionFlagClear hdf state.directionFlag
           allocated := fun a ha => agrees.grow a (state.allocated a ha)
           frame := total
           rsp := rsp
           savedRbx := (Program.ScalarFrame.Work.read pre (by decide) memory (offset := 16) (n := 64)
             (by decide) (by decide)).trans state.savedRbx
           savedR14 := (Program.ScalarFrame.Work.read pre (by decide) memory (offset := 8) (n := 64)
             (by decide) (by decide)).trans state.savedR14
           rbp := (agrees.read (n := 64) (r := 5) (preserve 5 (by simp))).trans state.rbp
           r12 := (agrees.read (n := 64) (r := 12) (preserve 12 (by simp))).trans state.r12
           r13 := (agrees.read (n := 64) (r := 13) (preserve 13 (by simp))).trans state.r13
           r15 := (agrees.read (n := 64) (r := 15) (preserve 15 (by simp))).trans state.r15
           returnAddress := ?_
           mxcsr := (agrees.mxcsr hmxcsr).trans state.mxcsr
           fp87 := (agrees.fcw hfcw).trans state.fp87 }
  have h := Program.ScalarFrame.Work.read pre (by decide) memory (offset := 0) (n := 64) (by decide) (by decide)
  simp only [BitVec.sub_zero] at h
  exact h.trans state.returnAddress

theorem Frame.after_registers [Bindings] {s t u : RamState} {cs : List Component}
    (state : Frame s t) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (preserve : ∀ r ∈ ([4, 5, 12, 13, 15] : List (BitVec 5)), .reg r ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : Frame s u := by
  have hm := agrees.external memory
  refine { bindingsSupported := bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees
           machine := supportedMachine_of_ready_agrees state.machine ready agrees
           loaded := ?_
           directionFlag := agrees.directionFlagClear hdf state.directionFlag
           allocated := fun a ha => agrees.grow a (state.allocated a ha)
           frame := ?_
           rsp := (agrees.read (n := 64) (r := 4) (preserve 4 (by simp))).trans state.rsp
           savedRbx := ?_
           savedR14 := ?_
           rbp := (agrees.read (n := 64) (r := 5) (preserve 5 (by simp))).trans state.rbp
           r12 := (agrees.read (n := 64) (r := 12) (preserve 12 (by simp))).trans state.r12
           r13 := (agrees.read (n := 64) (r := 13) (preserve 13 (by simp))).trans state.r13
           r15 := (agrees.read (n := 64) (r := 15) (preserve 15 (by simp))).trans state.r15
           returnAddress := ?_
           mxcsr := (agrees.mxcsr hmxcsr).trans state.mxcsr
           fp87 := (agrees.fcw hfcw).trans state.fp87 }
  · intro a b hb
    rw [hm]
    exact state.loaded a b hb
  · intro a ha
    rw [hm]
    exact state.frame a ha
  · change memLoad u.external _ 64 = _
    rw [hm]
    exact state.savedRbx
  · change memLoad u.external _ 64 = _
    rw [hm]
    exact state.savedR14
  · change memLoad u.external _ 64 = _
    rw [hm]
    exact state.returnAddress

theorem Stage.after [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {fuel : Nat}
    {inputBytes : Nat} (pre : CalleePre s boundary 0x109ac0 inputBytes 72 560) (state : Stage s t boundary)
    (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 72, workRegion s])
    (rsp : stackPtr u = stackPtr s - 184)
    (preserve : ∀ r ∈ ([3, 5, 12, 13, 15] : List (BitVec 5)), .reg r ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    Stage s u boundary := by
  obtain ⟨n, hn⟩ := state.execution
  exact ⟨state.toFrame.of_agrees pre ready agrees writes rsp
    (fun r hr => preserve r (by simpa only [List.mem_cons] using Or.inr hr)) hdf hmxcsr hfcw,
    ⟨n + fuel, hn.trans run⟩,
    (agrees.read (n := 64) (r := 3) (preserve 3 (by simp))).trans state.output⟩

theorem Stage.after_registers [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {fuel : Nat} (state : Stage s t boundary)
    (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (preserve : ∀ r ∈ ([3, 4, 5, 12, 13, 15] : List (BitVec 5)), .reg r ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    Stage s u boundary := by
  obtain ⟨n, hn⟩ := state.execution
  exact ⟨state.toFrame.after_registers ready agrees memory
    (fun r hr => preserve r (by simpa only [List.mem_cons] using Or.inr hr)) hdf hmxcsr hfcw,
    ⟨n + fuel, hn.trans run⟩,
    (agrees.read (n := 64) (r := 3) (preserve 3 (by simp))).trans state.output⟩

theorem Frame.input_bytes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray}
    {inputBytes : Nat} (pre : CalleePre s boundary 0x109ac0 inputBytes 72 560) (state : Frame s t)
    (bytes : (registerRegion s .rsi inputBytes).HasBytes s.external input) :
    (registerRegion s .rsi inputBytes).HasBytes t.external input :=
  Program.ScalarFrame.input_bytes_of_frame pre state.frame bytes

end P256.Proofs.SignatureFromDer.Fixed
