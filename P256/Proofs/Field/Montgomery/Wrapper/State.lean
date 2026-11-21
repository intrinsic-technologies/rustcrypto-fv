import P256.Proofs.Field.Montgomery.Entry
import P256.Proofs.Program.ScalarFrame.Work
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev scratch (s : RamState) : BitVec 64 := stackPtr s - 136

abbrev workRegion (s : RamState) : MemoryRegion := ScalarFrame.Work.region s 280 8

structure SavedState [bindings : Bindings] (s t : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 32, Stack.region s 280]
  registers : ∀ r ∈ [Syntax.Reg.rbp, .r12, .r13, .r14, .r15], t.regValue r = s.regValue r
  directionFlag : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control
  savedRbx : memLoad t.external (stackPtr s - 8) 64 = s.regValue .rbx
  returnWord : memLoad t.external (stackPtr s) 64 = (returnBoundary s).rip

structure FrameState [Bindings] (s t : RamState) : Prop extends SavedState s t where
  rsp : stackPtr t = scratch s
  rbx : t.regValue .rbx = s.regValue .rdi

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64}

theorem SavedState.after_result {entry : RamState} {outputBytes reserve : Nat}
    (pre : CalleePre s boundary entryPC 32 32 280) (state : SavedState s entry)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (frame : MemoryWriteFrame entry t #v[registerRegion s .rdi 32, workRegion s]) :
    SavedState s t := by
  refine {
    bindingsSupported := result.bindingsSupported
    machine := result.machine
    loaded := result.loaded
    allocated := fun a ha => result.allocated a (state.allocated a ha)
    frame := memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre frame)
    registers := fun r hr => (result.calleeSaved r (List.mem_cons_of_mem .rbx hr)).trans
      (state.registers r hr)
    directionFlag := result.directionFlag
    mxcsr := result.mxcsr.trans state.mxcsr
    fp87 := result.fp87.trans state.fp87
    savedRbx := (ScalarFrame.Work.read pre (by decide) frame
      (offset := 8) (n := 64) (by decide) (by decide)).trans state.savedRbx
    returnWord := ?_ }
  have h := ScalarFrame.Work.read pre (by decide) frame
    (offset := 0) (n := 64) (by decide) (by decide)
  simp only [BitVec.sub_zero] at h
  exact h.trans state.returnWord

theorem SavedState.after_agrees {cs : List Component}
    (pre : CalleePre s boundary entryPC 32 32 280) (state : SavedState s t) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 32, workRegion s])
    (regs : ∀ r ∈ [Syntax.Reg.rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r)
    (hdf : Component.df ∉ cs) (hmxcsr : Component.mxcsr ∉ cs) (hfcw : Component.fcw ∉ cs) :
    SavedState s u := by
  have memory := agrees.memoryWriteFrame writes
  have whole := memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre memory)
  refine {
    bindingsSupported := bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees
    machine := supportedMachine_of_ready_agrees state.machine ready agrees
    loaded := ScalarFrame.loaded_of_frame pre whole
    allocated := fun a ha => agrees.grow a (state.allocated a ha)
    frame := whole
    registers := fun r hr => (regs r hr).trans (state.registers r hr)
    directionFlag := agrees.directionFlagClear hdf state.directionFlag
    mxcsr := (agrees.mxcsr hmxcsr).trans state.mxcsr
    fp87 := (agrees.fcw hfcw).trans state.fp87
    savedRbx := (ScalarFrame.Work.read pre (by decide) memory
      (offset := 8) (n := 64) (by decide) (by decide)).trans state.savedRbx
    returnWord := ?_ }
  have h := ScalarFrame.Work.read pre (by decide) memory
    (offset := 0) (n := 64) (by decide) (by decide)
  simp only [BitVec.sub_zero] at h
  exact h.trans state.returnWord

end P256.Proofs.Field.Montgomery.Wrapper
