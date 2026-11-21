import P256.Proofs.Generate.Sampler.Interface
import P256.Proofs.Program.ScalarFrame.Prologue
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure State [bindings : Bindings] (s t : RamState) (offset : BitVec 64 := 264) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  directionFlag : DirectionFlagUnset t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t (writes s)
  rsp : stackPtr t = stackPtr s - offset
  saved : ∀ entry ∈ savedRegisters,
    memLoad t.external (stackPtr s - BitVec.ofNat 64 entry.2) 64 = s.regValue entry.1
  returnAddress : memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control

def bodyWrites (s : RamState) : Vector MemoryRegion 3 :=
  #v[registerRegion s .rdi 104, ScalarFrame.workRegion s 3624, registerRegion s .rsi 16]

theorem State.of_scalarFrame [Bindings] {s t : RamState} {offset : BitVec 64}
    (state : ScalarFrame.FrameState s t 104 3624 offset) : State s t offset := by
  refine ⟨state.bindingsSupported,state.machine,state.loaded,state.directionFlag,
    state.allocated,?_,state.rsp,state.saved,state.returnAddress,state.mxcsr,state.fp87⟩
  intro a ha
  apply state.frame a
  intro r hr
  apply ha r
  have hr : r = registerRegion s .rdi 104 ∨ r = Stack.region s 3624 := by simpa using hr
  rcases hr with rfl | rfl <;> simp [writes]

theorem body_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : Pre s boundary input)
    (frame : MemoryWriteFrame t u (bodyWrites s)) :
    MemoryWriteFrame t u (writes s) := by
  intro a ha
  apply frame a
  intro r hr hit
  have choice : r = registerRegion s .rdi 104 ∨ r = ScalarFrame.workRegion s 3624 ∨
      r = registerRegion s .rsi 16 := by simpa [bodyWrites] using hr
  rcases choice with rfl | rfl | rfl
  · exact ha _ (by simp [writes]) hit
  · apply ha (Stack.region s 3624) (by simp [writes])
    have bounds := stack_bounds pre.stack
    change (stackPtr s).toNat - 3624 ≤ a.toNat ∧
      a.toNat < (stackPtr s).toNat - 3624 + 3576 at hit
    change (stackPtr s).toNat - 3624 ≤ a.toNat ∧
      a.toNat < (Stack.region s 3624).start + (Stack.region s 3624).size
    rw [stack_region_end]
    constructor <;> omega
  · exact ha _ (by simp [writes]) hit

theorem body_read [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset width : Nat}
    (pre : Pre s boundary input) (frame : MemoryWriteFrame t u (bodyWrites s))
    (ho : offset ≤ 48) (hw : width / 8 ≤ offset + 8) :
    memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) width =
      memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) width := by
  have bounds := stack_bounds pre.toCalleePre.stack
  have low := stack_sub_toNat pre.toCalleePre.stack (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [frame _]
  intro r hr hit
  have address : (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat - offset + i := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by rw [low]; omega),low]
  have inStack : (Stack.region s 3624).Contains
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
    change (stackPtr s).toNat - 3624 ≤ _ ∧ _ < (Stack.region s 3624).start + (Stack.region s 3624).size
    rw [address,stack_region_end]
    constructor <;> omega
  have choice : r = registerRegion s .rdi 104 ∨ r = ScalarFrame.workRegion s 3624 ∨
      r = registerRegion s .rsi 16 := by simpa [bodyWrites] using hr
  rcases choice with rfl | rfl | rfl
  · exact pre.separation 1 2 (by decide) _ hit inStack
  · change _ ≤ _ ∧ _ < (stackPtr s).toNat - 3624 + 3576 at hit
    rw [address] at hit
    omega
  · exact pre.separation 0 2 (by decide) _ hit inStack

theorem State.after [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset : BitVec 64}
    {cs : List Component} (pre : Pre s boundary input) (state : State s t offset)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (within : WritesWithin cs (bodyWrites s)) (rsp : stackPtr u = stackPtr t)
    (df : Component.df ∉ cs := by component_not_mem)
    (mxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (fcw : Component.fcw ∉ cs := by component_not_mem) : State s u offset := by
  have localFrame := agrees.memoryWriteFrame within
  have fullFrame := body_frame pre localFrame
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,?_,
    agrees.directionFlagClear df state.directionFlag,
    fun a ha ↦ agrees.grow a (state.allocated a ha),
    memoryWriteFrame_trans state.frame fullFrame,rsp.trans state.rsp,?_,?_,
    (agrees.mxcsr mxcsr).trans state.mxcsr,(agrees.fcw fcw).trans state.fp87⟩
  · intro a b hb
    rw [fullFrame a]
    · exact state.loaded a b hb
    · intro r hr hit
      have choice : r = registerRegion s .rdi 104 ∨ r = registerRegion s .rsi 16 ∨
          r = Stack.region s 3624 := by simpa [writes] using hr
      rcases choice with rfl | rfl | rfl
      · exact pre.avoids _ (by simp) a hit (.inl ⟨b,hb⟩)
      · exact pre.descriptorAvoids a hit (.inl ⟨b,hb⟩)
      · exact pre.avoids _ (by simp) a hit (.inl ⟨b,hb⟩)
  · intro e he
    have bound : e.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (body_read pre localFrame bound (by omega)).trans (state.saved e he)
  · have h := body_read pre localFrame (offset := 0) (width := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem State.after_registers [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset : BitVec 64}
    {cs : List Component} (pre : Pre s boundary input) (state : State s t offset)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (noMem : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (sp : Component.reg 4 ∉ cs)
    (df : Component.df ∉ cs := by component_not_mem)
    (mxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (fcw : Component.fcw ∉ cs := by component_not_mem) : State s u offset :=
  state.after pre ready agrees (fun c hc a ha ↦ (noMem c hc a ha).elim)
    (agrees.read (n := 64) (r := 4) sp) df mxcsr fcw

end P256.Proofs.Generate.Sampler
