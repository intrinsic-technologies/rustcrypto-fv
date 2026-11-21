import Hkdf.Proofs.Common.SHA256.Interfaces
import Hkdf.Proofs.Common.Encoding.Serialize.Prologue

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Spec Hkdf.Proofs.Program Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure RegistersAt (s : RamState) (hash : Array UInt32) : Prop where
  size : hash.size = 8
  a : (s.regValue .rbx).setWidth 32 = hash[0]!.toBitVec
  b : (s.regValue .r14).setWidth 32 = hash[1]!.toBitVec
  c : (s.regValue .rax).setWidth 32 = hash[2]!.toBitVec
  d : (s.regValue .r9).setWidth 32 = hash[3]!.toBitVec
  e : (s.regValue .r8).setWidth 32 = hash[4]!.toBitVec
  f : (s.regValue .r10).setWidth 32 = hash[5]!.toBitVec
  g : (s.regValue .rdx).setWidth 32 = hash[6]!.toBitVec
  h : (s.regValue .rcx).setWidth 32 = hash[7]!.toBitVec

structure FrameState [bindings : Bindings] (s t : RamState) : Prop where
  machine : SupportedMachine bindings t
  loaded : ProgramLoaded t
  directionFlag : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 32, Stack.region s 336]
  rsp : stackPtr t = stackPtr s - 336
  saved : ∀ entry ∈ Hkdf.Proofs.Common.Encoding.Serialize.savedRegisters,
    (Operand.mem (stackPtr s - BitVec.ofNat 64 entry.2) : Operand 64).read t =
      s.regValue entry.1
  returnAddress : (Operand.mem (stackPtr s) : Operand 64).read t =
    (Operand.mem (stackPtr s) : Operand 64).read s
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control

structure LoopState [Bindings] (initial current : RamState) (hash : Array UInt32)
    (index count : Nat) : Prop extends FrameState initial current where
  registers : RegistersAt current hash
  inputPointer : current.regValue .rsi = initial.regValue .rsi + BitVec.ofNat 64 (64 * index)
  statePointer : memLoad current.external (stackPtr current + 0xc0) 64 = initial.regValue .rdi
  endPointer : memLoad current.external (stackPtr current + 0xc8) 64 =
    initial.regValue .rsi + BitVec.ofNat 64 (64 * count)

theorem FrameState.after_registers [Bindings] {s u t : RamState} {cs : List Component}
    (state : FrameState s u) (ready : ReadyToStep t) (h : AgreesExcept cs u t)
    (hm : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (hsp : .reg 4 ∉ cs)
    (hdf : .df ∉ cs := by simp) (hmxcsr : .mxcsr ∉ cs := by simp) (hfcw : .fcw ∉ cs := by simp) : FrameState s t := by
  have memory := h.external hm
  refine ⟨Hkdf.Proofs.Common.Machine.supportedMachine_of_ready_agrees state.machine ready h,
    ?_, h.directionFlagClear hdf state.directionFlag,
    fun a ha => h.grow a (state.allocated a ha), ?_,
    (h.read (n := 64) (r := 4) hsp).trans state.rsp, ?_, ?_,
    (h.mxcsr hmxcsr).trans state.mxcsr,
    (h.fcw hfcw).trans state.fp87⟩
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro entry he
    change memLoad t.external _ 64 = _
    rw [memory]
    exact state.saved entry he
  · change memLoad t.external _ 64 = _
    rw [memory]
    exact state.returnAddress

end Hkdf.Proofs.Common.SHA256
