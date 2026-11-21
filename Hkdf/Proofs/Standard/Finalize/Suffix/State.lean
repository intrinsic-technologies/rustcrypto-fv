import Hkdf.Proofs.Standard.Finalize.StreamPadding
import Hkdf.Proofs.Common.Streaming

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

structure State [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (s : RamState) : Prop where
  running : Running initial boundary
    #v[registerRegion initial .rdi 176, Stack.region initial 1264] s
  rsp : stackPtr s = stackPtr initial - 408
  rbx : s.regValue .rbx = initial.regValue .rdi
  saved : ∀ i < 48, s.external[stackPtr initial - 40 + BitVec.ofNat 64 i]? =
    (Hmac.savedMemory initial)[stackPtr initial - 40 + BitVec.ofNat 64 i]?
  rbp : s.regValue .rbp = initial.regValue .rbp
  mxcsr : s.MXCSR = initial.MXCSR
  fcw : s.FP87_Control = initial.FP87_Control

theorem State.of_agrees [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {fuel : Nat} {components : List Component}
    (state : State initial boundary s)
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (writes : WritesWithin components
      #v[registerRegion initial .rdi 176, Stack.region initial 1264])
    (kept : ∀ c ∈ ([.reg 4, .reg 3, .reg 5, .mxcsr, .fcw, .df] : List Component),
      c ∉ components)
    (saved : (Component.mem (stackPtr initial - 40) 48).Agrees s t) :
    State initial boundary t := by
  have stable := Common.StreamPadding.Execution.stable_of_agrees agrees
    (fun c hc ↦ kept c (by simpa using List.mem_append_left [.df] hc))
  refine ⟨state.running.of_agrees run ready agrees writes ?_ (kept _ (by simp)),
    stable.1.trans state.rsp, stable.2.1.trans state.rbx, ?_,
    stable.2.2.1.trans state.rbp, stable.2.2.2.1.trans state.mxcsr,
    stable.2.2.2.2.trans state.fcw⟩
  · intro region member a contained inProgram
    exact pre.avoids region (by simpa using member) a contained (.inl inProgram)
  · intro i hi
    exact (saved i hi).trans (state.saved i hi)

theorem State.of_running [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (state : State initial boundary s)
    (running : Running initial boundary
      #v[registerRegion initial .rdi 176, Stack.region initial 1264] t)
    (abi : Hkdf.Proofs.Program.PreservesABI s t) (rsp : stackPtr t = stackPtr s)
    (saved : (Component.mem (stackPtr initial - 40) 48).Agrees s t) :
    State initial boundary t :=
  ⟨running, rsp.trans state.rsp, (abi.1 .rbx (by simp)).trans state.rbx,
    fun i hi ↦ (saved i hi).trans (state.saved i hi),
    (abi.1 .rbp (by simp)).trans state.rbp,
    abi.2.2.1.trans state.mxcsr, abi.2.2.2.trans state.fcw⟩

def innerHash (key message : ByteArray) :=
  compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
    (bytePadding (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message))

def outerHash (key : ByteArray) :=
  compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
    (HMAC.xorPad (HMAC.keyBlock key) 0x5c)

theorem from_hmac [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {key message : ByteArray}
    (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (hmac : HmacAt initial (initial.regValue .rsi) key message)
    (size : 64 + message.size < 2^61) :
    ∃ s, State initial boundary s ∧ s.RIP = 0x10df0d ∧
      HashStateAt s (stackPtr initial - 272) (innerHash key message) ∧
      HashStateAt s (stackPtr initial - 232) (outerHash key) ∧
      loadBytes s.external (stackPtr initial - 200) 8 = .ok 1 := by
  obtain ⟨s, running, rip, rsp, rbx, inner, outer, count, saved, rbp, mxcsr, fcw⟩ :=
    StreamPadding.run pre hmac size
  exact ⟨s, ⟨running, rsp, rbx, saved, rbp, mxcsr, fcw⟩, rip, inner, outer, count⟩

end Hkdf.Proofs.Standard.Finalize.Suffix
