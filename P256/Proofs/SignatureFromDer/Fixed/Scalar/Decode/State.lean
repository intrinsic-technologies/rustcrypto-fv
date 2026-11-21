import P256.Proofs.SignatureFromDer.Fixed.Scalar.State

set_option autoImplicit false

open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Stage [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop
    extends FrameState s t where
  execution : ∃ fuel, Advances boundary fuel s t
  output : t.regValue .rbx = s.regValue .rdi
  tag : t.regValue .r14 = 1

theorem Stage.after [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {fuel : Nat}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : Stage s t boundary)
    (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion s .rdi 40, Program.ScalarFrame.workRegion s 288])
    (rsp : .reg 4 ∉ cs) (rbx : .reg 3 ∉ cs) (r14 : .reg 14 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    Stage s u boundary := by
  obtain ⟨n, hn⟩ := state.execution
  exact ⟨Program.ScalarFrame.FrameState.after_effect (frameOffset := 152) pre (by decide) state.toFrameState ready agrees writes rsp hdf hmxcsr hfcw,
    ⟨n + fuel, hn.trans run⟩,
    (agrees.read (n := 64) (r := 3) rbx).trans state.output,
    (agrees.read (n := 64) (r := 14) r14).trans state.tag⟩

theorem Stage.after_registers [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {fuel : Nat} (state : Stage s t boundary)
    (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (rsp : .reg 4 ∉ cs) (rbx : .reg 3 ∉ cs) (r14 : .reg 14 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    Stage s u boundary := by
  obtain ⟨n, hn⟩ := state.execution
  exact ⟨state.toFrameState.after_registers ready agrees memory rsp hdf hmxcsr hfcw,
    ⟨n + fuel, hn.trans run⟩,
    (agrees.read (n := 64) (r := 3) rbx).trans state.output,
    (agrees.read (n := 64) (r := 14) r14).trans state.tag⟩

structure CopiedState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x10fa64
  bytes : (MemoryRegion.mk (stackPtr s - 80).toNat 32).HasBytes t.external input

structure EntryState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x10faaa
  source : t.regValue .rdi = stackPtr s - 80
  destination : t.regValue .rdx = stackPtr s - 112
  count : t.regValue .rsi = 32
  limbs : t.regValue .rcx = 4
  bits : t.regValue .r8 = 256
  bytes : (MemoryRegion.mk (stackPtr s - 80).toNat 32).HasBytes t.external input

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode
