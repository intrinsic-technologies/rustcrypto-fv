import P256.Proofs.Signing.Wrapper.Entry.Decode.Range
import P256.Proofs.Signing.Wrapper.Entry.Decode.Choice

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

structure ValidState [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 520, Saved initial s, LimbsAt s (Arith.uint secret) where
  rip : s.RIP = 0x10256a

theorem valid_branch [Bindings] {initial s : RamState} {secret message : ByteArray}
    (context : Context initial secret message) (state : Compared initial s secret) :
    ∃ t, Advances (returnBoundary initial) 8 s t ∧ ValidState initial t secret := by
  obtain ⟨slices,call⟩ := context.call
  have outside := outer_boundary call context.machine context.bindingsSupported
  obtain ⟨a,ha,sa,ipa,va,fa⟩ := choice_call context.call context.bindingsSupported context.machine
    state.toState 0x255d 0x16b0e (by decide) (by decide +kernel) (by decide +kernel) state.rip
  have ax : a.regValue .rax = 1 := by
    change a.regValue .rax = ((s.regValue .rdi).setWidth 8).setWidth 64 at va
    rw [va,state.valid]
    decide +kernel
  obtain ⟨t,ht,rt,ipt,ft⟩ := range_status (readyToStep sa.machine sa.bindingsSupported)
    sa.loaded ipa (by change (a.regValue .rax).setWidth 8 = 1; rw [ax]; rfl) outside
  have st := after_stack call sa ht rt ft (by simp) (by simp) (by simp)
  have ag := fa.trans ft
  have mt := ft.external (by simp [Component.Covers])
  have read (off : Nat) (bound : off ≤ 520) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) 64 =
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) 64 := by
    rw [mt]
    exact memLoad_agrees_apart fa (choice_memory context.call bound (by omega))
  refine ⟨t,ha.trans ht,⟨st,?_,?_,ipt⟩⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (ag.read (n:=64) (r:=12) (by simp [choiceClobbers])).trans state.pointers
    · exact (ag.read (n:=64) (r:=13) (by simp [choiceClobbers])).trans state.count
    · exact (read 192 (by decide)).trans state.lengths
    · exact (read 208 (by decide)).trans state.output
    · exact (read 200 (by decide)).trans state.capacity
  · refine ⟨?_,?_,?_,?_⟩
    · exact (ag.read (n:=64) (r:=5) (by simp [choiceClobbers])).trans state.word0
    · exact (ag.read (n:=64) (r:=14) (by simp [choiceClobbers])).trans state.word1
    · exact (ag.read (n:=64) (r:=3) (by simp [choiceClobbers])).trans state.word2
    · exact (ag.read (n:=64) (r:=15) (by simp [choiceClobbers])).trans state.word3

end P256.Proofs.Signing.Wrapper.Entry.Decode
