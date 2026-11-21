import P256.Proofs.Nonce.Initialize.Read.Guard
import P256.Proofs.Nonce.Initialize.Read.Copy
import P256.Proofs.Nonce.Initialize.Read.Arguments

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Read

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

structure ShiftReady [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (digest : ByteArray) : Prop where
  stage : Stage initial s boundary
  output : memLoad s.external (stackPtr s + 192) 64 = initial.regValue .rdi
  secret : memLoad s.external (stackPtr s + 184) 64 = initial.regValue .rsi
  length : memLoad s.external (stackPtr s + 176) 64 = 32
  entropy : memLoad s.external (stackPtr s + 168) 64 = 1
  order0 : s.regValue .r15 = 0xf3b9cac2fc632551
  order1 : s.regValue .r14 = 0xbce6faada7179e84
  order2 : s.regValue .r13 = 0xffffffffffffffff
  order3 : s.regValue .rbx = 0xffffffff00000000
  destination : s.regValue .rdi = stackPtr s + 8
  source : s.regValue .rsi = stackPtr s + 72
  count : s.regValue .rdx = 0
  value : Nat256At s (stackPtr s + 72) (Arith.uint digest)

theorem prepare_shift [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {digest : ByteArray}
    (pre : InitializePre initial boundary orderAddress)
    (state : Decoded initial s boundary digest) (rip : s.RIP = 0x10795a) :
    ∃ t, ShiftReady initial t boundary digest ∧ t.RIP = 0x107999 := by
  obtain ⟨a, aa, ar, ap, ag⟩ := guard
    (readyToStep state.stage.machine state.stage.bindingsSupported) state.stage.loaded rip
    state.status pre.outerBoundary
  have af := state.stage.after_registers aa ar ag (by simp [Component.Covers]) (by simp)
  have am := ag.external (by simp [Component.Covers])
  have spa : stackPtr a = stackPtr s := by rw [af.rsp, state.stage.rsp]
  have av : Nat256At a (stackPtr a + 104) (Arith.uint digest) := by
    simpa only [Nat256At, am, spa] using state.value
  obtain ⟨b, bf, bp, bg, words⟩ := Copy.correct pre af ap
  have spb : stackPtr b = stackPtr s := by rw [bf.rsp, state.stage.rsp]
  have bg' : AgreesExcept (Copy.components s) a b := by simpa only [Copy.components, spa] using bg
  have ab := ag.trans bg'
  have shift : b.regValue .rbp = 0 :=
    (ab.read (n := 64) (r := 5) (by simp [Copy.components])).trans state.shift
  obtain ⟨t, ta, tr, tp, td, ts, tc, tg⟩ := arguments
    (readyToStep bf.machine bf.bindingsSupported) bf.loaded bp shift pre.outerBoundary
  have tf := bf.after_registers ta tr tg (by simp [Component.Covers]) (by simp)
  have spt : stackPtr t = stackPtr s := by rw [tf.rsp, state.stage.rsp]
  have tm := tg.external (by simp [Component.Covers])
  have total := ab.trans tg
  have word (offset : Nat) (ho : offset = 168 ∨ offset = 176 ∨ offset = 184 ∨ offset = 192) :
      memLoad t.external (stackPtr t + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64 := by
    rw [spt]
    apply read_mem_of_agrees total
    intro i hi c hc
    simp only [Copy.components, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl)
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals rcases ho with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel
  refine ⟨t, ⟨tf, (word 192 (.inr (.inr (.inr rfl)))).trans state.output,
    (word 184 (.inr (.inr (.inl rfl)))).trans state.secret,
    (word 176 (.inr (.inl rfl))).trans state.length,
    (word 168 (.inl rfl)).trans state.entropy,
    (total.read (n := 64) (r := 15) (by simp [Copy.components])).trans state.order0,
    (total.read (n := 64) (r := 14) (by simp [Copy.components])).trans state.order1,
    (total.read (n := 64) (r := 13) (by simp [Copy.components])).trans state.order2,
    (total.read (n := 64) (r := 3) (by simp [Copy.components])).trans state.order3,
    by simpa only [spb, spt] using td, by simpa only [spb, spt] using ts, tc, ?_⟩, tp⟩
  have v : Nat256At b (stackPtr b + 72) (Arith.uint digest) := by
    apply nat256At_of_memLoad_limbs av.1
    · exact (ScalarFrame.stack_readable pre.toCalleePre bf.toFrameState
        (offset := 72) (len := 32) (by decide) (by decide)).mem
    · intro j hj
      exact (words j hj).trans (av.memLoad_limb j hj)
  simpa only [Nat256At, tm, spt, spb] using v

theorem prepare_correct [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {digest : ByteArray}
    (pre : InitializePre initial boundary orderAddress)
    (bytes : (registerRegion initial .rcx 32).HasBytes initial.external digest) :
    ∃ t, ShiftReady initial t boundary digest ∧ t.RIP = 0x107999 := by
  obtain ⟨a, af, ap⟩ := Prepare.correct pre
  obtain ⟨b, bf, bp⟩ := Prepare.buffer_correct pre af ap
  obtain ⟨c, cf, cp⟩ := correct pre bf bp bytes
  exact prepare_shift pre cf cp

end P256.Proofs.Nonce.Initialize.Read
