import P256.Proofs.Nonce.Initialize.Prepare.Length
import P256.Proofs.Nonce.Initialize.Prepare.Buffer.Stores
import P256.Proofs.Nonce.Initialize.Prepare.Buffer.Arguments

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Encoding.Serialize

structure CallReady [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop
    extends LengthReady initial s boundary where
  inputPointer : s.regValue .rdi = initial.regValue .rcx
  outputPointer : s.regValue .rdx = stackPtr s + 104
  limbs : s.regValue .rcx = 4
  requestedBits : s.regValue .r8 = 256

theorem buffer_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (state : LengthReady initial s boundary) (rip : s.RIP = 0x107916) :
    ∃ t, CallReady initial t boundary ∧ t.RIP = 0x107955 := by
  obtain ⟨a, af, ap, ag⟩ := Buffer.stores_correct pre state.stage rip
  obtain ⟨t, tf, tp, td, tc, ti, tb, tg⟩ := Buffer.arguments_correct pre af ap
  have spa : stackPtr a = stackPtr s := by rw [af.rsp, state.stage.rsp]
  have spt : stackPtr t = stackPtr s := by rw [tf.rsp, state.stage.rsp]
  have total := ag.trans tg
  have word (offset : Nat) (ho : offset = 168 ∨ offset = 176 ∨ offset = 184 ∨ offset = 192) :
      memLoad t.external (stackPtr t + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) 64 := by
    rw [spt]
    apply read_mem_of_agrees total
    intro i hi c hc
    simp only [Buffer.storeComponents, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals rcases ho with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel
  have frame : LengthReady initial t boundary := by
    refine ⟨tf,
      (word 192 (.inr (.inr (.inr rfl)))).trans state.output,
      (word 184 (.inr (.inr (.inl rfl)))).trans state.secret,
      (word 176 (.inr (.inl rfl))).trans state.length,
      (word 168 (.inl rfl)).trans state.entropy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (total.read (n := 64) (r := 0) (by simp [Buffer.storeComponents])).trans state.source
    · exact (total.read (n := 64) (r := 15) (by simp [Buffer.storeComponents])).trans state.order0
    · exact (total.read (n := 64) (r := 14) (by simp [Buffer.storeComponents])).trans state.order1
    · exact (total.read (n := 64) (r := 13) (by simp [Buffer.storeComponents])).trans state.order2
    · exact (total.read (n := 64) (r := 3) (by simp [Buffer.storeComponents])).trans state.order3
    · exact (total.read (n := 64) (r := 6) (by simp [Buffer.storeComponents])).trans state.count
    · exact (total.read (n := 64) (r := 9) (by simp [Buffer.storeComponents])).trans state.bits
    · exact (total.read (n := 64) (r := 5) (by simp [Buffer.storeComponents])).trans state.shift
  refine ⟨t, ⟨frame, ?_, ?_, tc, ?_⟩, tp⟩
  · exact ti.trans ((ag.read (n := 64) (r := 0) (by simp [Buffer.storeComponents])).trans state.source)
  · simpa only [spa, spt] using td
  · have nine : a.regValue .r9 = 256 :=
      (ag.read (n := 64) (r := 9) (by simp [Buffer.storeComponents])).trans state.bits
    simpa [nine] using tb

end P256.Proofs.Nonce.Initialize.Prepare
