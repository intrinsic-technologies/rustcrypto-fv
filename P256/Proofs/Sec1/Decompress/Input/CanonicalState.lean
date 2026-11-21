import P256.Proofs.Sec1.Decompress.Input.Stored
import P256.Proofs.Sec1.Decompress.Input.Canonical
import P256.Proofs.Sec1.Decompress.Input.Canonical.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC
open P256.Proofs.SecretKeyFromBytes.Scalar

structure CanonicalState [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop
    extends Frame s t where
  rip : t.RIP = 0x10fcd0
  parity : memLoad t.external (stackPtr s - 332) 32 = BitVec.ofNat 32 odd.toNat
  output : memLoad t.external (stackPtr s - 224) 64 = s.regValue .rdi
  valid : t.regValue .rbx = if x < P256.Spec.Operations.domain.p then 1 else 0
  raw : Nat256At t (stackPtr s - 328) x
  r14 : t.regValue .r14 = 0xffffffff00000001

theorem canonical_state [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd)
    (state : Stored s u (Encoding.octetsToNat bytes) odd) :
    ∃ fuel t, Advances boundary fuel u t ∧
      CanonicalState s t (Encoding.octetsToNat bytes) odd := by
  have addr (k : Nat) (hk : k ≤ 408) :
      stackPtr u + BitVec.ofNat 64 k = stackPtr s - BitVec.ofNat 64 (408-k) :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) hk
  have hp : CanonicalPre 0x10fc44 u := by
    refine ⟨⟨state.rip, ?_, ?_⟩, ?_, ?_⟩
    · rw [state.rsp]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · intro a ha hin
      rw [state.rsp] at ha
      exact pre.avoids _ (by simp) a
        (ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) ha) (.inl hin)
    · rw [addr 184 (by decide)]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · intro a ha hin
      rw [addr 184 (by decide)] at ha
      exact pre.avoids _ (by simp) a
        (ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) ha) (.inl hin)
  have value : (canonicalInput u).toNat = Encoding.octetsToNat bytes := by
    change (Limbs.mk (u.regValue .rdx) (u.regValue .r8)
      (u.regValue .rcx) (u.regValue .rax)).toNat = _
    rw [state.low, state.second, state.third, state.high]
    exact limbs_ofNat_toNat _ state.raw.1
  obtain ⟨fuel, t, run, ready, _, ht, agrees, valid, output, r14⟩ :=
    canonical_correct pre.outerBoundary (readyToStep state.machine state.bindingsSupported)
      state.loaded hp
  have writes : WritesWithin (canonicalFrame u)
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro c hc a ha
    simp only [canonicalFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · rw [state.rsp] at ha
      exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha⟩
    · rw [addr 184 (by decide)] at ha
      exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha⟩
  have frame := state.toFrameState.after_effect pre.toCalleePre (by decide) ready agrees writes
    (by simp [canonicalFrame])
  refine ⟨fuel, t, run, ⟨frame, ht.rip, ?_, ?_, ?_, ?_, r14⟩⟩
  · have h := canonical_read agrees (offset := 76) (n := 32)
      (by decide) (.inl (by decide)) (by decide)
    have a76 : stackPtr u + 76 = stackPtr s - 332 := addr 76 (by decide)
    change memLoad t.external (stackPtr u + 76) 32 = memLoad u.external (stackPtr u + 76) 32 at h
    rw [a76] at h
    exact h.trans state.parity
  · rw [addr 184 (by decide)] at output
    exact output.trans state.output
  · rwa [value] at valid
  · refine ⟨state.raw.1, ?_⟩
    intro i hi
    have h := canonical_byte agrees (offset := 80) (len := 32)
      (by decide) (.inl (by decide)) (by decide) hi
    rw [addr 80 (by decide)] at h
    exact h.trans (state.raw.2 i hi)

end P256.Proofs.Sec1.Decompress.Input
