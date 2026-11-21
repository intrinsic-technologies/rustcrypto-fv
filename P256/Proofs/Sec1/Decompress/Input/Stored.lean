import P256.Proofs.Sec1.Decompress.Input.Decode
import P256.Proofs.Sec1.Decompress.Input.Stores
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC
open P256.Proofs.SecretKeyFromBytes.Scalar

structure Stored [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop
    extends Frame s t where
  rip : t.RIP = 0x10fc44
  parity : memLoad t.external (stackPtr s - 332) 32 = BitVec.ofNat 32 odd.toNat
  output : t.regValue .rdi = s.regValue .rdi
  high : t.regValue .rax = BitVec.ofNat 64 (x / 2^192)
  third : t.regValue .rcx = BitVec.ofNat 64 (x / 2^128)
  second : t.regValue .r8 = BitVec.ofNat 64 (x / 2^64)
  low : t.regValue .rdx = BitVec.ofNat 64 x
  raw : Nat256At t (stackPtr s - 328) x

theorem store [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd)
    (state : Decoded s u (Encoding.octetsToNat bytes) odd) :
    ∃ fuel t, Advances boundary fuel u t ∧ Stored s t (Encoding.octetsToNat bytes) odd := by
  have addr (k : Nat) (hk : k ≤ 408) :
      stackPtr u + BitVec.ofNat 64 k = stackPtr s - BitVec.ofNat 64 (408-k) :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) hk
  have addr80 : stackPtr u + 80 = stackPtr s - 328 := addr 80 (by decide)
  have addr88 : stackPtr u + 88 = stackPtr s - 320 := addr 88 (by decide)
  have addr96 : stackPtr u + 96 = stackPtr s - 312 := addr 96 (by decide)
  have addr104 : stackPtr u + 104 = stackPtr s - 304 := addr 104 (by decide)
  have hp : InputStorePre u := by
    refine ⟨state.rip, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals first | rw [addr80] | rw [addr88] | rw [addr96] | rw [addr104]
      all_goals
        exact writable_of_grow (stack_sub_writable8 pre.stack
          (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
          (by decide) (by decide)) state.allocated
    · intro i hi off len bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals first
        | exact ScalarFrame.stack_code pre.toCalleePre state.toFrameState (offset := 80) (by decide) (by decide) bound
        | exact ScalarFrame.stack_code pre.toCalleePre state.toFrameState (offset := 88) (by decide) (by decide) bound
        | exact ScalarFrame.stack_code pre.toCalleePre state.toFrameState (offset := 96) (by decide) (by decide) bound
        | exact ScalarFrame.stack_code pre.toCalleePre state.toFrameState (offset := 104) (by decide) (by decide) bound
  obtain ⟨fuel, t, run, ready, _, effect⟩ := input_store_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfc30 inputStoreBytes
      (by decide) (by decide +kernel)) hp
  have writes : WritesWithin (inputStoreEffect u).components
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro c hc a ha
    simp only [inputStoreEffect, Effect.components, List.map_cons, Write.component_mem,
      List.map_nil, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      change (Component.mem (stackPtr u + _) 8).Covers a at ha
      first | rw [addr80] at ha | rw [addr88] at ha | rw [addr96] at ha | rw [addr104] at ha
      exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha⟩
  have frame := state.toFrameState.after_effect pre.toCalleePre (by decide) ready effect.agrees
    writes (by simp [inputStoreEffect, Effect.components])
  have read (r : BitVec 5) : (Operand.reg r : Operand 64).read t =
      (Operand.reg r : Operand 64).read u :=
    effect.agrees.read (by simp [inputStoreEffect, Effect.components])
  refine ⟨fuel, t, run, ⟨frame, effect.rip, ?_, (read 7).trans state.output,
    (read 0).trans state.high, (read 1).trans state.third,
    (read 8).trans state.second, (read 2).trans state.low, ?_⟩⟩
  · have parityAddr := addr 76 (by decide)
    change stackPtr u + 76 = stackPtr s - 332 at parityAddr
    rw [← parityAddr]
    apply Eq.trans (P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees effect.agrees _ ?_)
      (parityAddr ▸ state.parity)
    intro i hi c hc ha
    simp only [inputStoreEffect, Effect.components, List.map_cons, Write.component_mem,
      List.map_nil, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨j, hj, he⟩ := ha
      exact RangeApart.offsets (stackPtr u) (a := _) (b := 76) (len := 8) (count := 4)
        (by decide) (by decide) (.inr (by decide)) j hj i hi he.symm
  · have bound := P256.Proofs.SecretKeyFromBytes.Encoding.octetsToNat_lt bytes
    rw [pre.size] at bound
    have bound' : Encoding.octetsToNat bytes < 2^256 := by exact bound
    apply nat256At_of_memLoad_limbs bound'
    · intro i hi
      exact frame.allocated _ ((stack_sub_readable pre.stack
        (offset := 328) (len := 32) (by decide) (by decide)).mem i hi)
    · intro j hj
      have eqj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      have vals := effect.writes
      change memLoad t.external (stackPtr u + 80) 64 = u.regValue .rdx ∧
        memLoad t.external (stackPtr u + 88) 64 = u.regValue .r8 ∧
        memLoad t.external (stackPtr u + 96) 64 = u.regValue .rcx ∧
        memLoad t.external (stackPtr u + 104) 64 = u.regValue .rax at vals
      have base := addr 80 (by decide)
      change stackPtr u + 80 = stackPtr s - 328 at base
      rw [← base, BitVec.add_assoc]
      rcases eqj with rfl | rfl | rfl | rfl
      · simpa only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, BitVec.add_zero] using vals.1.trans state.low
      · exact vals.2.1.trans state.second
      · exact vals.2.2.1.trans state.third
      · exact vals.2.2.2.trans state.high

end P256.Proofs.Sec1.Decompress.Input
