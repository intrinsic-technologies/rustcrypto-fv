import P256.Proofs.Nonce.Fill.Tail.Compare.Zero.Call
import P256.Proofs.Nonce.Fill.CallResult.Frame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem zero_return [Bindings] {initial s t u : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : ZeroPrepared initial s orderAddress state)
    (effect : (callEffect (fun _ => 0x119270) 0x1075e5 s).Holds s t)
    (result : Equal.Result t u boundary) : Compared initial u orderAddress state := by
  have combined := effect.agrees.trans result.agrees
  have rsp : stackPtr u = stackPtr s := result.rsp.trans (callEffect_stack effect).2
  have agrees : AgreesExcept (Equal.clobbers ++ [.mem (pushAddr s) 8]) s u := by
    apply combined.narrow
    intro c member absent
    have eq : c = .reg 4 := by
      simp only [pushEffect_components, Equal.clobbers, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at member absent
      rcases member with (h | h | h) | (h | h | h | h | h | h | h | h) | h <;> simp_all
    subst c
    exact rsp
  have writes : WritesWithin (Equal.clobbers ++ [.mem (pushAddr s) 8]) (workRegions initial) := by
    intro c member a cover
    simp only [Equal.clobbers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact cover.elim
    refine ⟨ScalarFrame.workRegion initial 2096, by simp [workRegions], ?_⟩
    rw [call_address input.toFrame] at cover
    exact ScalarFrame.work_contains pre.toCalleePre (offset := 240) (len := 8)
      (by decide) (by decide) cover
  have frame := input.toFrame.after_effect pre result.ready agrees writes
    (by simp [Equal.clobbers])
  have reads : ∀ offset n : Nat, offset ≤ 232 → n / 8 ≤ offset + 8 →
      memLoad u.external (stackPtr initial - BitVec.ofNat 64 offset) n =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) n := by
    intro offset n bound span
    rw [result.memory]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (ScalarFrame.call_byte (frameOffset := 232) (by decide) input.rsp effect bound span hi)
  have slots := input.toSlots.of_stack_reads reads
  have generator : GeneratorAt u (initial.regValue .rdi) orderAddress (nextState state) := by
    have h := call_generator pre input.toFrame effect input.generator
    simpa only [GeneratorAt, DrbgAt, Nat256At, result.memory] using h
  refine ⟨⟨frame, slots,
    (agrees.read (n := 64) (r := 13) (by simp [Equal.clobbers])).trans input.r13,
    (agrees.read (n := 64) (r := 15) (by simp [Equal.clobbers])).trans input.r15, generator⟩, ?_⟩
  have integer : Nat256At t (frameBase initial + 72) (nextCandidate state).1 := zero_call_nat256 input.toFrame effect (off := 72) (by decide) input.integer
  simpa only [Nat256At, result.memory] using integer

end P256.Proofs.Nonce.Fill.Tail.Compare
