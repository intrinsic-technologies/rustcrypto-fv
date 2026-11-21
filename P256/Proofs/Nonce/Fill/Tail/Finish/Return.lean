import P256.Proofs.Nonce.Fill.Tail.Finish.Call
import P256.Proofs.Nonce.Fill.Work
import P256.Proofs.Nonce.Fill.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure Serialized [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Frame initial s where
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress (Signing.Search.nextState state)
  output : (registerRegion initial .rsi 32).HasBytes s.external
    (Standards.SECG.ECC.Encoding.natToOctets 32 (Signing.Search.nextCandidate state).1)

theorem return_state [Bindings] {initial s t u : RamState}
    {boundary : ReturnBoundary} {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Prepared initial s orderAddress state) (ready : ReadyToStep t)
    (effect : (callEffect (fun _ => 0x106f40) 0x1076fa s).Holds s t)
    (result : Initialize.Conversions.Int2Octets.Result t u boundary
      (Signing.Search.nextCandidate state).1) :
    Serialized initial u orderAddress state ∧ u.RIP = 0x1076fa := by
  have cp := call_pre pre input ready effect
  have agrees := effect.agrees
  have sp : stackPtr t = stackPtr initial - 240 :=
    effect.writes.1.trans (call_address input.toFrame)
  have dx : t.regValue .rdx = initial.regValue .rsi :=
    (agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans input.rdx
  have sameOutput : registerRegion t .rdx 32 = registerRegion initial .rsi 32 := by
    simp only [registerRegion, dx]
  have bounds := stack_bounds pre.stack
  have spn : (stackPtr t).toNat = (stackPtr initial).toNat - 240 := by
    rw [sp]
    exact stack_sub_toNat pre.stack (by decide)
  let writes := #v[registerRegion t .rdx 32, Stack.region t 128]
  have stackSub (a : Nat) (inside : (Stack.region t 128).Contains a) :
      (ScalarFrame.workRegion initial 2096).Contains a := by
    change (stackPtr t).toNat - 128 ≤ a ∧
      a < (Stack.region t 128).start + (Stack.region t 128).size at inside
    rw [stack_region_end, spn] at inside
    change (stackPtr initial).toNat - 2096 ≤ a ∧ a < (stackPtr initial).toNat - 2096 + 2048
    constructor <;> omega
  have pushWrites : WritesWithin (callEffect (fun _ => 0x106f40) 0x1076fa s).components writes := by
    intro c member a inside
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact inside.elim
    · obtain ⟨j, hj, rfl⟩ := inside
      refine ⟨Stack.region t 128, by simp [writes], ?_⟩
      have pushEq : stackPtr t = pushAddr s := effect.writes.1
      rw [← pushEq]
      apply memoryRegion_contains_add cp.stack.1 (len := 8) _ _ hj
      · change (stackPtr t).toNat - 128 ≤ (stackPtr t).toNat
        omega
      · rw [stack_region_end]
        exact Nat.le_refl _
    · exact inside.elim
  have frame : MemoryWriteFrame s u writes := by
    intro a ha
    exact (result.frame a ha).trans (agrees.memoryWriteFrame pushWrites a ha)
  have workFrame : MemoryWriteFrame s u (workRegions initial) := by
    intro a ha
    apply frame a
    intro region member inside
    have cases : region = registerRegion t .rdx 32 ∨ region = Stack.region t 128 := by
      simpa [writes] using member
    rcases cases with rfl | rfl
    · rw [sameOutput] at inside
      exact ha _ (by simp [workRegions]) inside
    · exact ha _ (by simp [workRegions]) (stackSub a.toNat inside)
  have generatorApart : ∀ region ∈ writes, (registerRegion initial .rdi 72).Disjoint region := by
    intro region member a ha hb
    have cases : region = registerRegion t .rdx 32 ∨ region = Stack.region t 128 := by
      simpa [writes] using member
    rcases cases with rfl | rfl
    · rw [sameOutput] at hb
      exact pre.separation 0 1 (by decide) a hb ha
    · exact pre.separation 1 2 (by decide) a ha (work_substack pre (stackSub a hb))
  have orderApart : ∀ region ∈ writes, (MemoryRegion.mk orderAddress.toNat 32).Disjoint region := by
    intro region member a ha hb
    have cases : region = registerRegion t .rdx 32 ∨ region = Stack.region t 128 := by
      simpa [writes] using member
    rcases cases with rfl | rfl
    · rw [sameOutput] at hb
      exact pre.orderDisjoint _ (by simp) a ha hb
    · exact pre.orderDisjoint _ (by simp) a ha (work_substack pre (stackSub a hb))
  have finalFrame : Frame initial u := by
    refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
      fun a ha => result.allocated a (agrees.grow a (input.allocated a ha)),
      memoryWriteFrame_trans input.frame (work_frame pre workFrame), ?_, ?_, ?_,
      result.mxcsr.trans ((agrees.mxcsr (by simp)).trans input.mxcsr),
      result.fp87.trans ((agrees.fcw (by simp)).trans input.fp87)⟩
    · exact result.rsp.trans ((callEffect_stack effect).2.trans input.rsp)
    · intro item member
      have bound : item.2 ≤ 48 := by
        simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (work_read pre workFrame bound (by omega)).trans (input.saved item member)
    · have h := work_read pre workFrame (offset := 0) (n := 64) (by decide) (by decide)
      simp only [BitVec.sub_zero] at h
      exact h.trans input.returnAddress
  refine ⟨⟨finalFrame,
    input.generator.of_frame pre.outputBounded pre.orderBounded frame generatorApart orderApart,
    ?_⟩, result.rip.trans (callEffect_stack effect).1⟩
  simpa only [sameOutput, intToOctets_eq] using result.output

end P256.Proofs.Nonce.Fill.Tail.Finish
