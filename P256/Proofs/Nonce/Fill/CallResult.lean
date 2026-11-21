import P256.Proofs.Nonce.Fill.CallResult.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

variable [Bindings] {initial s called t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : State}

theorem Frame.after_drbg_call (pre : Pre initial boundary orderAddress original)
    (frame : Frame initial s) {entry ret : BitVec 64} {reserve : Nat}
    (capacity : reserve ≤ 1856)
    (effect : (callEffect (fun _ => entry) ret s).Holds s called)
    (pointer : s.regValue .rdi = initial.regValue .rdi + 8)
    (result : CalleeResult called t boundary 64 reserve) : Frame initial t := by
  have memory := call_result_memory pre frame capacity effect pointer result
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (effect.agrees.grow a (frame.allocated a ha)),
    memoryWriteFrame_trans frame.frame (work_frame pre (call_frame_work pre memory)),
    result.rsp.trans ((callEffect_stack effect).2.trans frame.rsp), ?_, ?_,
    result.mxcsr.trans ((effect.agrees.mxcsr (by simp)).trans frame.mxcsr),
    result.fp87.trans ((effect.agrees.fcw (by simp)).trans frame.fp87)⟩
  · intro item member
    have bound : item.2 ≤ 232 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (call_frame_read pre memory bound (by omega)).trans (frame.saved item member)
  · have h := call_frame_read pre memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans frame.returnAddress

theorem call_stack_sub (pre : Pre initial boundary orderAddress original)
    {a : Nat} (inside : (MemoryRegion.mk ((stackPtr initial).toNat - 2096) 1864).Contains a) :
    (Stack.region initial 2096).Contains a := by
  have bounds := stack_bounds pre.stack
  change (stackPtr initial).toNat - 2096 ≤ a ∧
    a < (stackPtr initial).toNat - 2096 + 1864 at inside
  change (stackPtr initial).toNat - 2096 ≤ a ∧
    a < (Stack.region initial 2096).start + (Stack.region initial 2096).size
  rw [stack_region_end]
  constructor <;> omega

theorem call_order_apart (pre : Pre initial boundary orderAddress original)
    {region : MemoryRegion} (member : region ∈ callRegions initial) :
    (MemoryRegion.mk orderAddress.toNat 32).Disjoint region := by
  have cases : region = MemoryRegion.mk (initial.regValue .rdi + 8).toNat 64 ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - 2096) 1864 := by
    simpa [callRegions] using member
  rcases cases with rfl | rfl
  · exact fun a ha hb => pre.orderDisjoint _ (by simp) a ha (drbg_sub pre hb)
  · exact fun a ha hb => pre.orderDisjoint _ (by simp) a ha (call_stack_sub pre hb)

theorem call_output_apart (pre : Pre initial boundary orderAddress original)
    {region : MemoryRegion} (member : region ∈ callRegions initial) :
    (registerRegion initial .rsi 32).Disjoint region := by
  have cases : region = MemoryRegion.mk (initial.regValue .rdi + 8).toNat 64 ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - 2096) 1864 := by
    simpa [callRegions] using member
  rcases cases with rfl | rfl
  · exact fun a ha hb => pre.separation 0 1 (by decide) a ha (drbg_sub pre hb)
  · exact fun a ha hb => pre.separation 0 2 (by decide) a ha (call_stack_sub pre hb)

theorem call_header_apart (pre : Pre initial boundary orderAddress original)
    {region : MemoryRegion} (member : region ∈ callRegions initial) :
    (MemoryRegion.mk (initial.regValue .rdi).toNat 8).Disjoint region := by
  have cases : region = MemoryRegion.mk (initial.regValue .rdi + 8).toNat 64 ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - 2096) 1864 := by
    simpa [callRegions] using member
  rcases cases with rfl | rfl
  · intro a ha hb
    change (initial.regValue .rdi).toNat ≤ a ∧ a < (initial.regValue .rdi).toNat + 8 at ha
    change (initial.regValue .rdi + 8).toNat ≤ a ∧
      a < (initial.regValue .rdi + 8).toNat + 64 at hb
    rw [drbg_address pre] at hb
    omega
  · intro a ha hb
    apply pre.separation 1 2 (by decide) a ?_ (call_stack_sub pre hb)
    change (initial.regValue .rdi).toNat ≤ a ∧ a < (initial.regValue .rdi).toNat + 8 at ha
    change (initial.regValue .rdi).toNat ≤ a ∧ a < (initial.regValue .rdi).toNat + 72
    constructor <;> omega

theorem generator_after_call (pre : Pre initial boundary orderAddress original)
    (memory : MemoryWriteFrame s t (callRegions initial))
    {before after : State}
    (generator : GeneratorAt s (initial.regValue .rdi) orderAddress before)
    (drbg : DrbgAt t (initial.regValue .rdi + 8) after) :
    GeneratorAt t (initial.regValue .rdi) orderAddress after := by
  refine ⟨?_, ⟨generator.2.1.1, ?_⟩, drbg⟩
  · apply Eq.trans (frame_memLoad memory (fun _ hr => call_header_apart pre hr) ?_
      (Nat.le_refl _) (Nat.le_refl _)) generator.1
    have bound : (initial.regValue .rdi).toNat + 72 < 2^32 := pre.outputBounded
    change (initial.regValue .rdi).toNat + 8 < 2^32
    omega
  · intro i hi
    exact (frame_read memory (fun _ hr => call_order_apart pre hr)
      (memoryRegion_contains_add pre.orderBounded (Nat.le_refl _) (Nat.le_refl _) hi)).trans
      (generator.2.1.2 i hi)

end P256.Proofs.Nonce.Fill
