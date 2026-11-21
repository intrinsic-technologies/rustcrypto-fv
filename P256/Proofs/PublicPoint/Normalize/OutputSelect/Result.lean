import P256.Proofs.PublicPoint.Normalize.OutputSelect.Pre
import P256.Proofs.Program.FieldCall.Result

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.OutputSelect

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open Program Program.ScalarFrame X86 X86.Machine X86.UserProcess X86Proofs

theorem child_stack_sub [Bindings] {s v : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s v 65 3352 1952) {saved : Nat} (bound : saved ≤ 1944) :
    ∀ a, (Stack.region v 128).Contains a → (Work.region s 3352 saved).Contains a := by
  have hb := stack_bounds pre.stack
  have hs : (stackPtr v).toNat = (stackPtr s).toNat - 1952 := by
    rw [state.rsp]; exact stack_sub_toNat pre.stack (by decide)
  intro a ha
  change (stackPtr v).toNat - 128 ≤ a ∧ a < (Stack.region v 128).start + (Stack.region v 128).size at ha
  rw [stack_region_end,hs] at ha
  change (stackPtr s).toNat - 3352 ≤ a ∧ a < (stackPtr s).toNat - 3352 + (3352-saved)
  constructor <;> omega

theorem result_frame [Bindings] {s v u : RamState} {boundary : ReturnBoundary} {offset : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s v 65 3352 1952)
    (result : CalleeResult v u boundary 32 128)
    (output : v.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 offset)
    (bound : offset + 32 ≤ 65) :
    MemoryWriteFrame v u #v[registerRegion s .rdi 65,workRegion s 3352] := by
  intro a ha
  apply result.frame a
  intro r hr hin
  have hr' : r = registerRegion v .rdi 32 ∨ r = Stack.region v 128 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact ha _ (by simp) (output_sub pre output bound _ hin)
  · exact ha (workRegion s 3352) (by simp) (child_stack_sub pre state (saved := 48) (by decide) _ hin)

theorem after_result [Bindings] {s v u : RamState} {boundary : ReturnBoundary} {offset : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s v 65 3352 1952)
    (result : CalleeResult v u boundary 32 128)
    (output : v.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 offset)
    (bound : offset + 32 ≤ 65) : FrameState s u 65 3352 1944 := by
  have hw := result_frame pre state result output bound
  refine ⟨result.bindingsSupported,result.machine,result.loaded,result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (output_work_frame pre hw),?_,?_,?_,
    result.mxcsr.trans state.mxcsr,result.fp87.trans state.fp87⟩
  · have hsp : stackPtr u = stackPtr v + 8 := result.rsp
    rw [hsp,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · intro entry he
    have hb : entry.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre (by decide) hw hb (by omega)).trans (state.saved entry he)
  · have h := output_work_read pre (by decide) hw (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem result_stack_byte [Bindings] {s v u : RamState} {boundary : ReturnBoundary}
    {outputOffset offset len i : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s v 65 3352 1952)
    (result : CalleeResult v u boundary 32 128)
    (output : v.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 outputOffset)
    (bound : outputOffset + 32 ≤ 65) (ho : offset ≤ 1944) (hlen : len ≤ offset + 8)
    (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      v.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have hb := stack_bounds pre.stack
  have hs := stack_sub_toNat pre.stack (offset := offset) (by omega)
  have ha : (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat - offset + i := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by rw [hs]; omega),hs]
  apply result.frame
  intro r hr hin
  have hr' : r = registerRegion v .rdi 32 ∨ r = Stack.region v 128 := by simpa using hr
  rcases hr' with rfl | rfl
  · apply pre.separation 1 2 (by decide) _ (output_sub pre output bound _ hin)
    exact stack_contains pre (by omega) hlen ⟨i,hi,rfl⟩
  · have h := child_stack_sub pre state (saved := 1944) (by decide) _ hin
    change (stackPtr s).toNat - 3352 ≤ _ ∧ _ < (stackPtr s).toNat - 3352 + (3352-1944) at h
    rw [ha] at h
    omega

theorem work_sub_stack [Bindings] {s : RamState} {boundary : ReturnBoundary} {saved a : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (ha : (Work.region s 3352 saved).Contains a) : (Stack.region s 3352).Contains a := by
  have hb := stack_bounds pre.stack
  change (stackPtr s).toNat - 3352 ≤ a ∧ a < (stackPtr s).toNat - 3352 + (3352-saved) at ha
  change (stackPtr s).toNat - 3352 ≤ a ∧ a < (Stack.region s 3352).start + (Stack.region s 3352).size
  rw [stack_region_end]
  constructor <;> omega

theorem result_output_byte [Bindings] {s v u : RamState} {boundary : ReturnBoundary}
    {outputOffset i : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s v 65 3352 1952)
    (result : CalleeResult v u boundary 32 128)
    (output : v.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 outputOffset)
    (bound : outputOffset + 32 ≤ 65) (hi : i < 65)
    (apart : i < outputOffset ∨ outputOffset + 32 ≤ i) :
    u.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      v.external[s.regValue .rdi + BitVec.ofNat 64 i]? := by
  have ha := output_address pre (offset := i) (len := 1) (by omega)
  have hd : (v.regValue .rdi).toNat = (s.regValue .rdi).toNat + outputOffset := by
    rw [output]; exact output_address pre bound
  apply result.frame
  intro r hr hin
  have hr' : r = registerRegion v .rdi 32 ∨ r = Stack.region v 128 := by simpa using hr
  rcases hr' with rfl | rfl
  · change (v.regValue .rdi).toNat ≤ _ ∧ _ < (v.regValue .rdi).toNat + 32 at hin
    rw [ha,hd] at hin
    omega
  · exact pre.separation 1 2 (by decide) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      (work_sub_stack pre (child_stack_sub pre state (saved := 1944) (by decide) _ hin))

theorem call_output_byte [Bindings] {s t v : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64} {i : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944)
    (effect : (callEffect target ret t).Holds t v) (hi : i < 65) :
    v.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      t.external[s.regValue .rdi + BitVec.ofNat 64 i]? := by
  apply FieldCall.field_call_work_frame (frameOffset := 1944) pre state (by decide) (by decide) effect
  intro r hr hin
  have he : r = workRegion s 3352 := by simpa using hr
  subst r
  exact pre.separation 1 2 (by decide) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
    (work_sub_stack pre hin)

end P256.Proofs.PublicPoint.Normalize.OutputSelect
