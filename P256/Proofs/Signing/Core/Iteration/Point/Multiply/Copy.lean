import P256.Proofs.Signing.Core.Iteration.Point.Call
import P256.Proofs.Program.Copy

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Multiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open NextNonce (scalarFrame)

theorem copy_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cf4b)
    (source : t.regValue .rsi = frameBase s+528)
    (destination : t.regValue .rdi = frameBase s+1328)
    (count : t.regValue .rdx = 768) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10cf51 ∧
      (∀ i < 768, u.external[frameBase s+1328+BitVec.ofNat 64 i]? =
        t.external[frameBase s+528+BitVec.ofNat 64 i]?) ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r) ∧
      (∀ offset len, offset+len ≤ 2280 → (offset+len ≤ 1328 ∨ 2096 ≤ offset) →
        ∀ i < len, u.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          t.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) := by
  have push : pushAddr t = stackPtr s-2288 := ScalarFrame.scalar_call_address (scalarFrame frame)
  have writable : MemWritable t (pushAddr t) 8 := by
    rw [push]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha h => pre.avoids _ (by simp) a ha (.inr h)) (by decide) (by decide))
      frame.allocated
  have apart : RangeApart (pushAddr t) 8 0x10cf4b 6 := by
    rw [push]
    intro i hi j hj eq
    apply pre.avoids (Stack.region s 4584) (by simp)
      (stackPtr s-2288+BitVec.ofNat 64 i)
      (ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) ⟨i,hi,rfl⟩) (.inl ?_)
    rw [eq]
    have h := inProgram_of_textOffset (0xcf4b+j) (by omega)
    rw [BitVec.ofNat_add,← BitVec.add_assoc] at h
    exact h
  have pointer := memcpy_pointer frame.loaded
  have target : callMemPtr 0x10cf4b (.rip 0xf75a7) t = 0x11c930 := pointer.2
  obtain ⟨v,step,ready,effect⟩ := call_m64_effect_step 0x10cf4b (.rip 0xf75a7)
    trivial rfl rfl t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xcf4b _
      (by decide) (by decide +kernel))
    ⟨⟨⟨rip,writable,apart⟩,by rw [target]; decide⟩,pointer.1⟩
  have next : (0x10cf4b : BitVec 64)+BitVec.ofNat 64 (callMemLen (.rip 0xf75a7)) =
      0x10cf51 := by decide
  have ef : (callEffect (fun _ => 0x11c930) 0x10cf51 t).Holds t v := by
    simpa only [callEffect,pushEffect,target,next] using effect
  have run : Advances boundary 1 t v := Advances.of_step step (.inl (by
    rw [ef.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide))))
  have cp : CalleePre v boundary 0x11c930 768 768 8 :=
    local_call_pre pre frame ready ef (inProgram_of_textOffset 0xcf51 (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
      source destination
  have srcV : v.regValue .rsi = frameBase s+528 :=
    (ef.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have dstV : v.regValue .rdi = frameBase s+1328 :=
    (ef.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  obtain ⟨u,result,copied,_⟩ := memcpy_correct cp
    ((ef.agrees.read (n := 64) (r := 2) (by simp)).trans count) (by decide)
  obtain ⟨fuel,executed⟩ := result.execution
  refine ⟨1+fuel,u,run.trans executed,after_call pre frame ready ef result (by decide)
      (by decide) destination,result.rip.trans (callEffect_stack ef).1,?_,
    call_registers ef result,
    fun offset len bound disjoint => local_result_copy pre frame ef result destination bound (by decide) disjoint⟩
  intro i hi
  have h := copied i hi
  rw [srcV,dstV] at h
  exact h.trans (local_call_copy frame ef (by decide) i hi)

end P256.Proofs.Signing.Core.Iteration.Point.Multiply
