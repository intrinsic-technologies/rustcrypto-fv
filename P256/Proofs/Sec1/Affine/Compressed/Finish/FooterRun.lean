import P256.Proofs.Sec1.Affine.Compressed.Finish.Footer
import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Memory.LoadByte
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish.Footer

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open ScalarFrame

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x1101fb) (output : t.regValue .rbx = s.regValue .rdi) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      (∀ i < 64, u.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
        t.external[s.regValue .rdi + BitVec.ofNat 64 i]?) ∧
      memLoad u.external (s.regValue .rdi+64) 8 = (t.regValue .rax).setWidth 8 ∧
      memLoad u.external (s.regValue .rdi+72) 8 = (t.regValue .r14).setWidth 8 := by
  have cp : ResultStorePre t := by
    refine ⟨rip,?_,?_⟩
    · intro i hi
      change MemWritable t (t.regValue .rbx+i) 1
      rw [output]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl
      · have w := (output_writable pre.toCalleePre (by decide) state.allocated).add 64 (len := 1) (by decide)
        exact ⟨w.low, w.mem, w.tables⟩
      · have w := (output_writable pre.toCalleePre (by decide) state.allocated).add 72 (len := 1) (by decide)
        exact ⟨w.low, w.mem, w.tables⟩
    · intro i hi off len hb
      change RangeApart (t.regValue .rbx+i) 1 _ _
      rw [output]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl
      all_goals exact P256.Proofs.Common.Instructions.RangeApart.add_left (output_code pre.toCalleePre hb) _ (by decide)
  obtain ⟨fuel,a,runA,ready,_,effect⟩ := result_store boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x101fb resultStoreBytes (by decide) (by decide +kernel)) cp
  have agrees : AgreesExcept [.mem (s.regValue .rdi+64) 1,.mem (s.regValue .rdi+72) 1,.rip] t a := by
    have h := effect.agrees
    simp only [resultStoreEffect, Effect.components, List.map_cons,List.map_nil,
      Write.component,Operand.component,List.append_nil,List.cons_append,List.nil_append] at h
    change AgreesExcept [.mem (t.regValue .rbx+64) 1,.mem (t.regValue .rbx+72) 1,.rip] t a at h
    rwa [output] at h
  have writes : WritesWithin [.mem (s.regValue .rdi+64) 1,.mem (s.regValue .rdi+72) 1,.rip]
      #v[registerRegion s .rdi 80,workRegion s 3360] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨_,by simp,output_contains pre.toCalleePre (by decide) ha⟩
    · exact ⟨_,by simp,output_contains pre.toCalleePre (by decide) ha⟩
    · exact ha.elim
  have frame := state.after_effect pre.toCalleePre (by decide) ready agrees writes (by simp)
  have values := effect.writes
  change memLoad a.external (t.regValue .rbx+64) 8 = (t.regValue .rax).setWidth 8 ∧
    memLoad a.external (t.regValue .rbx+72) 8 = (t.regValue .r14).setWidth 8 at values
  rw [output] at values
  obtain ⟨u,runU,readyU,effectU⟩ := (jmp_rel32_effect_step 0x110202 0xb1b (by decide)).advances ready
    (programText_slice (programLoaded_codeIn frame.loaded) 0x10202 _ (by decide) (by decide +kernel))
    effect.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10d22 (by decide)))
  have jump : AgreesExcept [.rip] a u := effectU.agrees
  have memory := jump.external (by simp [Component.Covers])
  refine ⟨fuel+1,u,runA.trans runU,frame.after_registers readyU jump (by simp [Component.Covers]) (by simp),effectU.rip,?_,?_,?_⟩
  · intro i hi
    rw [memory]
    apply agrees.byte
    intro c hc ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨j,hj,he⟩ := ha
      have zero : j = 0 := by omega
      subst j
      simp only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.add_right_inj] at he
      have h := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at h
      omega
  · rw [memory]; exact values.1
  · rw [memory]; exact values.2

end P256.Proofs.Sec1.Affine.Compressed.Finish.Footer
