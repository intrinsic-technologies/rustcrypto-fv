import P256.Proofs.Projective.Multiply.Machine.Radix.State
import P256.Proofs.Program.Push
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem prologue_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10b720 32 65 136) :
    ∃ t, Advances boundary 3 s t ∧ State s t ∧ t.RIP = 0x10b728 ∧
      t.regValue .rbx = s.regValue .rdi ∧ t.regValue .rsi = s.regValue .rsi ∧
      t.external = memStore s.external (stackPtr s - 8) (s.regValue .rbx) := by
  obtain ⟨u, run, ready, loaded, rip, rsp, ag, mem⟩ := push_exists pre.stack
    (pre.avoids _ (by simp)) pre.outerBoundary
    (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h)
    3 0 0xb720 (by simp) pre.rip (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨v, step, rv, sub⟩ :=
    (sub_r64_imm8_effect_step 0x10b721 0x48 0xec 112
      (by constructor <;> decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xb721 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb725 (by decide)))
  change (subR64Imm8Effect 0x10b721 4 112 u).Holds u v at sub
  have mv : v.external = u.external := sub.agrees.external
    (by simp [subR64Imm8Effect_components, Component.Covers])
  have lv : ProgramLoaded v := by intro a b hb; rw [mv]; exact loaded a b hb
  obtain ⟨t, last, rt, mov⟩ :=
    (mov_r64_r64_effect_step 0x10b725 0x48 0xfb
      (by constructor <;> decide) rfl).advances rv
      (programText_slice (programLoaded_codeIn lv) 0xb725 _
        (by decide) (by decide +kernel)) sub.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb728 (by decide)))
  change (movR64R64Effect 0x10b725 3 7 v).Holds v t at mov
  have mt : t.external = v.external := mov.agrees.external
    (by simp [movR64R64Effect_components, Component.Covers])
  have spv : stackPtr v = stackPtr s - 120 := by
    have h : stackPtr v = stackPtr u - 112 := sub.writes
    rw [h, rsp, BitVec.sub_sub]
    rfl
  have spt : stackPtr t = stackPtr s - 120 :=
    (mov.agrees.read (n := 64) (r := 4) (by simp)).trans spv
  have all := (ag.trans sub.agrees).trans mov.agrees
  have narrow : AgreesExcept (components s) s t := by
    apply all.widen
    · intro c hc hm
      simp only [subR64Imm8Effect_components, movR64R64Effect_components,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl|rfl|rfl)|(rfl|rfl|rfl))|(rfl|rfl)
      all_goals simp_all [components, registers, Component.isMem]
    · intro a c hc ha
      simp only [subR64Imm8Effect_components, movR64R64Effect_components,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl|rfl|rfl)|(rfl|rfl|rfl))|(rfl|rfl)
      all_goals try exact ha.elim
      obtain ⟨i,hi,rfl⟩ := ha
      refine ⟨.mem (stackPtr s - 136) 136, by simp [components], 128+i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [← BitVec.add_assoc (-136)]
      rfl
  have memory : t.external = memStore s.external (stackPtr s - 8) (s.regValue .rbx) :=
    mt.trans (mv.trans mem)
  refine ⟨t, (run.trans step).trans last, ⟨rt, narrow, spt, ?_⟩, mov.rip, ?_, ?_, memory⟩
  · rw [memory, memLoad_memStore_same _ _ _ (by decide) (by decide)]
  · have out : v.regValue .rdi = s.regValue .rdi :=
      (ag.trans sub.agrees).read (n := 64) (r := 7) (by simp)
    exact mov.writes.trans out
  · exact all.read (n := 64) (r := 6) (by simp)

end P256.Proofs.Projective.Multiply.Machine.Radix
