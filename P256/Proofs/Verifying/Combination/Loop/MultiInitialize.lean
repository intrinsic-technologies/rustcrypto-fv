import P256.Proofs.Verifying.Combination.Loop.MultiInitializeLength
import P256.Proofs.Verifying.Combination.Loop.MultiIdentity
import P256.Proofs.Verifying.Combination.Loop.MultiBranch
import P256.Proofs.Verifying.Combination.Loop.MultiPointerSetup
import P256.Proofs.Verifying.Combination.Loop.MultiSaveTable
import P256.Proofs.Verifying.Combination.Loop.MultiRegisterSetup
import P256.Proofs.Verifying.Combination.Loop.MultiRoundState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialize_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q : Projective} {u v : Nat}
    (pre : MultiPre s boundary tables digits)
    (leftTable : Table.TableAt s tables (Table.oddTable p))
    (rightTable : Table.TableAt s (tables + 768) (Table.oddTable q))
    (leftDigits : Naf.NafAt s digits u) (rightDigits : Naf.NafAt s (digits + 272) v)
    (hu : u < 2^256) (hv : v < 2^256) :
    ∃ fuel t, Advances boundary fuel s t ∧
      ((max (Naf.digits u).length (Naf.digits v).length = 0 ∧
          Memory s t tables digits p q u v ∧ t.RIP = 0x10f301 ∧
          ProjectiveAt t (stackPtr s - 336) Projective.identity ∧
          memLoad t.external (stackPtr s - 392) 64 = s.regValue .rdi) ∨
       RoundState s t tables digits p q u v
         (max (Naf.digits u).length (Naf.digits v).length) Projective.identity) := by
  obtain ⟨fa, a, runA, memoryA, ripA, axA, dxA, ptrA, indexA, maxA, countA, outA⟩ :=
    entry_maximum pre leftTable rightTable leftDigits rightDigits hu hv
  obtain ⟨fb, b, runB, stateB, ripB, valueB, frameB⟩ :=
    initialize_identity pre memoryA.toFrameState ripA
  have countB : b.regValue .rbx = BitVec.ofNat 64
      (max (Naf.digits u).length (Naf.digits v).length) :=
    (frameB.read (n := 64) (r := 3) (by simp)).trans maxA
  have bound : max (Naf.digits u).length (Naf.digits v).length ≤ 257 :=
    Nat.max_le.mpr ⟨Naf.digits_length u hu, Naf.digits_length v hv⟩
  obtain ⟨c, runC, stateC, ripC, frameC⟩ := initialize_branch pre stateB ripB countB bound
  have frameAC : AgreesExcept [.reg 7, .reg 1, .reg 6,
      .mem (stackPtr s - 336) 96, .flags, .rip] a c := (frameB.trans frameC).mono (by simp)
  have outC : memLoad c.external (stackPtr s - 392) 64 = s.regValue .rdi := by
    rw [memLoad_agrees_apart frameAC]
    · exact outA
    · intro address size h
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
        reduceCtorEq, false_or, or_false] at h
      obtain ⟨rfl, rfl⟩ := h
      exact stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide) (.inr (by decide))
  have valueC : ProjectiveAt c (stackPtr s - 336) Projective.identity :=
    valueB.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?)
      (frameC.external (by simp [Component.Covers])))
  by_cases zero : max (Naf.digits u).length (Naf.digits v).length = 0
  · exact ⟨fa+fb+2, c, (runA.trans runB).trans runC,
      Or.inl ⟨zero, memory_of_frame pre stateC leftTable rightTable leftDigits rightDigits,
        by simpa only [ite_eq_left zero] using ripC, valueC, outC⟩⟩
  have ripC' : c.RIP = 0x10f137 := by simpa only [ite_eq_right zero] using ripC
  have countC : c.regValue .rbx = BitVec.ofNat 64
      (max (Naf.digits u).length (Naf.digits v).length) :=
    (frameAC.read (n := 64) (r := 3) (by simp)).trans maxA
  obtain ⟨fd, d, runD, stateD, ripD, tableD, cursorD, frameD⟩ :=
    initialize_pointers pre stateC ripC'
      ((frameAC.read (n := 64) (r := 0) (by simp)).trans axA)
      ((frameAC.read (n := 64) (r := 2) (by simp)).trans dxA)
      ((frameAC.read (n := 64) (r := 8) (by simp)).trans ptrA)
      ((frameAC.read (n := 64) (r := 9) (by simp)).trans indexA) countC
  obtain ⟨e, runE, stateE, ripE, tableE, frameE⟩ := save_table_pointer pre stateD ripD
  obtain ⟨ff, t, runT, stateT, ripT, flagT, scratchT, frameT⟩ := initialize_registers pre stateE ripE
  have frameCT : AgreesExcept [.reg 9, .reg 13, .reg 1,
      .mem (stackPtr s - 384) 8, .reg 14, .reg 15, .flags, .rip] c t :=
    ((frameD.trans frameE).trans frameT).mono (by simp)
  have valueT : ProjectiveAt t (stackPtr s - 336) Projective.identity := by
    apply valueC.of_bytes_eq
    intro i hi
    apply frameCT.byte
    intro component hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    exact stack_sub_apart pre.stack (a := 384) (b := 336) (by decide) (by decide)
      (by decide) (by decide) (.inl (by decide)) j hj i hi eq.symm
  have totalT : memLoad t.external (stackPtr s - 400) 64 = 2 := by
    have frame : AgreesExcept [.reg 7, .reg 1, .reg 6, .mem (stackPtr s - 336) 96,
        .reg 9, .reg 13, .mem (stackPtr s - 384) 8, .reg 14, .reg 15, .flags, .rip] a t :=
      (frameAC.trans frameCT).mono (by simp)
    rw [memLoad_agrees_apart frame]
    · exact countA
    · intro address size h
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
        reduceCtorEq, false_or, or_false] at h
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      all_goals exact stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide) (.inr (by decide))
  have outputT : memLoad t.external (stackPtr s - 392) 64 = s.regValue .rdi := by
    rw [memLoad_agrees_apart frameCT]
    · exact outC
    · intro address size h
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
        reduceCtorEq, false_or, or_false] at h
      obtain ⟨rfl,rfl⟩ := h
      exact stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide) (.inr (by decide))
  refine ⟨fa+fb+2+fd+1+ff, t,
    ((((runA.trans runB).trans runC).trans runD).trans runE).trans runT, Or.inr ?_⟩
  refine ⟨⟨memory_of_frame pre stateT leftTable rightTable leftDigits rightDigits,
    (frameCT.read (n := 64) (r := 3) (by simp)).trans countC,
    Nat.pos_of_ne_zero zero, Nat.le_refl _, scratchT, valueT, totalT, ?_, outputT⟩,
    ripT, ?_, fun _ => rfl⟩
  · rw [frameT.external (by simp [Component.Covers])]
    exact tableE.trans tableD
  · exact (frameT.read (n := 64) (r := 13) (by simp)).trans
      ((frameE.read (n := 64) (r := 13) (by simp)).trans cursorD)

end P256.Proofs.Verifying.Combination.Loop.Multi
