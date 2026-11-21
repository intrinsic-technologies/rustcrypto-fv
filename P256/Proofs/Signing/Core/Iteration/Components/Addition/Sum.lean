import P256.Proofs.Signing.Core.Iteration.Components.Addition.Sum.Execution
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Choice.Run

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Field (BinaryFieldPre)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Program (memoryRegion_memReadable
  programText_slice programLoaded_codeIn)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem sum_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a b : Nat}
    (pre : BinaryFieldPre s boundary 0x113310 64) (state : FrameState s t)
    (rip : t.RIP = 0x11392e)
    (rsi : t.regValue .rsi = s.regValue .rsi)
    (rdx : t.regValue .rdx = s.regValue .rdx)
    (output : t.regValue .rdi = s.regValue .rdi)
    (modulus : t.regValue .rcx = 0x2025e0)
    (left : Nat256At t (t.regValue .rsi) a)
    (right : Nat256At t (t.regValue .rdx) b) :
    ∃ fuel u, Advances boundary fuel t u ∧ SumState s u a b := by
  have blockPre : Sum.BlockPre t := by
    refine ⟨rip,?_,?_,writable_byte pre.toCalleePre state (by decide),?_⟩
    · intro i hi
      change MemReadable t (t.regValue .rsi+i) 8
      rw [rsi]
      have readable (j : Nat) (bound : j+8 ≤ 32) :
          MemReadable t (s.regValue .rsi+BitVec.ofNat 64 j) 8 :=
        by
        apply Program.readable_of_grow (s := s) _ state.allocated
        have hb : (s.regValue .rsi).toNat+32 < 2^32 := pre.inputBounded
        have he := toNat_add_ofNat (s.regValue .rsi) j (by omega)
        apply memoryRegion_memReadable pre.inputBounded pre.inputAllocated
        · change (s.regValue .rsi).toNat ≤ _
          rw [he]
          omega
        · change _ ≤ (s.regValue .rsi).toNat+32
          rw [he]
          omega
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact readable 0 (by decide)
      · exact readable 8 (by decide)
      · exact readable 16 (by decide)
      · exact readable 24 (by decide)
    · intro i hi
      change MemReadable t (t.regValue .rdx+i) 8
      rw [rdx]
      have readable (j : Nat) (bound : j+8 ≤ 32) :
          MemReadable t (s.regValue .rdx+BitVec.ofNat 64 j) 8 := by
        apply P256.Proofs.Program.readable_of_grow (s := s) _ state.allocated
        have hb : (s.regValue .rdx).toNat+32 < 2^32 := pre.rightBounded
        have he := toNat_add_ofNat (s.regValue .rdx) j (by omega)
        apply memoryRegion_memReadable pre.rightBounded pre.rightAllocated
        · change (s.regValue .rdx).toNat ≤ _
          rw [he]
          omega
        · change _ ≤ (s.regValue .rdx).toNat+32
          rw [he]
          omega
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact readable 0 (by decide)
      · exact readable 8 (by decide)
      · exact readable 16 (by decide)
      · exact readable 24 (by decide)
    · intro offset len bound
      exact stack_code pre.toCalleePre state (by decide) bound
  obtain ⟨fuel,u,run,ready,_,effect⟩ := Sum.correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1392e Sum.bytes
      (by decide +kernel) (by decide +kernel)) blockPre
  have writes : WritesWithin (Sum.effect t).components
      #v[registerRegion s .rdi 32,workRegion s] := by
    intro c hc addr ha
    simp only [Sum.effect,Effect.components,List.map_cons,List.map_nil,List.cons_append,
      List.nil_append,List.mem_cons,List.not_mem_nil,or_false,Write.component_reg,
      Write.component_mem] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨workRegion s,by simp,?_⟩
    change (Component.mem (stackPtr t+BitVec.ofNat 64 15) 1).Covers addr at ha
    rw [scalar_stack_address state.rsp (offset := 15) (by decide)] at ha
    exact work_contains pre.toCalleePre (by decide) (by decide) ha
  have final := state.after_effect pre.toCalleePre ready effect.agrees writes
    (by simp [Sum.effect,Effect.components])
  have limbs : sumLimbs u = Sum.value (P256.Proofs.Field.readLimbs t (t.regValue .rsi))
      (P256.Proofs.Field.readLimbs t (t.regValue .rdx)) := by
    unfold sumLimbs Sum.value
    congr 1
    · exact effect.writes.2.2.2.2.2.1
    · exact effect.writes.2.2.2.2.1
    · exact effect.writes.2.2.2.1
    · exact effect.writes.2.2.1
  have carry : u.regValue .r12 = Sum.extendedCarry
      (P256.Proofs.Field.readLimbs t (t.regValue .rsi)) (P256.Proofs.Field.readLimbs t (t.regValue .rdx)) :=
    effect.writes.2.2.2.2.2.2.1
  refine ⟨fuel,u,run,{ toFrameState := final
                       rip := effect.rip
                       output := ?_
                       modulus := ?_
                       sum := ?_ }⟩
  · exact (effect.agrees.read (n := 64) (r := 7) (by simp [Sum.effect,Effect.components])).trans output
  · exact (effect.agrees.read (n := 64) (r := 1) (by simp [Sum.effect,Effect.components])).trans modulus
  · rw [limbs,carry,Sum.value_toNat,P256.Proofs.Field.readLimbs_toNat left,P256.Proofs.Field.readLimbs_toNat right]

end P256.Proofs.Signing.Core.Iteration.Components.Addition
