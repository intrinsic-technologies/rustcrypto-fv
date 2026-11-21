import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Common
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.Output
import P256.Proofs.Common.Instructions.CrossPageStore.Range
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar.Limbs (mk)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StoreLimbsPre (entry : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = (entry + 0x59c#64)
  writable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 7 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 1469 → RangeApart ((Operand.reg 7 : Operand 64).read s + i) 8
      (entry + BitVec.ofNat 64 offset) len

def storeLimbsBytes : List UInt8 :=
  [0x4c, 0x89, 0x17, 0x48, 0x89, 0x4f, 0x8, 0x48, 0x89, 0x77, 0x10, 0x48, 0x89, 0x47, 0x18]

def storeLimbsEffect (entry : BitVec 64) (s : RamState) : Effect :=
  { rip := (entry + 0x5ab#64)
    writes := [
      ⟨(.mem ((Operand.reg 7 : Operand 64).read s + 0) : Operand 64), (Operand.reg 10 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 7 : Operand 64).read s + 8) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 7 : Operand 64).read s + 16) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 7 : Operand 64).read s + 24) : Operand 64), (Operand.reg 0 : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem store_limbs_correct [Bindings] (entry : BitVec 64) (hentry : Entry entry)
    (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (StoreLimbsPre entry) (codeRange (entry + 0x59c#64) storeLimbsBytes)
      (Effect.post (storeLimbsEffect entry)) := by
  intro s ready code pre
  let dst := (Operand.reg 7 : Operand 64).read s
  have pre1 : P256.Proofs.Common.Instructions.CrossPageStore.Pre (entry + 0x59c#64) 3
      (fun t => (AddrMode.base 7 .none).addr t (entry + 0x59f#64)) 8 s := by
    refine ⟨pre.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 7 : Operand 64).read s + 0) 8
      exact pre.writable 0 (by simp)
    · change RangeApart ((Operand.reg 7 : Operand 64).read s + 0) 8 (entry + 0x59c#64) 3
      exact pre.codeApart 0 (by simp) 0x59c 3 (by decide)
  obtain ⟨s1, e1, ready1, h1⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (entry + 0x59c#64) 0x4c
      (by unfold RexWPrefix; decide +kernel) 2 (.base 7 .none) (by decide +kernel) rfl rfl).advances ready
      (by change CodeIn (codeRange (entry + 0x59c#64) [0x4c, 0x89, 0x17]) _
          simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, storeLimbsBytes, List.drop, List.take] using code.mono (codeRange_slice_subset (entry + 0x59c#64) storeLimbsBytes 0 3)) pre1
      (by change (entry + 0x59c#64) + 3#64 ≠ boundary.rip
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using instruction_ne_boundary hentry hout 0x59f (by decide))
  change ({rip := ((entry + 0x59c#64) + 3), writes :=
    [⟨(Operand.mem ((Operand.reg 7 : Operand 64).read s + 0) : Operand 64),
      (Operand.reg 10 : Operand 64).read s⟩]} : Effect).Holds s s1 at h1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  have f1 : AgreesExcept [.mem (dst + 0) 8, .rip] s s1 := by simpa [Effect.components, dst] using h1.agrees
  have fAll1 := f1
  have g1 (r : BitVec 5) : (Operand.reg r : Operand 64).read s1 =
      (Operand.reg r : Operand 64).read s := fAll1.read (by simp)
  have av1 : ({rip := (entry + 0x59f#64), writes :=
      [⟨(Operand.mem (dst + 0) : Operand 64), (Operand.reg 10 : Operand 64).read s⟩]} : Effect).Avoids
      (codeRange (entry + 0x59c#64) storeLimbsBytes) := by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, Nat.reduceDiv,
      List.append_nil, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact pre.codeApart 0 (by simp) 0x59c 15 (by decide)
    · cases he
  have code1 := h1.codeIn av1 code
  have pre2 : P256.Proofs.Common.Instructions.CrossPageStore.Pre (entry + 0x59f#64) 4
      (fun t => (AddrMode.base 7 (.d8 8)).addr t (entry + 0x5a3#64)) 8 s1 := by
    refine ⟨h1.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s1 ((Operand.reg 7 : Operand 64).read s1 + 8) 8
      rw [g1]
      exact (pre.writable 8 (by simp)).of_holds h1
    · change RangeApart ((Operand.reg 7 : Operand 64).read s1 + 8) 8 (entry + 0x59f#64) 4
      rw [g1]
      exact pre.codeApart 8 (by simp) 0x59f 4 (by decide)
  obtain ⟨s2, e2, ready2, h2⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (entry + 0x59f#64) 0x48
      (by unfold RexWPrefix; decide +kernel) 1 (.base 7 (.d8 8)) (by decide +kernel) rfl rfl).advances ready1
      (by change CodeIn (codeRange (entry + 0x59f#64) [0x48, 0x89, 0x4f, 8]) _
          simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, storeLimbsBytes, List.drop, List.take] using code1.mono (codeRange_slice_subset (entry + 0x59c#64) storeLimbsBytes 3 4)) pre2
      (by change (entry + 0x59f#64) + 4#64 ≠ boundary.rip
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using instruction_ne_boundary hentry hout 0x5a3 (by decide))
  change ({rip := ((entry + 0x59f#64) + 4), writes :=
    [⟨(Operand.mem ((Operand.reg 7 : Operand 64).read s1 + 8) : Operand 64),
      (Operand.reg 1 : Operand 64).read s1⟩]} : Effect).Holds s1 s2 at h2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2
  rw [g1 7, g1 1] at h2
  have f2 : AgreesExcept [.mem (dst + 8) 8, .rip] s1 s2 := by simpa [Effect.components, dst] using h2.agrees
  have fAll2 := fAll1.trans f2
  have g2 (r : BitVec 5) : (Operand.reg r : Operand 64).read s2 =
      (Operand.reg r : Operand 64).read s := fAll2.read (by simp)
  have av2 : ({rip := (entry + 0x5a3#64), writes :=
      [⟨(Operand.mem (dst + 8) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩]} : Effect).Avoids
      (codeRange (entry + 0x59c#64) storeLimbsBytes) := by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, Nat.reduceDiv,
      List.append_nil, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact pre.codeApart 8 (by simp) 0x59c 15 (by decide)
    · cases he
  have code2 := h2.codeIn av2 code1
  have pre3 : P256.Proofs.Common.Instructions.CrossPageStore.Pre (entry + 0x5a3#64) 4
      (fun t => (AddrMode.base 7 (.d8 16)).addr t (entry + 0x5a7#64)) 8 s2 := by
    refine ⟨h2.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s2 ((Operand.reg 7 : Operand 64).read s2 + 16) 8
      rw [g2]
      exact ⟨P256.Proofs.Program.readable_of_grow (pre.writable 16 (by simp)).toMemReadable fAll2.grow, (pre.writable 16 (by simp)).tables⟩
    · change RangeApart ((Operand.reg 7 : Operand 64).read s2 + 16) 8 (entry + 0x5a3#64) 4
      rw [g2]
      exact pre.codeApart 16 (by simp) 0x5a3 4 (by decide)
  obtain ⟨s3, e3, ready3, h3⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (entry + 0x5a3#64) 0x48
      (by unfold RexWPrefix; decide +kernel) 6 (.base 7 (.d8 16)) (by decide +kernel) rfl rfl).advances ready2
      (by change CodeIn (codeRange (entry + 0x5a3#64) [0x48, 0x89, 0x77, 16]) _
          simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, storeLimbsBytes, List.drop, List.take] using code2.mono (codeRange_slice_subset (entry + 0x59c#64) storeLimbsBytes 7 4)) pre3
      (by change (entry + 0x5a3#64) + 4#64 ≠ boundary.rip
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using instruction_ne_boundary hentry hout 0x5a7 (by decide))
  change ({rip := ((entry + 0x5a3#64) + 4), writes :=
    [⟨(Operand.mem ((Operand.reg 7 : Operand 64).read s2 + 16) : Operand 64),
      (Operand.reg 6 : Operand 64).read s2⟩]} : Effect).Holds s2 s3 at h3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h3
  rw [g2 7, g2 6] at h3
  have f3 : AgreesExcept [.mem (dst + 16) 8, .rip] s2 s3 := by simpa [Effect.components, dst] using h3.agrees
  have fAll3 := fAll2.trans f3
  have g3 (r : BitVec 5) : (Operand.reg r : Operand 64).read s3 =
      (Operand.reg r : Operand 64).read s := fAll3.read (by simp)
  have av3 : ({rip := (entry + 0x5a7#64), writes :=
      [⟨(Operand.mem (dst + 16) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩]} : Effect).Avoids
      (codeRange (entry + 0x59c#64) storeLimbsBytes) := by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, Nat.reduceDiv,
      List.append_nil, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact pre.codeApart 16 (by simp) 0x59c 15 (by decide)
    · cases he
  have code3 := h3.codeIn av3 code2
  have pre4 : P256.Proofs.Common.Instructions.CrossPageStore.Pre (entry + 0x5a7#64) 4
      (fun t => (AddrMode.base 7 (.d8 24)).addr t (entry + 0x5ab#64)) 8 s3 := by
    refine ⟨h3.rip, ?_, ?_⟩
    · change P256.Proofs.Common.Instructions.CrossPageStore.Writable s3 ((Operand.reg 7 : Operand 64).read s3 + 24) 8
      rw [g3]
      exact ⟨P256.Proofs.Program.readable_of_grow (pre.writable 24 (by simp)).toMemReadable fAll3.grow, (pre.writable 24 (by simp)).tables⟩
    · change RangeApart ((Operand.reg 7 : Operand 64).read s3 + 24) 8 (entry + 0x5a7#64) 4
      rw [g3]
      exact pre.codeApart 24 (by simp) 0x5a7 4 (by decide)
  obtain ⟨s4, e4, ready4, h4⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (entry + 0x5a7#64) 0x48
      (by unfold RexWPrefix; decide +kernel) 0 (.base 7 (.d8 24)) (by decide +kernel) rfl rfl).advances ready3
      (by change CodeIn (codeRange (entry + 0x5a7#64) [0x48, 0x89, 0x47, 24]) _
          simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, storeLimbsBytes, List.drop, List.take] using code3.mono (codeRange_slice_subset (entry + 0x59c#64) storeLimbsBytes 11 4)) pre4
      (by change (entry + 0x5a7#64) + 4#64 ≠ boundary.rip
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using instruction_ne_boundary hentry hout 0x5ab (by decide))
  change ({rip := ((entry + 0x5a7#64) + 4), writes :=
    [⟨(Operand.mem ((Operand.reg 7 : Operand 64).read s3 + 24) : Operand 64),
      (Operand.reg 0 : Operand 64).read s3⟩]} : Effect).Holds s3 s4 at h4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4
  rw [g3 7, g3 0] at h4
  have f4 : AgreesExcept [.mem (dst + 24) 8, .rip] s3 s4 := by simpa [Effect.components, dst] using h4.agrees
  have fAll4 := fAll3.trans f4
  have g4 (r : BitVec 5) : (Operand.reg r : Operand 64).read s4 =
      (Operand.reg r : Operand 64).read s := fAll4.read (by simp)
  have av4 : ({rip := (entry + 0x5ab#64), writes :=
      [⟨(Operand.mem (dst + 24) : Operand 64), (Operand.reg 0 : Operand 64).read s⟩]} : Effect).Avoids
      (codeRange (entry + 0x59c#64) storeLimbsBytes) := by
    apply Effect.avoids_codeRange
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, Nat.reduceDiv,
      List.append_nil, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact pre.codeApart 24 (by simp) 0x59c 15 (by decide)
    · cases he
  have code4 := h4.codeIn av4 code3
  have m21 : (Operand.mem (dst + 0) : Operand 64).read s2 =
      (Operand.mem (dst + 0) : Operand 64).read s1 :=
    P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.store_memLoad_apart f2 (by
      intro i hi j hj
      exact (show OffsetsApart 8 8 0 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  have m31 : (Operand.mem (dst + 0) : Operand 64).read s3 =
      (Operand.mem (dst + 0) : Operand 64).read s2 :=
    P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.store_memLoad_apart f3 (by
      intro i hi j hj
      exact (show OffsetsApart 16 8 0 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  have m41 : (Operand.mem (dst + 0) : Operand 64).read s4 =
      (Operand.mem (dst + 0) : Operand 64).read s3 :=
    P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.store_memLoad_apart f4 (by
      intro i hi j hj
      exact (show OffsetsApart 24 8 0 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  have m32 : (Operand.mem (dst + 8) : Operand 64).read s3 =
      (Operand.mem (dst + 8) : Operand 64).read s2 :=
    P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.store_memLoad_apart f3 (by
      intro i hi j hj
      exact (show OffsetsApart 16 8 8 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  have m42 : (Operand.mem (dst + 8) : Operand 64).read s4 =
      (Operand.mem (dst + 8) : Operand 64).read s3 :=
    P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.store_memLoad_apart f4 (by
      intro i hi j hj
      exact (show OffsetsApart 24 8 8 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  have m43 : (Operand.mem (dst + 16) : Operand 64).read s4 =
      (Operand.mem (dst + 16) : Operand 64).read s3 :=
    P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.store_memLoad_apart f4 (by
      intro i hi j hj
      exact (show OffsetsApart 24 8 16 8 from by unfold OffsetsApart; decide +kernel).ne dst hi hj (by decide))
  refine ⟨4, s4, ((e1.trans e2).trans e3).trans e4, ready4, code4, ?_⟩
  refine ⟨h4.rip, ?_, ?_, ?_⟩
  · change _ ∧ _ ∧ _ ∧ _
    exact ⟨((m41.trans m31).trans m21).trans h1.writes,
      (m42.trans m32).trans h2.writes, m43.trans h3.writes, h4.writes⟩
  · trivial
  · exact fAll4.mono (by simp [storeLimbsEffect, Effect.components, dst])

structure StoreInput (s : RamState) (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) : Prop where
  l0 : (Operand.reg 10 : Operand 64).read s = a.l0
  l1 : (Operand.reg 1 : Operand 64).read s = a.l1
  l2 : (Operand.reg 6 : Operand 64).read s = a.l2
  l3 : (Operand.reg 0 : Operand 64).read s = a.l3

theorem stores_frame {entry : BitVec 64} {s t : RamState}
    (h : (storeLimbsEffect entry s).Holds s t) :
    AgreesExcept [.mem (s.regValue .rdi) 32, .rip] s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [storeLimbsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, List.append_nil, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp_all [Component.isMem]
  · intro address c hc hv
    simp only [storeLimbsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, List.append_nil, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    refine ⟨.mem (s.regValue .rdi) 32, by simp, ?_⟩
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    · exact output_covered (offset := 0) (by decide) hv
    · exact output_covered (offset := 8) (by decide) hv
    · exact output_covered (offset := 16) (by decide) hv
    · exact output_covered (offset := 24) (by decide) hv

theorem stores_correct [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {s : RamState} {a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs} (he : Entry entry)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (hout : ¬ InProgram boundary.rip)
    (memory : MemoryPre s) (rip : s.RIP = entry + 0x59c#64) (input : StoreInput s a) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = entry + 0x5ab#64 ∧
      Nat256At t (s.regValue .rdi) a.toNat ∧
      AgreesExcept [.mem (s.regValue .rdi) 32, .rip] s t := by
  have pre : StoreLimbsPre entry s := by
    refine ⟨rip, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact memory.output.add _ (by decide)
    · intro i hi offset len hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact memory.output_apart he _ 8 offset len (by decide) hc
  obtain ⟨fuel, t, run, ready', _, effect⟩ := store_limbs_correct entry he boundary hout
    s ready (code_slice he loaded 0x59c storeLimbsBytes (by decide) (by decide +kernel)) pre
  have frame := stores_frame effect
  have wide : AgreesExcept (components s) s t := frame.mono (by simp [components, scratchComponents])
  refine ⟨fuel, t, run, ready', memory.loaded wide loaded, effect.rip, ?_, frame⟩
  have readEq : P256.Proofs.Field.readLimbs t (s.regValue .rdi) = a := by
    have ws := effect.writes
    have hd : (Operand.reg 7 : Operand 64).read s = s.regValue .rdi := rfl
    simp only [storeLimbsEffect, Write.AllHold, hd, input.l0, input.l1, input.l2, input.l3] at ws
    cases a with
    | mk l0 l1 l2 l3 =>
      change P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.mk _ _ _ _ = P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.mk _ _ _ _
      congr 1
      · change (Operand.mem (s.regValue .rdi) : Operand 64).read t = l0
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ws.1
      · exact ws.2.1
      · exact ws.2.2.1
      · exact ws.2.2.2
  have result := P256.Proofs.Field.nat256At_readLimbs (fun i hi =>
    frame.grow _ (memory.output.mem i hi))
  rwa [readEq] at result

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
