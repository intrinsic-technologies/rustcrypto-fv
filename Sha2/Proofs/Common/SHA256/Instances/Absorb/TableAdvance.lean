import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableRun
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableShape

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb

theorem advance_compare {s u v : RamState} {p : BitVec 64} {i c : BitVec 4}
    (different : c ≠ i)
    (inc : (incR64Effect p (i.setWidth 5) s).Holds s u)
    (cmp : (cmpR64R64Effect (p + 3) (c.setWidth 5) (i.setWidth 5) u).Holds u v) :
    v.RIP = (p + 6 : BitVec 64) ∧
    Blocks.readReg v i = Blocks.readReg s i + 1 ∧
    (StatusFlags.ofRFLAGS v.RFLAGS).ZF = (Blocks.readReg s c == (Blocks.readReg s i + 1)) ∧
    AgreesExcept [.reg (i.setWidth 5), .flags, .rip] s v := by
  have index : Blocks.readReg u i = Blocks.readReg s i + 1 := by
    simpa [incR64Effect, Write.AllHold, Blocks.readReg] using inc.writes
  have count : Blocks.readReg u c = Blocks.readReg s c := by
    apply inc.agrees.read
    simp only [incR64Effect_components, List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq, reduceCtorEq, or_false]
    intro h
    exact different (by have := congrArg (BitVec.setWidth 4) h; simpa using this)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [cmpR64R64Effect, BitVec.add_assoc] using cmp.rip
  · exact (cmp.agrees.read (by simp [cmpR64R64Effect, Effect.components])).trans index
  · have h := cmp.flag .ZF
    change (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      (Blocks.readReg u c - Blocks.readReg u i == 0) at h
    rw [index, count] at h
    rw [h]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    rw [show (0 : BitVec 64) + (Blocks.readReg s i + 1) = Blocks.readReg s i + 1 from BitVec.zero_add _]
  · exact (inc.agrees.trans cmp.agrees).mono (by simp [incR64Effect, cmpR64R64Effect, Effect.components])

theorem advance_small_trace {s t : RamState} {p finish head : BitVec 64}
    {i c : BitVec 4} {disp : Blocks.Displacement}
    (different : c ≠ i) (rip : s.RIP = p)
    (len : (Blocks.bytes (.branch 4 disp)).length = 6)
    (target : branchTarget (p + 6) 6 disp.value = finish)
    (fall : p + 6 + 6 = head)
    (trace : Blocks.SiteTrace [⟨p, .incrementIndex i⟩, ⟨p + 3, .compareIndex i c⟩,
      ⟨p + 6, .branch 4 disp⟩] s t) :
    t.RIP = (if Blocks.readReg s i + 1 = Blocks.readReg s c then finish else head) ∧
    Blocks.readReg t i = Blocks.readReg s i + 1 ∧
    AgreesExcept [.reg (i.setWidth 5), .flags, .rip] s t := by
  simp only [Blocks.SiteTrace, rip, ite_true] at trace
  obtain ⟨u, inc, trace⟩ := trace
  have urip : u.RIP = (p + 3 : BitVec 64) := inc.rip
  simp only [urip, ite_true] at trace
  obtain ⟨v, cmp, trace⟩ := trace
  have facts := advance_compare different inc cmp
  simp only [facts.1, ite_true] at trace
  obtain ⟨w, branch, rfl⟩ := trace
  have agr : AgreesExcept [.reg (i.setWidth 5), .flags, .rip] s t :=
    (facts.2.2.2.trans branch.agrees).mono (by
      simp [Blocks.effect, jccEffect, branchEffect, Effect.components])
  refine ⟨?_, ?_, agr⟩
  · have h := branch.rip
    change t.RIP = (jccEffect (p + 6) (Blocks.bytes (.branch 4 disp)).length 4 disp.value v).rip at h
    rw [len] at h
    change t.RIP = (if (StatusFlags.ofRFLAGS v.RFLAGS).ZF then
      branchTarget (p + 6) 6 disp.value else p + 6 + 6) at h
    rw [facts.2.2.1, target, fall] at h
    simp only [beq_iff_eq] at h
    simpa only [eq_comm] using h
  · exact (branch.agrees.read (by simp [Blocks.effect, jccEffect, branchEffect, Effect.components])).trans facts.2.1


theorem advance_large_trace {s t : RamState} {p finish head : BitVec 64}
    {i c : BitVec 4} {disp : Blocks.Displacement} {jump : BitVec 8}
    (different : c ≠ i) (rip : s.RIP = p)
    (len : (Blocks.bytes (.branch 5 disp)).length = 6)
    (target : branchTarget (p + 6) 6 disp.value = head)
    (skip : head ≠ p + 12)
    (exit : branchTarget (p + 12) 2 (Blocks.Displacement.short jump).value = finish)
    (trace : Blocks.SiteTrace [⟨p, .incrementIndex i⟩, ⟨p + 3, .compareIndex i c⟩,
      ⟨p + 6, .branch 5 disp⟩, ⟨p + 12, .jump (.short jump)⟩] s t) :
    t.RIP = (if Blocks.readReg s i + 1 = Blocks.readReg s c then finish else head) ∧
    Blocks.readReg t i = Blocks.readReg s i + 1 ∧
    AgreesExcept [.reg (i.setWidth 5), .flags, .rip] s t := by
  simp only [Blocks.SiteTrace, rip, ite_true] at trace
  obtain ⟨u, inc, trace⟩ := trace
  have urip : u.RIP = (p + 3 : BitVec 64) := inc.rip
  simp only [urip, ite_true] at trace
  obtain ⟨v, cmp, trace⟩ := trace
  have facts := advance_compare different inc cmp
  simp only [facts.1, ite_true] at trace
  obtain ⟨w, branch, trace⟩ := trace
  have agr : AgreesExcept [.reg (i.setWidth 5), .flags, .rip] s w :=
    (facts.2.2.2.trans branch.agrees).mono (by
      simp [Blocks.effect, jccEffect, branchEffect, Effect.components])
  have idx : Blocks.readReg w i = Blocks.readReg s i + 1 :=
    (branch.agrees.read (by simp [Blocks.effect, jccEffect, branchEffect, Effect.components])).trans facts.2.1
  have wrip := branch.rip
  change w.RIP = (jccEffect (p + 6) (Blocks.bytes (.branch 5 disp)).length 5 disp.value v).rip at wrip
  rw [len] at wrip
  change w.RIP = (if !(StatusFlags.ofRFLAGS v.RFLAGS).ZF then
    branchTarget (p + 6) 6 disp.value else p + 6 + 6) at wrip
  rw [facts.2.2.1, target] at wrip
  have plus : p + 6 + 6 = p + 12 := by rw [BitVec.add_assoc]; rfl
  rw [plus] at wrip
  by_cases equal : Blocks.readReg s i + 1 = Blocks.readReg s c
  · have atJump : w.RIP = (p + 12 : BitVec 64) := by
      have hb : (Blocks.readReg s c == (Blocks.readReg s i + 1)) = true := beq_iff_eq.mpr equal.symm
      rw [hb] at wrip
      exact wrip
    simp only [atJump, ite_true] at trace
    obtain ⟨z, jmp, rfl⟩ := trace
    refine ⟨?_, ?_, ?_⟩
    · simpa only [equal, ite_true] using jmp.rip.trans exit
    · exact (jmp.agrees.read (by simp [Blocks.effect, jmpEffect, Effect.components])).trans idx
    · exact (agr.trans jmp.agrees).mono (by simp [Blocks.effect, jmpEffect, Effect.components])
  · have atHead : w.RIP = head := by
      have ne : Blocks.readReg s c ≠ Blocks.readReg s i + 1 := Ne.symm equal
      have hb : (Blocks.readReg s c == (Blocks.readReg s i + 1)) = false := by simp only [beq_eq_false_iff_ne]; exact ne
      rw [hb] at wrip
      exact wrip
    have notJump : w.RIP ≠ (p + 12 : BitVec 64) := by rw [atHead]; exact skip
    simp only [notJump, ite_false] at trace
    subst t
    exact ⟨by simpa only [equal, ite_false] using atHead, idx, agr⟩


theorem advance_post {l : Table.Layout} {sp : BitVec 64} {s t : RamState}
    {large : Bool} {c : BitVec 4}
    (count : l.count = .reg c) (different : c ≠ l.index) (notSp : l.index ≠ 4)
    (noIn : l.cloneIn = []) (restore : l.chunk.bufferRestore = none)
    (same : l.storedOffset = l.chunk.bufferOffset)
    (pre : Table.NextPre l sp large s)
    (rip : t.RIP = if Blocks.readReg s l.index + 1 = Blocks.readReg s c then l.exit else l.head)
    (index : Blocks.readReg t l.index = Blocks.readReg s l.index + 1)
    (agrees : AgreesExcept [.reg (l.index.setWidth 5), .flags, .rip] s t) :
    Table.NextPost l sp s t := by
  have regs : ∀ r : BitVec 5, r ≠ l.index.setWidth 5 →
      (.reg r : Operand 64).read t = (.reg r : Operand 64).read s := by
    intro r ne
    exact agrees.read (by simp [ne])
  refine ⟨?_, ?_, index, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [count, Table.Count.read] using rip
  · have h := regs 4 (by
      intro h
      have hh := congrArg (BitVec.setWidth 4) h
      exact notSp (by simpa using hh.symm))
    exact h.trans pre.rsp
  · simp only [count, Table.Count.read]
    apply regs
    intro h
    exact different (by have hh := congrArg (BitVec.setWidth 4) h; simpa using hh)
  · intro i _
    have memory := agrees.external (by simp [Component.Covers])
    rw [memory]
    congr 2
    simp [Table.Layout.stored, Layout.buffer, same]
  · simp [restore]
  · simp [noIn]
  · exact agrees.mono (by simp)
  · exact agrees.memoryWriteFrame (by simp [WritesWithin, Component.Covers])
  · intro r _ ne
    exact regs r ne

theorem noClone_advance [bindings : Bindings] {l : Table.Layout}
    (shape : NoCloneShape l) (boundary : ReturnBoundary)
    (stride : UnitStringStride bindings) (outside : ¬ InProgram boundary.rip)
    (sp : BitVec 64) (large : Bool) :
    AdvanceTriple boundary (Table.NextPre l sp large)
      (((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut).flatMap Blocks.Site.code)
      (Table.NextPost l sp) := by
  rcases shape with ⟨noIn, noOut, data⟩
  unfold noCloneData at data
  split at data
  · rename_i c pc0 i source length pointers lengths pc1 tail address countEq loadEq
    rcases of_decide_eq_true data with ⟨indexEq, _, _, _, _, _, same, _, _, restore,
      _, apart, _, _, _, _, _, _, _, _, _, _, small, big⟩
    subst i
    have first := (List.pairwise_cons.mp apart).1
    have different : c ≠ l.index := Ne.symm (first c (by simp))
    have notSp : l.index ≠ 4 := first 4 (by simp)
    cases large
    · simp only [Bool.false_eq_true, ite_false, noOut, List.append_nil]
      unfold noCloneNextSmall at small
      split at small
      · rename_i p0 i p1 j k p2 cc disp sites
        rcases of_decide_eq_true small with
          ⟨hp0, hi, hp1, hj, hk, hp2, hcc, target, len, fall, in0, in1, in2, inTarget⟩
        subst p0 i p1 j k p2 cc
        rw [sites]
        apply next_sites_run boundary sp false
          [⟨l.chunk.smallExit, .incrementIndex l.index⟩,
           ⟨l.chunk.smallExit + 3, .compareIndex l.index c⟩,
           ⟨l.chunk.smallExit + 6, .branch 4 disp⟩] _ stride outside
        · intro site member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact codeLocation_inProgram in0
          · exact codeLocation_inProgram in1
          · exact codeLocation_inProgram in2
        · intro site member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · trivial
          · trivial
          · simpa only [BitVec.add_zero] using codeLocation_inProgram inTarget 0 (by omega)
        · intro site member x hx
          exact List.mem_flatMap.mpr ⟨site, member, hx⟩
        · intro s _
          apply Blocks.SitePre.of_basic
          intro site member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> trivial
        · intro s t pre trace
          have result := advance_small_trace different pre.rip len target fall trace
          exact advance_post countEq different notSp noIn restore same pre
            result.1 result.2.1 result.2.2
      · contradiction
    · simp only [ite_true, noOut, List.append_nil]
      unfold noCloneNextLarge at big
      split at big
      · rename_i p0 i p1 j k p2 cc disp p3 jump sites
        rcases of_decide_eq_true big with
          ⟨hp0, hi, hp1, hj, hk, hp2, hcc, target, len, hp3, _, skip, exit, in0, in1, in2, in3, inTarget, inJump⟩
        subst p0 i p1 j k p2 cc p3
        rw [sites]
        apply next_sites_run boundary sp true
          [⟨l.chunk.largeExit, .incrementIndex l.index⟩,
           ⟨l.chunk.largeExit + 3, .compareIndex l.index c⟩,
           ⟨l.chunk.largeExit + 6, .branch 5 disp⟩,
           ⟨l.chunk.largeExit + 12, .jump (.short jump)⟩] _ stride outside
        · intro site member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · exact codeLocation_inProgram in0
          · exact codeLocation_inProgram in1
          · exact codeLocation_inProgram in2
          · exact codeLocation_inProgram in3
        · intro site member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · trivial
          · trivial
          · simpa only [BitVec.add_zero] using codeLocation_inProgram inTarget 0 (by omega)
          · simpa only [BitVec.add_zero] using codeLocation_inProgram inJump 0 (by omega)
        · intro site member x hx
          exact List.mem_flatMap.mpr ⟨site, member, hx⟩
        · intro s _
          apply Blocks.SitePre.of_basic
          intro site member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> trivial
        · intro s t pre trace
          have result := advance_large_trace different pre.rip len target skip exit trace
          exact advance_post countEq different notSp noIn restore same pre
            result.1 result.2.1 result.2.2
      · contradiction
  · contradiction

end Sha2.Proofs.Common.SHA256.Instances.Absorption
