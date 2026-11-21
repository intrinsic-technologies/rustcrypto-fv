import Sha2.Proofs.Common.SHA256.Instances.Absorb.TraitTable.Shape
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableRun
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Normalize

set_option autoImplicit false


namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption.TraitTable
open Sha2.Spec.Program Sha2.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

private theorem next_sites_subset (l : Table.Layout) (large : Bool)
    {site : Blocks.Site}
    (member : site ∈ (if large then l.nextLarge else l.nextSmall) ++ l.cloneOut) :
    site ∈ l.load ++ l.cloneIn ++ l.cloneOut ++ l.nextSmall ++ l.nextLarge := by
  cases large <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    List.mem_append] at member ⊢
  · rcases member with small | copied
    · exact Or.inl (Or.inr small)
    · exact Or.inl (Or.inl (Or.inr copied))
  · rcases member with large | copied
    · exact Or.inr large
    · exact Or.inl (Or.inl (Or.inr copied))

theorem cloneShape_next_sites_inside {l : Table.Layout} (shape : CloneShape l)
    (large : Bool) :
    ∀ site ∈ (if large then l.nextLarge else l.nextSmall) ++ l.cloneOut,
      BlockInProgram site.pc (Blocks.bytes site.block).length := by
  intro site member
  exact cloneSitesCode_inProgram (cloneShape_sites_code shape) site
    (next_sites_subset l large member)

theorem cloneShape_next_code (l : Table.Layout) (large : Bool)
    {site : Blocks.Site}
    (member : site ∈ (if large then l.nextLarge else l.nextSmall) ++ l.cloneOut) :
    ∀ x ∈ site.code,
      x ∈ (((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut).flatMap
        Blocks.Site.code) := by
  intro x hx
  exact List.mem_flatMap.mpr ⟨site, member, hx⟩

theorem cloneShape_next_sites {l : Table.Layout} (shape : CloneShape l) (large : Bool) :
    nextPrefixOf l large ++ [nextCloneOf l, nextCompareOf l, nextBranchOf l] =
      (if large then l.nextLarge else l.nextSmall) ++ l.cloneOut := by
  have data := shape.2.2.1
  unfold cloneData at data
  split at data
  · rename_i he hc hl hi ho
    simp only [nextPrefixOf, nextCloneOf, nextCompareOf, nextBranchOf, ho]
    simp
  · contradiction

set_option maxRecDepth 10000 in
theorem cloneShape_next_targets {l : Table.Layout} (shape : CloneShape l)
    (large : Bool) :
    ∀ site ∈ (if large then l.nextLarge else l.nextSmall) ++ l.cloneOut,
      match site.block with
      | .branch _ disp | .jump disp =>
        InProgram (branchTarget site.pc (Blocks.bytes site.block).length disp.value)
      | _ => True := by
  have data := shape.2.2.1
  unfold cloneData at data
  split at data
  · rename_i _ _ _ _ countSlot loadPC index source length pointers lengths tailPC tail
      tailAddress ci0 c0 v0 ci1 bsrc0 restore0 ci2 dst0 restore1 ci3 dst1 src1 ci4 co0
      index0 co1 c1 v1 co2 addrReg addrMode co3 dst2 src2 co4 dst3 restore2 co5 co6
      index1 countOffset co7 cc disp hc hl hi ho
    simp only [decide_eq_true_eq] at data
    have small : cloneNextSmall l bsrc0 restore0 = true := by grind only
    have big : cloneNextLarge l = true := by grind only
    have branch : cloneCodeLocation
        (branchTarget co7 (Blocks.bytes (.branch cc disp)).length disp.value) 0 = true := by
      grind only
    have branchIn : InProgram
        (branchTarget co7 (Blocks.bytes (.branch cc disp)).length disp.value) := by
      simpa only [BitVec.add_zero] using
        cloneCodeLocation_inProgram branch 0 (by omega)
    intro site member
    simp only [List.mem_append] at member
    rcases member with chosen | copied
    · cases large
      · simp only [Bool.false_eq_true, ite_false] at chosen
        unfold cloneNextSmall at small
        split at small
        · rename_i pc dst src hs
          simp only [hs, List.mem_singleton] at chosen
          subst site
          trivial
        · contradiction
      · simp only [ite_true] at chosen
        unfold cloneNextLarge at big
        split at big
        · rename_i pc offset hb
          simp only [hb, List.mem_singleton] at chosen
          subst site
          have loc := (of_decide_eq_true big).2.2.2
          simpa only [BitVec.add_zero] using
            cloneCodeLocation_inProgram loc 0 (by omega)
        · contradiction
    · simp only [ho, List.mem_cons, List.mem_nil_iff, or_false] at copied
      rcases copied with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | trivial | exact branchIn

  · contradiction

set_option maxRecDepth 10000 in
theorem cloneShape_next_prefix_basic {l : Table.Layout} (shape : CloneShape l)
    (large : Bool) : ∀ site ∈ nextPrefixOf l large, Blocks.Basic site.block := by
  have data := shape.2.2.1
  unfold cloneData at data
  split at data
  · rename_i _ _ _ _ countSlot loadPC index source length pointers lengths tailPC tail
      tailAddress ci0 c0 v0 ci1 bsrc0 restore0 ci2 dst0 restore1 ci3 dst1 src1 ci4 co0
      index0 co1 c1 v1 co2 addrReg addrMode co3 dst2 src2 co4 dst3 restore2 co5 co6
      index1 countOffset co7 cc disp hc hl hi ho
    simp only [decide_eq_true_eq] at data
    have small : cloneNextSmall l bsrc0 restore0 = true := by grind only
    have big : cloneNextLarge l = true := by grind only
    have address : addrMode = .sib 4 none 0 (.d8 0x70) := by grind only
    intro site member
    simp only [nextPrefixOf, ho, List.take, List.mem_append] at member
    rcases member with chosen | member
    · cases large
      · simp only [Bool.false_eq_true, ite_false] at chosen
        unfold cloneNextSmall at small
        split at small
        · rename_i pc dst src hs
          simp only [hs, List.mem_singleton] at chosen
          subst site
          trivial
        · contradiction
      · simp only [ite_true] at chosen
        unfold cloneNextLarge at big
        split at big
        · rename_i pc offset hb
          simp only [hb, List.mem_singleton] at chosen
          subst site
          trivial
        · contradiction
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      all_goals first | trivial | simp [Blocks.Basic, address, AddrMode.Valid]
  · contradiction

end Sha2.Proofs.Common.SHA256.Instances.Absorption

namespace Sha2.Proofs.Common.SHA256.Absorb.Blocks

open X86 X86.Machine X86.UserProcess X86Proofs

theorem SiteTrace.append_iff (first second : List Site) (s t : RamState) :
    SiteTrace (first ++ second) s t ↔
      ∃ u, SiteTrace first s u ∧ SiteTrace second u t := by
  induction first generalizing s with
  | nil => simp [SiteTrace]
  | cons site rest ih =>
    simp only [List.cons_append, SiteTrace]
    by_cases atSite : s.RIP = site.pc
    · simp only [atSite, ite_true, ih]
      constructor
      · rintro ⟨v, step, u, front, suffix⟩
        exact ⟨u, ⟨v, step, front⟩, suffix⟩
      · rintro ⟨u, ⟨v, step, front⟩, suffix⟩
        exact ⟨v, step, u, front, suffix⟩
    · simp only [atSite, ite_false, ih]

theorem SitePre.append_iff (code : CodeMap) (first second : List Site) (s : RamState) :
    SitePre code (first ++ second) s ↔
      SitePre code first s ∧ ∀ u, SiteTrace first s u → SitePre code second u := by
  induction first generalizing s with
  | nil => simp [SitePre, SiteTrace]
  | cons site rest ih =>
    simp only [List.cons_append, SitePre, SiteTrace]
    by_cases atSite : s.RIP = site.pc
    · simp only [atSite, ite_true, ih]
      constructor
      · rintro ⟨pre, avoid, tail⟩
        refine ⟨⟨pre, avoid, fun u hu => (tail u hu).1⟩, ?_⟩
        rintro t ⟨u, hu, trace⟩
        exact (tail u hu).2 t trace
      · rintro ⟨⟨pre, avoid, tail⟩, suffix⟩
        refine ⟨pre, avoid, ?_⟩
        intro u hu
        exact ⟨tail u hu, fun t ht => suffix t ⟨u, hu, ht⟩⟩
    · simp only [atSite, ite_false, ih]

end Sha2.Proofs.Common.SHA256.Absorb.Blocks


namespace Sha2.Proofs.Common.SHA256.Instances.Absorption
open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Spec.Program Sha2.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

set_option maxHeartbeats 1000000 in
theorem clone_next_prefix_trace {p : BitVec 64} {index restore : BitVec 4}
    {s t : RamState}
    (distinct : [index, restore, 1, 2, 4, 6, 7].Pairwise (· ≠ ·))
    (rip : s.RIP = p)
    (trace : Blocks.SiteTrace [⟨p, .incrementIndex index⟩,
      ⟨(p + 3 : BitVec 64), .constant 1 13⟩,
      ⟨(p + 8 : BitVec 64), .address 2 (.sib 4 none 0 (.d8 0x70))⟩,
      ⟨(p + 13 : BitVec 64), .move 7 2⟩, ⟨(p + 16 : BitVec 64), .move 6 restore⟩] s t) :
    t.RIP = (p + 19 : BitVec 64) ∧ rspOf t = rspOf s ∧
    Blocks.readReg t index = Blocks.readReg s index + 1 ∧
    rcx.read t = 13 ∧ (.reg 2 : Operand 64).read t = (rspOf s + 112 : BitVec 64) ∧
    rdi.read t = (rspOf s + 112 : BitVec 64) ∧ rsi.read t = Blocks.readReg s restore ∧
    Blocks.readReg t restore = Blocks.readReg s restore ∧
    AgreesExcept [.reg (index.setWidth 5), .reg 1, .reg 2, .reg 7, .reg 6, .flags, .rip] s t := by
  simp only [Blocks.SiteTrace, rip, ite_true] at trace
  obtain ⟨a, inc, trace⟩ := trace
  have arip : a.RIP = (p + 3 : BitVec 64) := inc.rip
  simp only [arip, ite_true] at trace
  obtain ⟨b, constant, trace⟩ := trace
  have brip : b.RIP = (p + 8 : BitVec 64) := by simpa [Blocks.effect, movR32Imm32Effect,
    Blocks.bytes, encodeMovR32Imm32, BitVec.add_assoc] using constant.rip
  simp only [brip, ite_true] at trace
  obtain ⟨c, address, trace⟩ := trace
  have crip : c.RIP = (p + 13 : BitVec 64) := by simpa [Blocks.effect, leaR64Effect,
    leaLen, AddrMode.tail, Disp.bytes, BitVec.add_assoc] using address.rip
  simp only [crip, ite_true] at trace
  obtain ⟨d, move7, trace⟩ := trace
  have drip : d.RIP = (p + 16 : BitVec 64) := by simpa [Blocks.effect, movR64R64Effect,
    BitVec.add_assoc] using move7.rip
  simp only [drip, ite_true] at trace
  obtain ⟨e, move6, rfl⟩ := trace
  have agr : AgreesExcept [.reg (index.setWidth 5), .reg 1, .reg 2, .reg 7, .reg 6,
      .flags, .rip] s t :=
    ((((inc.agrees.trans constant.agrees).trans address.agrees).trans move7.agrees).trans
      move6.agrees).mono (by
      simp [Blocks.effect, incR64Effect, movR32Imm32Effect, leaR64Effect,
        movR64R64Effect, Effect.components])
  have sep : ∀ x y : BitVec 4, x ≠ y → x.setWidth 5 ≠ y.setWidth 5 := by
    intro x y ne eq
    exact ne (by have := congrArg (BitVec.setWidth 4) eq; simpa using this)
  simp only [ne_eq, BitVec.ofNat_eq_ofNat, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, BitVec.reduceEq, not_false_eq_true, and_self,
    false_implies, implies_true, List.Pairwise.nil, and_true] at distinct
  have indexA : Blocks.readReg a index = Blocks.readReg s index + 1 := by
    simpa [Blocks.effect, incR64Effect, Write.AllHold, Blocks.readReg] using inc.writes
  have rspA : rspOf a = rspOf s := by
    apply inc.agrees.read
    simp only [Blocks.effect, incR64Effect_components, List.mem_cons,
      List.not_mem_nil, or_false, Component.reg.injEq, reduceCtorEq, or_false]
    exact Ne.symm (sep index 4 distinct.1.2.2.2.1)
  have rspB : rspOf b = rspOf s := by
    exact (constant.agrees.read (by simp [Blocks.effect, movR32Imm32Effect,
      Effect.components])).trans rspA
  have rdxC : (.reg 2 : Operand 64).read c = (rspOf s + 112 : BitVec 64) := by
    have writes := address.writes
    change (.reg 2 : Operand 64).read c = rspOf b + 112 at writes
    exact writes.trans (congrArg (fun x : BitVec 64 => x + 112) rspB)
  have ine1 := sep index 1 distinct.1.2.1
  have ine2 := sep index 2 distinct.1.2.2.1
  have ine4 := sep index 4 distinct.1.2.2.2.1
  have ine6 := sep index 6 distinct.1.2.2.2.2.1
  have ine7 := sep index 7 distinct.1.2.2.2.2.2
  have rnei := Ne.symm (sep index restore distinct.1.1)
  have rne1 := sep restore 1 distinct.2.1
  have rne2 := sep restore 2 distinct.2.2.1
  have rne4 := sep restore 4 distinct.2.2.2.1
  have rne6 := sep restore 6 distinct.2.2.2.2.1
  have rne7 := sep restore 7 distinct.2.2.2.2.2
  change index.setWidth 5 ≠ (1 : BitVec 5) at ine1
  change index.setWidth 5 ≠ (2 : BitVec 5) at ine2
  change index.setWidth 5 ≠ (4 : BitVec 5) at ine4
  change index.setWidth 5 ≠ (6 : BitVec 5) at ine6
  change index.setWidth 5 ≠ (7 : BitVec 5) at ine7
  change restore.setWidth 5 ≠ (1 : BitVec 5) at rne1
  change restore.setWidth 5 ≠ (2 : BitVec 5) at rne2
  change restore.setWidth 5 ≠ (4 : BitVec 5) at rne4
  change restore.setWidth 5 ≠ (6 : BitVec 5) at rne6
  change restore.setWidth 5 ≠ (7 : BitVec 5) at rne7
  have afterInc : AgreesExcept [.reg 1, .reg 2, .reg 7, .reg 6, .rip] a t :=
    (((constant.agrees.trans address.agrees).trans move7.agrees).trans move6.agrees).mono
      (by simp [Blocks.effect, movR32Imm32Effect, leaR64Effect, movR64R64Effect,
        Effect.components])
  have afterConstant : AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] b t :=
    ((address.agrees.trans move7.agrees).trans move6.agrees).mono
      (by simp [Blocks.effect, leaR64Effect, movR64R64Effect, Effect.components])
  have afterAddress : AgreesExcept [.reg 7, .reg 6, .rip] c t :=
    (move7.agrees.trans move6.agrees).mono
      (by simp [Blocks.effect, movR64R64Effect, Effect.components])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, agr⟩
  · simpa [Blocks.effect, movR64R64Effect, BitVec.add_assoc] using move6.rip
  · exact agr.read (by simp only [List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq, reduceCtorEq, not_or]; exact ⟨Ne.symm ine4, by decide, by decide, by decide, by decide⟩)
  · exact (afterInc.read (by simp only [List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq, reduceCtorEq, not_or]; exact ⟨ine1, ine2, ine7, ine6⟩)).trans indexA
  · have value : rcx.read b = 13 := by
      simpa [Blocks.effect, movR32Imm32Effect, Write.AllHold] using constant.writes
    exact (afterConstant.read (by simp)).trans value
  · exact (afterAddress.read (by simp)).trans rdxC
  · have value : rdi.read d = (.reg 2 : Operand 64).read c := move7.writes
    exact (move6.agrees.read (by simp [Blocks.effect, movR64R64Effect,
      Effect.components])).trans (value.trans rdxC)
  · have value : rsi.read t = Blocks.readReg d restore := move6.writes
    have before : AgreesExcept [.reg (index.setWidth 5), .reg 1, .reg 2, .reg 7,
        .flags, .rip] s d :=
      (((inc.agrees.trans constant.agrees).trans address.agrees).trans move7.agrees).mono
        (by simp [Blocks.effect, incR64Effect, movR32Imm32Effect, leaR64Effect,
          movR64R64Effect, Effect.components])
    exact value.trans (before.read (by simp only [List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq, reduceCtorEq, not_or]; exact ⟨rnei, rne1, rne2, rne7⟩))
  · exact agr.read (by simp only [List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq, reduceCtorEq, not_or]; exact ⟨rnei, rne1, rne2, rne7, rne6⟩)

theorem clone_next_suffix_pre {p : BitVec 64} {index : BitVec 4}
    {disp : Blocks.Displacement} {s : RamState} {code : CodeMap}
    (pre : Blocks.Pre p .clone s)
    (avoid : (Blocks.effect p .clone s).Avoids code)
    (countRead : MemReadable s (rspOf s + 104) 8) :
    Blocks.SitePre code [⟨p, .clone⟩,
      ⟨p + 3, .compareIndexStack index (.d8 0x68)⟩,
      ⟨p + 8, .branch 4 disp⟩] s := by
  have rip : s.RIP = p := pre.1.rip
  simp only [Blocks.SitePre, rip, ite_true]
  refine ⟨pre, avoid, ?_⟩
  intro u copy
  have urip : u.RIP = (p + 3 : BitVec 64) := copy.rip
  simp only [urip, ite_true]
  have rsp : rspOf u = rspOf s := copy.agrees.read (by simp [Blocks.effect])
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨urip, by decide, ?_⟩
    change MemReadable u (rspOf u + 104) 8
    rw [rsp]
    exact ⟨countRead.low, fun i hi => copy.agrees.grow _ (countRead.mem i hi)⟩
  · apply Effect.Avoids.of_noMem
    simp [Blocks.effect, cmpMREffect, Effect.components, Component.Covers]
  · intro v _
    change Blocks.SitePre code [⟨p + 8, .branch 4 disp⟩] v
    apply Blocks.SitePre.of_basic
    simp [Blocks.Basic]

theorem clone_next_copy_pre {l : Table.Layout} {sp p : BitVec 64} {large : Bool}
    {s t : RamState} (pre : Table.NextPre l sp large s)
    (buffer : l.chunk.buffer sp = sp) (stored : l.stored sp = sp + 112)
    (rip : t.RIP = p) (count : rcx.read t = 13)
    (source : rsi.read t = l.chunk.buffer sp) (target : rdi.read t = l.stored sp)
    (memory : t.external = s.external) (direction : DirectionFlagClear t.RFLAGS)
    (apart : RangeApart (l.stored sp) 104 p 3) : Blocks.Pre p .clone t := by
  have countNat : (rcx.read t).toNat = 13 := by rw [count]; decide
  refine ⟨Common.Instructions.RepMovsq.pre_of_memory rip direction countNat ?_ ?_ ?_ ?_, countNat⟩
  · rw [source]
    exact pre.active.of_external_eq memory
  · rw [target]
    exact pre.stored.of_external_eq memory
  · left
    rw [source, target, buffer, stored]
    have low := pre.active.low
    rw [buffer] at low
    have add : (sp + 112 : BitVec 64).toNat = sp.toNat + 112 := by
      rw [BitVec.toNat_add]
      change (sp.toNat + 112) % 2^64 = sp.toNat + 112
      apply Nat.mod_eq_of_lt
      omega
    rw [add]
    omega
  · simpa only [target] using apart

 theorem clone_next_copy_avoids {p : BitVec 64} {s : RamState}
    (sites : List Blocks.Site) (count : rcx.read s = 13)
    (apart : ∀ site ∈ sites, RangeApart (rdi.read s) 104 site.pc
      (Blocks.bytes site.block).length) :
    (Blocks.effect p .clone s).Avoids (sites.flatMap Blocks.Site.code) := by
  intro x hx c hc hcov
  change c ∈ (repMovsqEffect p s).components at hc
  rw [repMovsqEffect_components, count] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
  obtain ⟨i, hi, hxe⟩ := hcov
  obtain ⟨site, member, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
  exact apart site member i hi j hj (hxe.symm.trans hxj)

open Sha2.Proofs.Common.SHA256.Instances.Absorption.TraitTable

set_option maxRecDepth 10000 in
theorem cloneShape_next_suffix_data {l : Table.Layout} (shape : CloneShape l)
    (sp : BitVec 64) :
    l.chunk.buffer sp = sp ∧ l.stored sp = sp + 112 ∧ l.count = .stack 104 ∧
    ∃ disp, [nextCloneOf l, nextCompareOf l, nextBranchOf l] =
      [⟨(nextCloneOf l).pc, .clone⟩,
       ⟨(nextCloneOf l).pc + 3, .compareIndexStack l.index (.d8 104)⟩,
       ⟨(nextCloneOf l).pc + 8, .branch 4 disp⟩] := by
  have data := shape.2.2.1
  unfold cloneData at data
  split at data
  · rename_i _ _ _ _ countSlot loadPC index source length pointers lengths tailPC tail
      tailAddress ci0 c0 v0 ci1 bsrc0 restore0 ci2 dst0 restore1 ci3 dst1 src1 ci4 co0
      index0 co1 c1 v1 co2 addrReg addrMode co3 dst2 src2 co4 dst3 restore2 co5 co6
      index1 countOffset co7 cc disp hc hl hi ho
    simp only [decide_eq_true_eq] at data
    have buffer : l.chunk.bufferOffset = 0 := by grind only
    have stored : l.storedOffset = 112 := by grind only
    have count : countSlot = 104 := by grind only
    have index : index1 = l.index := by grind only
    have offset : countOffset = .d8 104 := by grind only
    have cond : cc = 4 := by grind only
    have pcs : co5 = l.chunk.smallExit + 22 ∧ co6 = l.chunk.smallExit + 25 ∧
        co7 = l.chunk.smallExit + 30 := by grind only
    refine ⟨?_, ?_, ?_, disp, ?_⟩
    · simp [Layout.buffer, buffer]
    · simp [Table.Layout.stored, stored]
    · simpa only [count] using hc
    · simp [nextCloneOf, nextCompareOf, nextBranchOf, ho, index, offset, cond,
        pcs.1, pcs.2.1, pcs.2.2, BitVec.add_assoc]
  · contradiction

end Sha2.Proofs.Common.SHA256.Instances.Absorption
namespace Sha2.Proofs.Common.SHA256.Instances.Absorption
open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption.TraitTable
open Sha2.Spec.Program Sha2.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem cloneShape_next_prefix_trace {l : Table.Layout} (shape : CloneShape l)
    (sp : BitVec 64) (large : Bool) {s t : RamState}
    (pre : Table.NextPre l sp large s)
    (trace : Blocks.SiteTrace (nextPrefixOf l large) s t) :
    t.RIP = (nextCloneOf l).pc ∧ rspOf t = sp ∧
    Blocks.readReg t l.index = Blocks.readReg s l.index + 1 ∧
    rcx.read t = 13 ∧ (.reg 2 : Operand 64).read t = l.stored sp ∧
    rdi.read t = l.stored sp ∧ rsi.read t = l.chunk.buffer sp ∧
    (∀ r ∈ l.chunk.bufferRestore, Blocks.readReg t r = l.chunk.buffer sp) ∧
    AgreesExcept (l.chunk.clobbered.map Component.reg ++
      [.reg (l.index.setWidth 5), .flags, .rip]) s t := by
  have data := shape.2.2.1
  unfold cloneData at data
  split at data
  · rename_i _ _ _ _ countSlot loadPC index source length pointers lengths tailPC tail
      tailAddress ci0 c0 v0 ci1 bsrc0 restore0 ci2 dst0 restore1 ci3 dst1 src1 ci4 co0
      index0 co1 c1 v1 co2 addrReg addrMode co3 dst2 src2 co4 dst3 restore2 co5 co6
      index1 countOffset co7 cc disp hc hl hi ho
    simp only [decide_eq_true_eq] at data
    have small : cloneNextSmall l bsrc0 restore0 = true := by grind only
    have big : cloneNextLarge l = true := by grind only
    have pcs : co0 = l.chunk.smallExit + 3 ∧ co1 = l.chunk.smallExit + 6 ∧
        co2 = l.chunk.smallExit + 11 ∧ co3 = l.chunk.smallExit + 16 ∧
        co4 = l.chunk.smallExit + 19 ∧ co5 = l.chunk.smallExit + 22 := by grind only
    rcases data with ⟨indexEq, countSlotEq, bufferOffsetEq, clobbers, pointerSlotEq,
      lengthSlotEq, storedOffsetEq, srcEq, lenEq, tailEq, alignedEq, restoreEq,
      bufferEq, bulkEq, distinct, index0Eq, index1Eq, c0Eq, v0Eq, c1Eq, v1Eq,
      bsrcEq, restore1Eq, dst0Eq, dst1Eq, src1Eq, addrRegEq, addrModeEq,
      dst2Eq, src2Eq, dst3Eq, restore2Eq, countOffsetEq, ccEq, rest⟩
    have distinctCore : [index, restore0, 1, 2, 4, 6, 7].Pairwise (· ≠ ·) := by
      simp only [cloneRegisterData, ne_eq, BitVec.ofNat_eq_ofNat, List.pairwise_cons,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        BitVec.reduceEq, not_false_eq_true, false_implies, implies_true, List.Pairwise.nil,
        and_self, and_true, Bool.decide_and, decide_not, Bool.and_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at distinct
      simp only [ne_eq, BitVec.ofNat_eq_ofNat, List.pairwise_cons, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, BitVec.reduceEq,
        not_false_eq_true, and_self, false_implies, implies_true, List.Pairwise.nil, and_true]
      grind only
    have sep : index.setWidth 5 ≠ restore0.setWidth 5 ∧
        (4 : BitVec 5) ≠ restore0.setWidth 5 := by
      have neq : index ≠ restore0 ∧ (4 : BitVec 4) ≠ restore0 := by
        simp only [cloneRegisterData, Bool.and_eq_true, decide_eq_true_eq] at distinct
        grind only
      constructor <;> intro eq
      · exact neq.1 (by have := congrArg (BitVec.setWidth 4) eq; simpa using this)
      · exact neq.2 (by have := congrArg (BitVec.setWidth 4) eq; simpa using this)
    simp only [nextPrefixOf, Blocks.SiteTrace.append_iff] at trace
    obtain ⟨u, lead, core⟩ := trace
    have leadFacts : u.RIP = (l.chunk.smallExit + 3 : BitVec 64) ∧
        rspOf u = sp ∧ Blocks.readReg u index = Blocks.readReg s index ∧
        Blocks.readReg u restore0 = l.chunk.buffer sp ∧
        AgreesExcept [.reg (restore0.setWidth 5), .rip] s u := by
      cases large
      · unfold cloneNextSmall at small
        split at small
        · rename_i pc dst src hs
          simp only [decide_eq_true_eq] at small
          rcases small with ⟨hpc, hdst, hsrc, _⟩
          subst pc dst src
          have rip : s.RIP = (l.chunk.smallExit : BitVec 64) := pre.rip
          simp only [Bool.false_eq_true, ite_false, hs, Blocks.SiteTrace, rip,
            ite_true] at lead
          obtain ⟨v, step, rfl⟩ := lead
          have agr : AgreesExcept [.reg (restore0.setWidth 5), .rip] s u := by
            simpa only [Blocks.effect, movR64R64Effect_components] using step.agrees
          have buffer : Blocks.readReg s bsrc0 = l.chunk.buffer sp :=
            pre.bufferRegister bsrc0 (by simp [bufferEq])
          refine ⟨step.rip, (agr.read (n := 64) (by simpa using sep.2)).trans pre.rsp,
            agr.read (n := 64) (by simpa using sep.1), ?_, agr⟩
          exact (show Blocks.readReg u restore0 = Blocks.readReg s bsrc0 from step.writes).trans buffer
        · contradiction
      · unfold cloneNextLarge at big
        split at big
        · rename_i pc offset hb
          simp only [decide_eq_true_eq] at big
          rcases big with ⟨hpc, target, _, _⟩
          subst pc
          have rip : s.RIP = (l.chunk.largeExit : BitVec 64) := pre.rip
          simp only [ite_true, hb, Blocks.SiteTrace, rip] at lead
          obtain ⟨v, step, rfl⟩ := lead
          have agr : AgreesExcept [.rip] s u := by
            simpa [Blocks.effect, jmpEffect, Effect.components] using step.agrees
          refine ⟨step.rip.trans target, (agr.read (by simp)).trans pre.rsp,
            agr.read (by simp), ?_, agr.mono (by simp)⟩
          exact (agr.read (by simp)).trans (pre.workingPointer rfl restore0 (by simp [restoreEq]))
        · contradiction
    have core' : Blocks.SiteTrace
        [⟨l.chunk.smallExit + 3, .incrementIndex index⟩,
         ⟨(l.chunk.smallExit + 3) + 3, .constant 1 13⟩,
         ⟨(l.chunk.smallExit + 3) + 8, .address 2 (.sib 4 none 0 (.d8 0x70))⟩,
         ⟨(l.chunk.smallExit + 3) + 13, .move 7 2⟩,
         ⟨(l.chunk.smallExit + 3) + 16, .move 6 restore0⟩] u t := by
      simpa [ho, List.take, index0Eq, c1Eq, v1Eq, addrRegEq, addrModeEq,
        dst2Eq, src2Eq, dst3Eq, restore2Eq, pcs.1, pcs.2.1, pcs.2.2.1,
        pcs.2.2.2.1, pcs.2.2.2.2.1, BitVec.add_assoc, BitVec.reduceAdd] using core
    obtain ⟨trip, trsp, tidx, tcx, tdx, tdi, tsi, trestore, agr⟩ :=
      clone_next_prefix_trace distinctCore leadFacts.1 core'
    have stored : l.stored sp = sp + 112 := by simp [Table.Layout.stored, storedOffsetEq]
    refine ⟨?_, trsp.trans leadFacts.2.1, ?_, tcx, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [nextCloneOf, ho, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, pcs.2.2.2.2.2, BitVec.add_assoc, BitVec.reduceAdd] using trip
    · simpa only [indexEq, leadFacts.2.2.1] using tidx
    · simpa only [leadFacts.2.1, stored] using tdx
    · simpa only [leadFacts.2.1, stored] using tdi
    · exact tsi.trans leadFacts.2.2.2.1
    · intro r hr
      have : r = restore0 := by simpa [restoreEq] using hr.symm
      subst r
      exact trestore.trans leadFacts.2.2.2.1
    · apply (leadFacts.2.2.2.2.trans agr).mono
      simp only [List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq,
        and_true] at clobbers
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
        List.mem_map, indexEq]
      intro c member
      rcases member with (rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact Or.inl ⟨_, clobbers.2.2.2.2.2.2.2.2, rfl⟩
      · exact Or.inr (by simp)
      · exact Or.inr (by simp)
      · exact Or.inl ⟨1, clobbers.2.1, rfl⟩
      · exact Or.inl ⟨2, clobbers.2.2.1, rfl⟩
      · exact Or.inl ⟨7, clobbers.2.2.2.2.1, rfl⟩
      · exact Or.inl ⟨6, clobbers.2.2.2.1, rfl⟩
      · exact Or.inr (by simp)
      · exact Or.inr (by simp)
  · contradiction
end Sha2.Proofs.Common.SHA256.Instances.Absorption
namespace Sha2.Proofs.Common.SHA256.Instances.Absorption
open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption.TraitTable
open Sha2.Spec.Program Sha2.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem cloneShape_next_pre {l : Table.Layout} (shape : CloneShape l)
    (sp : BitVec 64) (large : Bool) (s : RamState) (pre : Table.NextPre l sp large s) :
    Blocks.SitePre (((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut).flatMap
      Blocks.Site.code) ((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut) s := by
  let code := (((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut).flatMap
    Blocks.Site.code)
  change Blocks.SitePre code ((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut) s
  rw [← cloneShape_next_sites shape large]
  apply (Blocks.SitePre.append_iff _ _ _ _).mpr
  refine ⟨Blocks.SitePre.of_basic _ _ (cloneShape_next_prefix_basic shape large) s, ?_⟩
  intro t trace
  obtain ⟨rip, rsp, index, count, rdx, target, source, restore, agr⟩ :=
    cloneShape_next_prefix_trace shape sp large pre trace
  obtain ⟨buffer, stored, countSlot, disp, suffix⟩ := cloneShape_next_suffix_data shape sp
  have memory : t.external = s.external := agr.external (by
    intro c hc a
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ⟨r, _, rfl⟩ | rfl | rfl | rfl <;> simp [Component.Covers])
  have direction : DirectionFlagClear t.RFLAGS :=
    (agr.directionFlagClear (by simp) pre.direction).df
  have member : nextCloneOf l ∈ (if large then l.nextLarge else l.nextSmall) ++ l.cloneOut := by
    rw [← cloneShape_next_sites shape large]
    simp
  have cloneBlock : (nextCloneOf l).block = .clone := by
    have head := congrArg (fun xs : List Blocks.Site => xs[0]?) suffix
    have eq : nextCloneOf l = ⟨(nextCloneOf l).pc, .clone⟩ := by simpa using head
    exact congrArg Blocks.Site.block eq
  have apart : RangeApart (l.stored sp) 104 (nextCloneOf l).pc 3 := by
    have ap := pre.codeApart (nextCloneOf l) member
    rw [cloneBlock] at ap
    exact ap
  rw [suffix]
  apply clone_next_suffix_pre
  · exact clone_next_copy_pre pre buffer stored rip count source target memory direction apart
  · apply clone_next_copy_avoids _ count
    intro site member
    rw [target]
    exact pre.codeApart site member
  · rw [rsp]
    have read := pre.countRead 104 countSlot
    exact read.of_external_eq memory

end Sha2.Proofs.Common.SHA256.Instances.Absorption


namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Spec.Program Sha2.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Field

theorem clone_compare_branch_trace {s t : RamState} {p finish head : BitVec 64}
    {index : BitVec 4} {disp : Blocks.Displacement}
    (rip : s.RIP = p)
    (len : (Blocks.bytes (.compareIndexStack index (.d8 0x68))).length = 5)
    (target : branchTarget (p + 5) (Blocks.bytes (.branch 4 disp)).length disp.value = finish)
    (fall : p + 5 + BitVec.ofNat 64 (Blocks.bytes (.branch 4 disp)).length = head)
    (trace : Blocks.SiteTrace [⟨p, .compareIndexStack index (.d8 0x68)⟩,
      ⟨p + 5, .branch 4 disp⟩] s t) :
    t.RIP = (if Blocks.readReg s index = memLoad s.external (rspOf s + 104) 64
      then finish else head) ∧ AgreesExcept [.flags, .rip] s t := by
  simp only [Blocks.SiteTrace, rip, ite_true] at trace
  obtain ⟨u, cmp, trace⟩ := trace
  have urip : u.RIP = (p + 5 : BitVec 64) := by
    have h := cmp.rip
    change u.RIP = p + BitVec.ofNat 64
      (Blocks.bytes (.compareIndexStack index (.d8 0x68))).length at h
    rw [len] at h
    exact h
  simp only [urip, ite_true] at trace
  obtain ⟨v, branch, rfl⟩ := trace
  have flags : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (memLoad s.external (rspOf s + 104) 64 == Blocks.readReg s index) := by
    have flag := cmp.flag .ZF
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (memLoad s.external (rspOf s + 104) 64 - Blocks.readReg s index == 0) at flag
    rw [flag]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    rw [show (0 : BitVec 64) + Blocks.readReg s index = Blocks.readReg s index from BitVec.zero_add _]
  constructor
  · have h := branch.rip
    change t.RIP = (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then
      branchTarget (p + 5) (Blocks.bytes (.branch 4 disp)).length disp.value
      else p + 5 + BitVec.ofNat 64 (Blocks.bytes (.branch 4 disp)).length) at h
    rw [flags, target, fall] at h
    simp only [beq_iff_eq] at h
    simpa only [eq_comm] using h
  · exact (cmp.agrees.trans branch.agrees).mono (by
      simp [Blocks.effect, cmpMREffect, jccEffect, branchEffect, Effect.components])

theorem clone_effect_bytes {s t : RamState} {p : BitVec 64}
    (count : (rcx.read s).toNat = 13)
    (source : MemReadable s (rsi.read s) 104)
    (target : MemReadable s (rdi.read s) 104)
    (copy : (repMovsqEffect p s).Holds s t) :
    ∀ i < 104, t.external[rdi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  intro i hi
  have value := repMovsqEffect_bytes copy i (by rw [count]; omega)
  have src := Bytes.of_isSome source.mem i hi
  have dst := Bytes.of_isSome
    (fun j hj => copy.agrees.grow _ (target.mem j hj)) i hi
  exact dst.trans ((congrArg some value).trans src.symm)

theorem clone_count_apart (sp : BitVec 64) :
    RangeApart (sp + 112) 104 (sp + 104) 8 := by
  intro i hi j hj equal
  have equal' : (112 : BitVec 64) + BitVec.ofNat 64 i =
      104 + BitVec.ofNat 64 j := by
    apply (BitVec.add_right_inj sp).mp
    simpa only [BitVec.add_assoc] using equal
  have values := congrArg BitVec.toNat equal'
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.add_mod_mod] at values
  omega

theorem clone_effect_count {s t : RamState} {p sp : BitVec 64}
    (count : (rcx.read s).toNat = 13)
    (target : rdi.read s = sp + 112)
    (copy : (repMovsqEffect p s).Holds s t) :
    memLoad t.external (sp + 104) 64 = memLoad s.external (sp + 104) 64 := by
  apply memLoad_congr
  intro i hi
  apply memByte_congr
  apply copy.agrees.byte
  intro c hc covers
  rw [repMovsqEffect_components, count, target] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact covers.elim
  obtain ⟨j, hj, equal⟩ := covers
  exact clone_count_apart sp j hj i hi equal.symm

theorem clone_suffix_trace {s t : RamState} {p finish head sp : BitVec 64}
    {index : BitVec 4} {disp : Blocks.Displacement}
    (rip : s.RIP = p) (rsp : rspOf s = sp)
    (count : (rcx.read s).toNat = 13)
    (dst : rdi.read s = sp + 112)
    (src : rsi.read s = sp)
    (ine : index.setWidth 5 ≠ 1 ∧ index.setWidth 5 ≠ 6 ∧ index.setWidth 5 ≠ 7)
    (source : MemReadable s sp 104)
    (targetMem : MemReadable s (sp + 112) 104)
    (len : (Blocks.bytes (.compareIndexStack index (.d8 0x68))).length = 5)
    (target : branchTarget (p + 8) (Blocks.bytes (.branch 4 disp)).length disp.value = finish)
    (fall : p + 8 + BitVec.ofNat 64 (Blocks.bytes (.branch 4 disp)).length = head)
    (trace : Blocks.SiteTrace [⟨p, .clone⟩,
      ⟨p + 3, .compareIndexStack index (.d8 0x68)⟩, ⟨p + 8, .branch 4 disp⟩] s t) :
    t.RIP = (if Blocks.readReg s index = memLoad s.external (sp + 104) 64
      then finish else head) ∧
    (∀ i < 104, t.external[sp + 112 + BitVec.ofNat 64 i]? =
      s.external[sp + BitVec.ofNat 64 i]?) ∧
    AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (sp + 112) 104, .flags, .rip] s t := by
  simp only [Blocks.SiteTrace, rip, ite_true] at trace
  obtain ⟨u, copy, trace⟩ := trace
  have urip : u.RIP = (p + 3 : BitVec 64) := copy.rip
  have suffix : Blocks.SiteTrace [⟨p + 3, .compareIndexStack index (.d8 0x68)⟩,
      ⟨p + 3 + 5, .branch 4 disp⟩] u t := by
    simpa [Blocks.SiteTrace, BitVec.add_assoc] using trace
  have endResult := clone_compare_branch_trace urip len
    (by simpa [BitVec.add_assoc] using target)
    (by simpa [BitVec.add_assoc] using fall) suffix
  have preserved : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (sp + 112) 104, .rip] s u := by
    simpa only [Blocks.effect, repMovsqEffect_components, count, dst,
      Nat.reduceMul] using copy.agrees
  have indexU : Blocks.readReg u index = Blocks.readReg s index :=
    preserved.read (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq,
        reduceCtorEq, not_or]
      exact ⟨ine.2.1, ine.2.2, ine.1⟩)
  have rspU : rspOf u = sp := (preserved.read (by simp)).trans rsp
  have countU := clone_effect_count count dst copy
  refine ⟨?_, ?_, ?_⟩
  · simpa only [indexU, rspU, countU] using endResult.1
  · have bytes := clone_effect_bytes count (by simpa only [src] using source)
      (by simpa only [dst] using targetMem) copy
    have external := endResult.2.external (by simp [Component.Covers])
    intro i hi
    rw [external]
    simpa only [dst, src] using bytes i hi
  · exact (preserved.trans endResult.2).mono (by simp)

theorem clone_suffix_count {s t : RamState} {sp : BitVec 64}
    (agrees : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (sp + 112) 104, .flags, .rip] s t) :
    memLoad t.external (sp + 104) 64 = memLoad s.external (sp + 104) 64 := by
  apply memLoad_congr
  intro i hi
  apply memByte_congr
  apply agrees.byte
  intro c hc covers
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covers.elim
  obtain ⟨j, hj, equal⟩ := covers
  exact clone_count_apart sp j hj i hi equal.symm

set_option maxHeartbeats 1000000 in
theorem clone_next_post_of_parts {l : Table.Layout} {sp : BitVec 64}
    {s u t : RamState} {large : Bool} {restore : BitVec 4}
    (buffer : l.chunk.bufferOffset = 0) (stored : l.storedOffset = 112)
    (count : l.count = .stack 104) (restoreEq : l.chunk.bufferRestore = some restore)
    (ine : l.index.setWidth 5 ≠ 1 ∧ l.index.setWidth 5 ≠ 6 ∧ l.index.setWidth 5 ≠ 7)
    (rne : restore.setWidth 5 ≠ 1 ∧ restore.setWidth 5 ≠ 6 ∧ restore.setWidth 5 ≠ 7)
    (clobbered : 1 ∈ l.chunk.clobbered ∧ 6 ∈ l.chunk.clobbered ∧ 7 ∈ l.chunk.clobbered)
    (pre : Table.NextPre l sp large s)
    (rspU : rspOf u = sp)
    (indexU : Blocks.readReg u l.index = Blocks.readReg s l.index + 1)
    (rdxU : (.reg 2 : Operand 64).read u = l.stored sp)
    (restoreU : Blocks.readReg u restore = l.chunk.buffer sp)
    (before : AgreesExcept (l.chunk.clobbered.map Component.reg ++
      [.reg (l.index.setWidth 5), .flags, .rip]) s u)
    (ripT : t.RIP = if Blocks.readReg u l.index = memLoad u.external (sp + 104) 64
      then l.exit else l.head)
    (copied : ∀ i < 104, t.external[sp + 112 + BitVec.ofNat 64 i]? =
      u.external[sp + BitVec.ofNat 64 i]?)
    (after : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (sp + 112) 104, .flags, .rip] u t) :
    Table.NextPost l sp s t := by
  have external : u.external = s.external := before.external (by
    intro c hc a covers
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ⟨r, _, rfl⟩ | rfl | rfl | rfl <;> exact covers.elim)
  have storedEq : l.stored sp = (sp + 112 : BitVec 64) := by
    simp [Table.Layout.stored, stored]
  have bufferEq : l.chunk.buffer sp = sp := by simp [Layout.buffer, buffer]
  have agrees : AgreesExcept (l.chunk.clobbered.map Component.reg ++
      [.reg (l.index.setWidth 5), .mem (l.stored sp) 104, .flags, .rip]) s t := by
    apply (before.trans after).mono
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with (hm | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hm
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inl (List.mem_map.mpr ⟨6, clobbered.2.1, rfl⟩)
    · exact Or.inl (List.mem_map.mpr ⟨7, clobbered.2.2, rfl⟩)
    · exact Or.inl (List.mem_map.mpr ⟨1, clobbered.1, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl (by rw [storedEq])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, agrees, ?_, ?_⟩
  · simpa only [indexU, external, count, Table.Count.read, BitVec.ofNat_eq_ofNat] using ripT
  · exact (after.read (by simp)).trans rspU
  · apply Eq.trans (after.read ?_) indexU
    simp only [List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq,
      reduceCtorEq, not_or]
    exact ⟨ine.2.1, ine.2.2, ine.1⟩
  · simpa only [count, Table.Count.read, external, BitVec.ofNat_eq_ofNat] using clone_suffix_count after
  · intro i hi
    simpa only [storedEq, bufferEq, external] using copied i hi
  · intro r hr
    have eq : restore = r := by simpa only [restoreEq, Option.mem_some_iff] using hr
    subst r
    apply Eq.trans (after.read ?_) restoreU
    simp only [List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq,
      reduceCtorEq, not_or]
    exact ⟨rne.2.1, rne.2.2, rne.1⟩
  · intro _
    exact (after.read (by simp)).trans rdxU
  · apply agrees.memoryWriteFrame
    intro c hc a covered
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ⟨r, _, rfl⟩ | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨i, hi, rfl⟩ := covered
    refine ⟨⟨(l.stored sp).toNat, 104⟩, by simp, ?_⟩
    have low := pre.stored.low
    simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro r notClobbered notIndex
    apply agrees.read
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      Component.reg.injEq, reduceCtorEq, not_or]
    constructor
    · rintro ⟨r', member, eq⟩
      exact notClobbered (eq ▸ member)
    · exact notIndex

end Sha2.Proofs.Common.SHA256.Instances.Absorption
namespace Sha2.Proofs.Common.SHA256.Instances.Absorption
open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption.TraitTable
open Sha2.Spec.Program Sha2.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Field

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem cloneShape_next_post {l : Table.Layout} (shape : CloneShape l)
    (sp : BitVec 64) (large : Bool) (s t : RamState) (pre : Table.NextPre l sp large s)
    (trace : Blocks.SiteTrace ((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut) s t) :
    Table.NextPost l sp s t := by
  rw [← cloneShape_next_sites shape large, Blocks.SiteTrace.append_iff] at trace
  obtain ⟨u, prefixTrace, trace⟩ := trace
  have prefixFacts := cloneShape_next_prefix_trace shape sp large pre prefixTrace
  rcases prefixFacts with ⟨ripU, rspU, indexU, countU, rdxU, dstU, srcU, restoreU, before⟩
  have external : u.external = s.external := before.external (by
    intro c hc a covers
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ⟨r, _, rfl⟩ | rfl | rfl | rfl <;> exact covers.elim)
  have data := shape.2.2.1
  unfold cloneData at data
  split at data
  · rename_i _ _ _ _ countSlot loadPC index source length pointers lengths tailPC tail
      tailAddress ci0 c0 v0 ci1 bsrc0 restore0 ci2 dst0 restore1 ci3 dst1 src1 ci4 co0
      index0 co1 c1 v1 co2 addrReg addrMode co3 dst2 src2 co4 dst3 restore2 co5 co6
      index1 countOffset co7 cc disp hc hl hi ho
    simp only [decide_eq_true_eq] at data
    have buffer : l.chunk.bufferOffset = 0 := by grind only
    have stored : l.storedOffset = 112 := by grind only
    have countSlotEq : countSlot = 104 := by grind only
    have count : l.count = .stack 104 := by simpa only [countSlotEq] using hc
    have indexEq : l.index = index := by grind only
    have index1Eq : index1 = l.index := by grind only
    have offset : countOffset = .d8 104 := by grind only
    have cond : cc = 4 := by grind only
    have restoreEq : l.chunk.bufferRestore = some restore0 := by grind only
    have regs : cloneRegisterData index source length tail restore0 = true := by grind only
    simp only [cloneRegisterData, Bool.and_eq_true, decide_eq_true_eq] at regs
    have ineRaw : index ≠ 1 ∧ index ≠ 6 ∧ index ≠ 7 := by
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false] at regs
      grind only
    have rneRaw : restore0 ≠ 1 ∧ restore0 ≠ 6 ∧ restore0 ≠ 7 := by grind only
    have widen {a b : BitVec 4} (ne : a ≠ b) : a.setWidth 5 ≠ b.setWidth 5 := by
      intro eq
      exact ne (by have := congrArg (BitVec.setWidth 4) eq; simpa using this)
    have ine : l.index.setWidth 5 ≠ 1 ∧ l.index.setWidth 5 ≠ 6 ∧ l.index.setWidth 5 ≠ 7 := by
      rw [indexEq]
      exact ⟨widen ineRaw.1, widen ineRaw.2.1, widen ineRaw.2.2⟩
    have rne : restore0.setWidth 5 ≠ 1 ∧ restore0.setWidth 5 ≠ 6 ∧ restore0.setWidth 5 ≠ 7 :=
      ⟨widen rneRaw.1, widen rneRaw.2.1, widen rneRaw.2.2⟩
    have clobs : [0, 1, 2, 6, 7, source.setWidth 5, length.setWidth 5, tail.setWidth 5,
        restore0.setWidth 5].all (fun r => decide (r ∈ l.chunk.clobbered)) = true := by grind only
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq] at clobs
    have clobbered : 1 ∈ l.chunk.clobbered ∧ 6 ∈ l.chunk.clobbered ∧ 7 ∈ l.chunk.clobbered := by grind only
    have pcs : co5 = l.chunk.smallExit + 22 ∧ co6 = l.chunk.smallExit + 25 ∧
        co7 = l.chunk.smallExit + 30 := by grind only
    have cmpLen : (Blocks.bytes (.compareIndexStack l.index (.d8 104))).length = 5 := by
      have raw : (Blocks.bytes (.compareIndexStack index1 countOffset)).length = 5 := by grind only
      simpa only [index1Eq, offset] using raw
    have targetRaw : branchTarget co7 (Blocks.bytes (.branch cc disp)).length disp.value = l.exit := by grind only
    have fallRaw : co7 + BitVec.ofNat 64 (Blocks.bytes (.branch cc disp)).length = l.head := by grind only
    have target : branchTarget ((nextCloneOf l).pc + 8)
        (Blocks.bytes (.branch 4 disp)).length disp.value = l.exit := by
      simpa [nextCloneOf, ho, pcs.1, pcs.2.2, cond, BitVec.add_assoc] using targetRaw
    have fall : (nextCloneOf l).pc + 8 + BitVec.ofNat 64
        (Blocks.bytes (.branch 4 disp)).length = l.head := by
      simpa [nextCloneOf, ho, pcs.1, pcs.2.2, cond, BitVec.add_assoc] using fallRaw
    have sites : [nextCloneOf l, nextCompareOf l, nextBranchOf l] =
        [⟨(nextCloneOf l).pc, .clone⟩,
         ⟨(nextCloneOf l).pc + 3, .compareIndexStack l.index (.d8 104)⟩,
         ⟨(nextCloneOf l).pc + 8, .branch 4 disp⟩] := by
      simp [nextCloneOf, nextCompareOf, nextBranchOf, ho, index1Eq, offset, cond,
        pcs.1, pcs.2.1, pcs.2.2, BitVec.add_assoc]
    rw [sites] at trace
    have bufferEq : l.chunk.buffer sp = sp := by simp [Layout.buffer, buffer]
    have storedEq : l.stored sp = sp + 112 := by simp [Table.Layout.stored, stored]
    have suffix := clone_suffix_trace ripU rspU (by rw [countU]; decide)
      (dstU.trans storedEq) (srcU.trans bufferEq) ine
      (by simpa only [bufferEq] using pre.active.of_external_eq external)
      (by simpa only [storedEq] using pre.stored.toMemReadable.of_external_eq external)
      cmpLen target fall trace
    exact clone_next_post_of_parts buffer stored count restoreEq ine rne clobbered pre
      rspU indexU rdxU (restoreU restore0 (by simp [restoreEq])) before
      suffix.1 suffix.2.1 suffix.2.2
  · contradiction
end Sha2.Proofs.Common.SHA256.Instances.Absorption
namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Spec.Program Sha2.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

open Sha2.Proofs.Common.Machine

open Sha2.Proofs.Common.Field

theorem cloneShape_advance [bindings : Bindings] {l : Table.Layout}
    (shape : CloneShape l) (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) (large : Bool) :
    AdvanceTriple boundary (Table.NextPre l sp large)
      (((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut).flatMap Blocks.Site.code)
      (Table.NextPost l sp) := by
  apply next_sites_run boundary sp large
    ((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut) _ stride outside
  · exact cloneShape_next_sites_inside shape large
  · exact cloneShape_next_targets shape large
  · intro site member
    exact cloneShape_next_code l large member
  · intro s pre
    exact cloneShape_next_pre shape sp large s pre
  · intro s t pre trace
    exact cloneShape_next_post shape sp large s t pre trace

end Sha2.Proofs.Common.SHA256.Instances.Absorption
