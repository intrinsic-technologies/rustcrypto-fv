import Sha2.Proofs.Common.SHA256.Instances.Absorb.TraitTable.Shape
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableRun
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Normalize
import Sha2.Proofs.Common.SHA256.Instances.Absorb.LoadPre

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.Field
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

 theorem clone_load_disjoint {l : Table.Layout} {sp : BitVec 64} {s : RamState}
    (pre : Table.LoadPre l sp s) (buffer : l.chunk.bufferOffset = 0)
    (stored : l.storedOffset = 0x70) :
    (l.chunk.buffer sp).toNat + 104 ≤ (l.stored sp).toNat := by
  have low := pre.active.low
  simp only [Layout.buffer, buffer, BitVec.add_zero] at low ⊢
  simp only [Table.Layout.stored, stored, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

 theorem clone_load_clone_pre {l : Table.Layout} {sp : BitVec 64} {s u : RamState}
    (pre : Table.LoadPre l sp s) (buffer : l.chunk.bufferOffset = 0)
    (stored : l.storedOffset = 0x70) {pc : BitVec 64}
    (rip : u.RIP = pc) (memory : u.external = s.external)
    (direction : DirectionFlagClear u.RFLAGS)
    (source : rsi.read u = l.stored sp) (target : rdi.read u = l.chunk.buffer sp)
    (count : rcx.read u = 13)
    (apart : RangeApart (l.chunk.buffer sp) 104 pc 3) :
    Blocks.Pre pc .clone u := by
  have n : (rcx.read u).toNat = 13 := by rw [count]; decide
  refine ⟨RepMovsq.pre_of_memory rip direction n ?_ ?_ ?_ ?_, n⟩
  · rw [source]
    exact pre.stored.of_external_eq memory
  · rw [target]
    exact pre.active.of_external_eq memory
  · rw [source, target]
    exact Or.inr (clone_load_disjoint pre buffer stored)
  · simpa only [target] using apart

attribute [local x86_compose] Blocks.effect Blocks.readReg

private def cloneLoadPrefix (p : BitVec 64) (index source length restore : BitVec 4)
    (pointers lengths : Disp) : List Blocks.Site :=
  [⟨p, .loadPair index source length pointers lengths⟩,
   ⟨p + 24, .constant 1 13⟩, ⟨p + 29, .move 3 restore⟩,
   ⟨p + 32, .move 7 restore⟩, ⟨p + 35, .move 6 2⟩]

private def cloneLoadPrefixEffect (p : BitVec 64) (index source length restore : BitVec 4)
    (pointers lengths : Disp) (s : RamState) : Effect :=
  { rip := p + 38
    writes := [
      ⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + lengths.value) 64⟩,
      ⟨(.reg (source.setWidth 5) : Operand 64), memLoad s.external
        (memLoad s.external (rspOf s + pointers.value) 64 + (Blocks.readReg s index <<< 3)) 64⟩,
      ⟨(.reg (length.setWidth 5) : Operand 64), memLoad s.external
        (memLoad s.external (rspOf s + lengths.value) 64 + (Blocks.readReg s index <<< 3)) 64⟩,
      ⟨(.reg 1 : Operand 64), 13⟩,
      ⟨(.reg 3 : Operand 64), Blocks.readReg s restore⟩,
      ⟨(.reg 7 : Operand 64), Blocks.readReg s restore⟩,
      ⟨(.reg 6 : Operand 64), Blocks.readReg s 2⟩] }

set_option maxHeartbeats 800000 in
private theorem cloneLoadPrefix_trace {p : BitVec 64}
    {index source length tail restore : BitVec 4} {pointers lengths : Disp}
    (size : (Blocks.bytes (.loadPair index source length pointers lengths)).length = 24)
    (distinct : cloneRegisterData index source length tail restore = true)
    {s t : RamState} (rip : s.RIP = p)
    (trace : Blocks.SiteTrace (cloneLoadPrefix p index source length restore pointers lengths) s t) :
    (cloneLoadPrefixEffect p index source length restore pointers lengths s).Holds s t := by
  have regfacts := distinct
  simp only [cloneRegisterData, Bool.and_eq_true, decide_eq_true_eq] at regfacts
  obtain ⟨⟨first, second⟩, rest⟩ := regfacts
  have first5 := first.map (S := fun a b : BitVec 5 => a ≠ b)
    (fun r => r.setWidth 5) (fun a b hab he => hab ((Blocks.widened_eq _ _).mp he))
  have second5 := second.map (S := fun a b : BitVec 5 => a ≠ b)
    (fun r => r.setWidth 5) (fun a b hab he => hab ((Blocks.widened_eq _ _).mp he))
  simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true,
    and_true, List.Pairwise.nil] at first5 second5
  rcases first5 with ⟨⟨_, _, _, _, _⟩, ⟨hsl, _, hs0, _⟩, ⟨_, hl0, _⟩, _, _⟩
  rcases second5 with ⟨_, ⟨_, _, hs1, hs2, hs3, hs6, hs7⟩,
    ⟨_, hl1, hl2, hl3, hl6, hl7⟩, _⟩
  obtain ⟨hri, hrs, hrl, hr0, hr4, hr1, hr2, hr3, hr6, hr7⟩ := rest
  have rwiden (r : BitVec 4) (h : restore ≠ r) : restore.setWidth 5 ≠ r.setWidth 5 :=
    fun he => h ((Blocks.widened_eq _ _).mp he)
  have hrs5 := rwiden source hrs
  have hrl5 := rwiden length hrl
  have hr05 := rwiden 0 hr0
  have hr15 := rwiden 1 hr1
  have hr35 := rwiden 3 hr3
  simp only [BitVec.reduceSetWidth] at hs0 hl0 hs1 hs2 hs3 hs6 hs7 hl1 hl2 hl3 hl6 hl7 hr05 hr15 hr35
  have pairLocal : Effect.Local (Blocks.effect p (.loadPair index source length pointers lengths)) := by
    apply Effect.Local.of_congr
    · intro a b obs
      have hm (addr : BitVec 64) : memLoad a.external addr 64 = memLoad b.external addr 64 :=
        memLoad_congr (fun i _ => obs.mem _)
      simp only [Blocks.effect, Blocks.readReg, rspOf, hm,
        ← obs.read_reg 4, ← obs.read_reg (index.setWidth 5)]
    · intro; rfl
    · intro; simp [Blocks.effect, Write.Full, Operand.Full]
  have composable : Blocks.Composable (fun u => u.RIP = p)
      (cloneLoadPrefix p index source length restore pointers lengths) Effect.start := by
    simp only [cloneLoadPrefix, Blocks.Composable]
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
    all_goals
      intro s u v pre before _ step
      apply before.seq ?_ ?_ step
    · exact pairLocal
    · x86_norm [Blocks.nextEffect, size, pre]
    · exact movR32Imm32Effect_local
    · x86_norm [Blocks.nextEffect, size, pre]
    · exact movR64R64Effect_local
    · x86_norm [Blocks.nextEffect, size, pre, hs0, hl0, hs1, hs2, hs3, hs6, hs7, hl1, hl2, hl3, hl6, hl7,
        hsl, hrs5, hrl5, hr05, hr15, hr35,
        Ne.symm hs0, Ne.symm hl0, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3,
        Ne.symm hs6, Ne.symm hs7, Ne.symm hl1, Ne.symm hl2, Ne.symm hl3,
        Ne.symm hl6, Ne.symm hl7, Ne.symm hsl, Ne.symm hrs5, Ne.symm hrl5,
        Ne.symm hr05, Ne.symm hr15, Ne.symm hr35, List.forall_mem_cons, List.forall_mem_nil]
    · exact movR64R64Effect_local
    · x86_norm [Blocks.nextEffect, size, pre, hs0, hl0, hs1, hs2, hs3, hs6, hs7, hl1, hl2, hl3, hl6, hl7,
        hsl, hrs5, hrl5, hr05, hr15, hr35,
        Ne.symm hs0, Ne.symm hl0, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3,
        Ne.symm hs6, Ne.symm hs7, Ne.symm hl1, Ne.symm hl2, Ne.symm hl3,
        Ne.symm hl6, Ne.symm hl7, Ne.symm hsl, Ne.symm hrs5, Ne.symm hrl5,
        Ne.symm hr05, Ne.symm hr15, Ne.symm hr35, List.forall_mem_cons, List.forall_mem_nil]
    · exact movR64R64Effect_local
    · x86_norm [Blocks.nextEffect, size, pre, hs0, hl0, hs1, hs2, hs3, hs6, hs7, hl1, hl2, hl3, hl6, hl7,
        hsl, hrs5, hrl5, hr05, hr15, hr35,
        Ne.symm hs0, Ne.symm hl0, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3,
        Ne.symm hs6, Ne.symm hs7, Ne.symm hl1, Ne.symm hl2, Ne.symm hl3,
        Ne.symm hl6, Ne.symm hl7, Ne.symm hsl, Ne.symm hrs5, Ne.symm hrl5,
        Ne.symm hr05, Ne.symm hr15, Ne.symm hr35, List.forall_mem_cons, List.forall_mem_nil]
  have folded := trace.normalized composable rip
  apply folded.weaken
  · x86_norm [Blocks.foldEffect, Blocks.nextEffect, cloneLoadPrefix,
      cloneLoadPrefixEffect, rip, size]
  · x86_norm [Blocks.foldEffect, Blocks.nextEffect, cloneLoadPrefix,
      cloneLoadPrefixEffect, rip, size, hs0, hl0, hs1, hs2, hs3, hs6, hs7, hl1, hl2, hl3, hl6, hl7,
        hsl, hrs5, hrl5, hr05, hr15, hr35,
        Ne.symm hs0, Ne.symm hl0, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3,
        Ne.symm hs6, Ne.symm hs7, Ne.symm hl1, Ne.symm hl2, Ne.symm hl3,
        Ne.symm hl6, Ne.symm hl7, Ne.symm hsl, Ne.symm hrs5, Ne.symm hrl5,
        Ne.symm hr05, Ne.symm hr15, Ne.symm hr35, List.forall_mem_cons, List.forall_mem_nil]
  · intro flag; cases flag <;> x86_norm [Blocks.foldEffect, Blocks.nextEffect,
      cloneLoadPrefix, cloneLoadPrefixEffect, rip, size]
  · x86_norm [Blocks.foldEffect, Blocks.nextEffect, cloneLoadPrefix,
      cloneLoadPrefixEffect, rip, size, hs0, hl0, hs1, hs2, hs3, hs6, hs7, hl1, hl2, hl3, hl6, hl7,
        hsl, hrs5, hrl5, hr05, hr15, hr35,
        Ne.symm hs0, Ne.symm hl0, Ne.symm hs1, Ne.symm hs2, Ne.symm hs3,
        Ne.symm hs6, Ne.symm hs7, Ne.symm hl1, Ne.symm hl2, Ne.symm hl3,
        Ne.symm hl6, Ne.symm hl7, Ne.symm hsl, Ne.symm hrs5, Ne.symm hrl5,
        Ne.symm hr05, Ne.symm hr15, Ne.symm hr35, List.forall_mem_cons, List.forall_mem_nil]

private theorem cloneLoadPrefix_run [bindings : Bindings] (boundary : ReturnBoundary)
    (stride : UnitStringStride bindings) (outside : ¬ InProgram boundary.rip)
    (p : BitVec 64) (index source length tail restore : BitVec 4) (pointers lengths : Disp)
    (size : (Blocks.bytes (.loadPair index source length pointers lengths)).length = 24)
    (distinct : cloneRegisterData index source length tail restore = true)
    (code : CodeMap)
    (inside : ∀ site ∈ cloneLoadPrefix p index source length restore pointers lengths,
      Sha2.Proofs.Common.Machine.BlockInProgram site.pc (Blocks.bytes site.block).length)
    (included : ∀ site ∈ cloneLoadPrefix p index source length restore pointers lengths,
      ∀ x ∈ site.code, x ∈ code) :
    AdvanceTriple boundary (Blocks.Pre p (.loadPair index source length pointers lengths))
      code (Effect.post (cloneLoadPrefixEffect p index source length restore pointers lengths)) := by
  intro s ready loaded pre
  have targets : ∀ site ∈ cloneLoadPrefix p index source length restore pointers lengths,
      match site.block with
      | .branch _ disp | .jump disp => InProgram (branchTarget site.pc
          (Blocks.bytes site.block).length disp.value)
      | _ => True := by
    intro site member
    simp only [cloneLoadPrefix, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> trivial
  have sitePre : Blocks.SitePre code
      (cloneLoadPrefix p index source length restore pointers lengths) s := by
    simp only [cloneLoadPrefix, Blocks.SitePre, pre.rip, ite_true]
    refine ⟨pre, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Blocks.effect, Effect.components, Component.Covers]
    · intro u _
      apply Blocks.SitePre.of_basic code
        [⟨p + 24, .constant 1 13⟩, ⟨p + 29, .move 3 restore⟩,
         ⟨p + 32, .move 7 restore⟩, ⟨p + 35, .move 6 2⟩]
      intro site member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> trivial
  obtain ⟨n, t, run, readyT, codeT, trace⟩ := Blocks.run_sites boundary
    (cloneLoadPrefix p index source length restore pointers lengths) code stride outside
    inside targets included s ready loaded sitePre
  exact ⟨n, t, run, readyT, codeT, cloneLoadPrefix_trace size distinct pre.rip trace⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxSize 256 in
set_option maxRecDepth 2048 in
theorem cloneShape_load [bindings : Bindings] {l : Table.Layout}
    (shape : CloneShape l) (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) (sp : BitVec 64) :
    AdvanceTriple boundary (Table.LoadPre l sp)
      ((l.load ++ l.cloneIn).flatMap Blocks.Site.code) (Table.LoadPost l sp) := by
  have data := shape.2.2.1
  unfold cloneData at data
  split at data
  · rename_i countSlot loadPC index source length pointers lengths tailPC tail tailAddress
      ci0 c0 v0 ci1 bsrc restore ci2 dst0 restore1 ci3 dst1 src1 ci4
      co0 index0 co1 c1 v1 co2 addrReg addrMode co3 dst2 src2 co4 dst3 restore2 co5 co6
      index1 countOffset co7 cc disp hcount hload hclone hcloneOut
    rcases of_decide_eq_true data with ⟨hi, hcountSlot, hbuffer, clobbers,
      hpointer, hlength, hstored, hsource, hlen, htail, haligned, hrestore, hbufsource,
      hbulk, distinct, hindex0, hindex1, hc0, hv0, hc1, hv1, hbsrc, hrestore1,
      hdst0, hdst1, hsrc1, haddr, ham, hdst2, hsrc2, hdst3, hrestore2, hcountoff, hcc,
      hloadPC, htailPC, pairSize, constSize, move3Size, move7Size, move6Size,
      incrSize, constOutSize, addrSize, moveOut1, moveOut2, compareSize, fall,
      entryEq, hci0, hci1, hci2, hci3, hci4, hco0, hco1, hco2, hco3, hco4,
      hco5, hco6, hco7, branchTargetEq, sitesCode, headCode, exitCode, branchCode,
      hpointers, hlengths, htailAddress, nextSmall, nextLarge⟩
    subst countSlot c0 v0 bsrc restore1 dst0 dst1 src1 loadPC tailPC ci0 ci1 ci2 ci3 ci4
      pointers lengths tailAddress
    intro s ready loaded pre
    have pairPre : Blocks.Pre l.head
        (.loadPair index source length (.d32 l.pointerSlot) (.d32 l.lengthSlot)) s := by
      apply loadPair_pre_of_table pre hi
      · simp [AddrMode.Valid]
      · simp [AddrMode.Valid]
      · have facts := distinct
        simp only [cloneRegisterData, Bool.and_eq_true, decide_eq_true_eq] at facts
        simp_all [AddrMode.Valid, regLow, List.pairwise_cons]
      · exact d32_value_ofNat _ (by rw [hpointer]; decide)
      · exact d32_value_ofNat _ (by rw [hlength]; decide)
      · have facts := distinct
        simp only [cloneRegisterData, Bool.and_eq_true, decide_eq_true_eq] at facts
        simp_all [List.pairwise_cons]
    have prefixMem : ∀ site ∈ cloneLoadPrefix l.head index source length restore
        (.d32 l.pointerSlot) (.d32 l.lengthSlot), site ∈ TraitTable.loadSitesOf l := by
      intro site member
      simp only [TraitTable.loadSitesOf, TraitTable.loadPrefixOf, TraitTable.loadCloneOf,
        TraitTable.loadTailOf, hload, hclone]
      simp only [cloneLoadPrefix, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp
    obtain ⟨n, u, runU, readyU, codeU, setup⟩ := cloneLoadPrefix_run boundary stride outside
      l.head index source length tail restore (.d32 l.pointerSlot) (.d32 l.lengthSlot)
      pairSize distinct _
      (fun site member => cloneShape_load_sites_inside shape site (prefixMem site member))
      (fun site member => cloneShape_load_code shape (prefixMem site member))
      s ready loaded pairPre
    have memoryU : u.external = s.external := setup.agrees.external (by
      simp [cloneLoadPrefixEffect, Effect.components, Component.Covers])
    have working : Blocks.readReg s restore = l.chunk.buffer sp :=
      pre.workingPointer restore (by simp [hrestore])
    have sourceU : rsi.read u = l.stored sp := by
      exact setup.writes.2.2.2.2.2.2.trans (pre.storedPointer shape.1)
    have targetU : rdi.read u = l.chunk.buffer sp :=
      setup.writes.2.2.2.2.2.1.trans working
    have countU : rcx.read u = 13 := setup.writes.2.2.2.1
    have countNat : (rcx.read u).toNat = 13 := by rw [countU]; decide
    have rspU : stackPtr u = sp := by
      have d := pairPre.distinct
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true,
        List.Pairwise.nil] at d
      rcases d with ⟨_, ⟨_, _, hs4⟩, ⟨_, hl4⟩, _⟩
      have hs4' : (4 : BitVec 5) ≠ source.setWidth 5 :=
        fun h => hs4 ((Blocks.widened_eq source 4).mp h.symm)
      have hl4' : (4 : BitVec 5) ≠ length.setWidth 5 :=
        fun h => hl4 ((Blocks.widened_eq length 4).mp h.symm)
      apply Eq.trans (setup.agrees.read (n := 64) (r := 4) ?_) pre.rsp
      simp [cloneLoadPrefixEffect, Effect.components]
      exact ⟨hs4', hl4'⟩
    have cloneMember : (⟨l.head + 38, .clone⟩ : Blocks.Site) ∈ TraitTable.loadSitesOf l := by
      simp [TraitTable.loadSitesOf, TraitTable.loadPrefixOf, TraitTable.loadCloneOf,
        TraitTable.loadTailOf, hload, hclone]
    have cloneOriginal : (⟨l.head + 38, .clone⟩ : Blocks.Site) ∈ l.load ++ l.cloneIn := by
      simp [hload, hclone]
    have clonePre : Blocks.Pre (l.head + 38) .clone u := by
      refine clone_load_clone_pre pre hbuffer hstored setup.rip memoryU ?_ sourceU targetU countU ?_
      · have flagsU : u.RFLAGS = s.RFLAGS := setup.agrees.rflags
          (by simp [cloneLoadPrefixEffect, Effect.components])
          (by simp [cloneLoadPrefixEffect, Effect.components])
        rw [flagsU]
        exact pre.direction.df
      · exact pre.codeApart _ cloneOriginal
    have cloneInside := cloneShape_load_sites_inside shape _ cloneMember
    change BlockInProgram (l.head + 38) 3 at cloneInside
    obtain ⟨runV, readyV, copy, copied⟩ := RepMovsq.rep_movsq_execution stride readyU
      (codeU.mono (cloneShape_load_code shape cloneMember)) clonePre.1 countNat
      (boundary_ne_program outside (by simpa using cloneInside 0 (by decide)))
      (boundary_ne_program outside (cloneInside 3 (by decide)))
    generalize hv : nextStates (max 13 1) u = v at runV readyV copy copied
    have avoidCopy : (repMovsqEffect (l.head + 38) u).Avoids
        ((l.load ++ l.cloneIn).flatMap Blocks.Site.code) := by
      intro x member
      obtain ⟨site, member, inSite⟩ := List.mem_flatMap.mp member
      apply Effect.avoids_codeRange (bytes := Blocks.bytes site.block) ?_ x inSite
      intro c hc a len ceq
      simp only [repMovsqEffect_components, targetU, countNat] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> try cases ceq
      exact pre.codeApart site member
    have codeV := copy.codeIn avoidCopy codeU
    have copyAgree : AgreesExcept
        [.reg 6, .reg 7, .reg 1, .mem (l.chunk.buffer sp) 104, .rip] u v := by
      simpa only [repMovsqEffect_components, targetU, countNat] using copy.agrees
    have rspV : stackPtr v = sp :=
      (copyAgree.read (n := 64) (r := 4) (by simp)).trans rspU
    have tailMember : (⟨l.head + 41, .loadTail tail (.sib 4 none 0 (.d8 63))⟩ : Blocks.Site)
        ∈ TraitTable.loadSitesOf l := by
      simp [TraitTable.loadSitesOf, TraitTable.loadPrefixOf, TraitTable.loadCloneOf,
        TraitTable.loadTailOf, hload, hclone]
    have tailAddressEq : (AddrMode.sib 4 none 0 (.d8 63)).addr v
        (l.head + 41 + BitVec.ofNat 64 (Blocks.bytes (.loadTail tail (.sib 4 none 0 (.d8 63)))).length)
        = l.chunk.buffer sp + 63 := by
      change stackPtr v + 63 = sp + BitVec.ofNat 64 l.chunk.bufferOffset + 63
      rw [hbuffer, rspV, BitVec.add_zero]
    have tailPre : Blocks.Pre (l.head + 41) (.loadTail tail (.sib 4 none 0 (.d8 63))) v := by
      refine ⟨?_, by simp [AddrMode.Valid], ?_⟩
      · simpa [repMovsqEffect, BitVec.add_assoc] using copy.rip
      · rw [tailAddressEq]
        exact Common.Memory.memReadable_sub
          ((MemReadable.of_holds copy (pre.active.toMemReadable.of_external_eq memoryU))) 63 1 (by decide)
    obtain ⟨m, t, runT, readyT, _, loadedTail⟩ := Blocks.run boundary (l.head + 41)
      (.loadTail tail (.sib 4 none 0 (.d8 63))) stride outside
      (cloneShape_load_sites_inside shape _ tailMember) (by trivial)
      v readyV (codeV.mono (cloneShape_load_code shape tailMember)) tailPre
    have tailAvoid : (Blocks.effect (l.head + 41) (.loadTail tail (.sib 4 none 0 (.d8 63))) v).Avoids
        ((l.load ++ l.cloneIn).flatMap Blocks.Site.code) :=
      Effect.Avoids.of_noMem (by simp [Blocks.effect, Effect.components, Component.Covers]) _
    refine ⟨n + max 13 1 + m, t, (runU.trans runV).trans runT, readyT,
      loadedTail.codeIn tailAvoid codeV, ?_⟩
    have memoryT : t.external = v.external := loadedTail.agrees.external (by
      simp [Blocks.effect, Effect.components, Component.Covers])
    have tailAgree : AgreesExcept [.reg (tail.setWidth 5), .rip] v t := by
      simpa [Blocks.effect, Effect.components] using loadedTail.agrees
    have setupAgree : AgreesExcept [.reg 0, .reg (source.setWidth 5),
        .reg (length.setWidth 5), .reg 1, .reg 3, .reg 7, .reg 6, .rip] s u := by
      simpa [cloneLoadPrefixEffect, Effect.components] using setup.agrees
    have whole := (setupAgree.trans copyAgree).trans tailAgree
    have regs := distinct
    simp only [cloneRegisterData, Bool.and_eq_true, decide_eq_true_eq] at regs
    have d1 := regs.1.1.map (S := fun a b : BitVec 5 => a ≠ b)
      (fun r => r.setWidth 5) (fun a b hab he => hab ((Blocks.widened_eq _ _).mp he))
    have d2 := regs.1.2.map (S := fun a b : BitVec 5 => a ≠ b)
      (fun r => r.setWidth 5) (fun a b hab he => hab ((Blocks.widened_eq _ _).mp he))
    simp only [List.map_cons, List.map_nil, BitVec.reduceSetWidth,
      List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true,
      List.Pairwise.nil] at d1 d2
    rcases d1 with ⟨⟨his, hil, hit, hi0, hi4⟩, ⟨hsl, hst, hs0, hs4⟩,
      ⟨hlt, hl0, hl4⟩, ⟨ht0, ht4⟩, _⟩
    rcases d2 with ⟨⟨_, _, _, hi1, hi2, hi3, hi6, hi7⟩,
      ⟨_, _, hs1, hs2, hs3, hs6, hs7⟩, ⟨_, hl1, hl2, hl3, hl6, hl7⟩,
      ⟨ht1, ht2, ht3, ht6, ht7⟩, _⟩
    have sourcePreserved : Blocks.readReg t source = Blocks.readReg u source :=
      (tailAgree.read (n := 64) (r := source.setWidth 5) (by simp [hst])).trans
        (copyAgree.read (n := 64) (r := source.setWidth 5) (by simp [hs1, hs6, hs7]))
    have lengthPreserved : Blocks.readReg t length = Blocks.readReg u length :=
      (tailAgree.read (n := 64) (r := length.setWidth 5) (by simp [hlt])).trans
        (copyAgree.read (n := 64) (r := length.setWidth 5) (by simp [hl1, hl6, hl7]))
    have bufferPreserved : Blocks.readReg t 3 = Blocks.readReg u 3 :=
      (tailAgree.read (n := 64) (r := 3) (by simp [Ne.symm ht3])).trans
        (copyAgree.read (n := 64) (r := 3) (by simp))
    have pointerValue := d32_value_ofNat l.pointerSlot (by rw [hpointer]; decide)
    have lengthValue := d32_value_ofNat l.lengthSlot (by rw [hlength]; decide)
    have finalBytes : ∀ i < 104, t.external[l.chunk.buffer sp + BitVec.ofNat 64 i]? =
        s.external[l.stored sp + BitVec.ofNat 64 i]? := by
      intro i bound
      rw [memoryT, ← targetU, ← sourceU, ← memoryU]
      exact copied i bound
    have agreements : AgreesExcept (l.chunk.clobbered.map Component.reg ++
        (l.chunk.bufferSource.toList.map fun r => Component.reg (r.setWidth 5)) ++
        [.mem (l.chunk.buffer sp) 104, .flags, .rip]) s t := by
      apply whole.mono
      intro c member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      simp only [List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq,
        and_true] at clobbers
      rcases clobbers with ⟨hc0, hc1, hc2, hc6, hc7, hcs, hcl, hct, hcr⟩
      rcases member with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
        (rfl | rfl | rfl | rfl | rfl)) | (rfl | rfl) <;>
        simp [hbufsource, hcs, hcl, hct]
      all_goals first | exact hc0 | exact hc1 | exact hc6 | exact hc7
    have rspS : rspOf s = sp := pre.rsp
    constructor
    · exact loadedTail.rip.trans entryEq.symm
    · exact (tailAgree.read (n := 64) (r := 4) (by simp [Ne.symm ht4])).trans rspV
    · rw [hsource, sourcePreserved]
      simpa only [cloneLoadPrefixEffect, pointerValue, rspS, hi, Blocks.readReg] using setup.writes.2.1
    · rw [hlen, lengthPreserved]
      simpa only [cloneLoadPrefixEffect, lengthValue, rspS, hi, Blocks.readReg] using setup.writes.2.2.1
    · rw [htail]
      have value := loadedTail.writes
      change Blocks.readReg t tail = (memLoad v.external
        ((AddrMode.sib 4 none 0 (.d8 63)).addr v _) 8).setWidth 64 at value
      rw [tailAddressEq] at value
      rw [value]
      apply congrArg (BitVec.setWidth 64)
      have bytes63 := copied 63 (by decide)
      rw [targetU, sourceU, memoryU] at bytes63
      simp only [memLoad_8]
      exact congrArg UInt8.toBitVec (memByte_congr bytes63)
    · exact finalBytes
    · intro r member
      simp only [hbufsource, Option.mem_some_iff] at member
      subst r
      exact bufferPreserved.trans (setup.writes.2.2.2.2.1.trans working)
    · rw [hcount]
      change memLoad t.external (sp + 104) 64 = memLoad s.external (sp + 104) 64
      apply memLoad_congr
      intro i bound
      apply memByte_congr
      apply agreements.byte
      intro c member covered
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with (⟨r, _, rfl⟩ | ⟨r, _, rfl⟩) | rfl | rfl | rfl
      all_goals try exact covered.elim
      obtain ⟨j, hj, equal⟩ := covered
      have low := pre.active.low
      simp only [Layout.buffer, hbuffer, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at equal low
      have values := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at values
      omega
    · rw [hi]
      exact whole.read (n := 64) (r := index.setWidth 5) (by
        simp [his, hil, hit, hi0, hi1, hi3, hi6, hi7])
    · exact agreements
    · apply agreements.memoryWriteFrame
      intro c member a covered
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with (⟨r, _, rfl⟩ | ⟨r, _, rfl⟩) | rfl | rfl | rfl
      all_goals try exact covered.elim
      obtain ⟨i, bound, rfl⟩ := covered
      refine ⟨⟨(l.chunk.buffer sp).toNat, 104⟩, by simp, ?_⟩
      have low := pre.active.low
      simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · intro r unclobbered unbuffer
      apply agreements.read
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
      intro member
      rcases member with (⟨x, hx, eq⟩ | ⟨x, hx, eq⟩) | eq
      · cases eq
        exact unclobbered hx
      · cases eq
        exact unbuffer x (by simpa using hx) rfl
      · simp at eq
  · contradiction

end Sha2.Proofs.Common.SHA256.Instances.Absorption
