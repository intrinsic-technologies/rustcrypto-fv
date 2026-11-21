import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.CopyCall
import Sha2.Proofs.Wrapper512.Finish.Copy
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableAdvance
import Sha2.Proofs.Wrapper512.Absorb.State

set_option autoImplicit false
namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Wrapper
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption

def counterOffset (v : Variant) (large : Bool) (form : Form := .slices) : Nat :=
  match form with
  | .traitFinalizeIntoReset second =>
    if large then (v.traversal form).exit - 24
    else (v.traversal form).head - (if second then 40 else 41)
  | _ => if large then (v.traversal form).exit - 28 else (v.traversal form).head - 12

def counterPC (v : Variant) (large : Bool) (form : Form := .slices) : BitVec 64 :=
  v.pc (counterOffset v large form) form

def counterBranchCC (large : Bool) : BitVec 4 := if large then 5 else 4

def counterBranchDisplacement (large : Bool) (v : Variant := .sha384)
    (form : Form := .slices) : BitVec 32 :=
  BitVec.ofNat 32 (if large then (v.traversal form).head else (v.traversal form).exit) -
    BitVec.ofNat 32 (counterOffset v large form + 12)

def counterSites (v : Variant) (large : Bool) (form : Form) : List Blocks.Site :=
  let p := counterPC v large form
  let i := BitVec.ofNat 4 (v.traversal form).indexReg
  let c := BitVec.ofNat 4 ((v.traversal form).countReg.getD 0)
  [⟨p, .incrementIndex i⟩, ⟨p+3, .compareIndex i c⟩,
    ⟨p+6, .branch (counterBranchCC large) (.near (counterBranchDisplacement large v form))⟩] ++
    if large then [⟨p+12, .jump (.short 14)⟩] else []

theorem counterSites_basic (v : Variant) (large : Bool) (form : Form) :
    ∀ site ∈ counterSites v large form, Blocks.Basic site.block := by
  cases large <;> simp [counterSites, Blocks.Basic]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem counterSites_bytes (v : Variant) (large : Bool) (form : Form)
    (nonDigest : form ≠ .digest) (register : (v.traversal form).countReg.isSome = true) :
    ∀ site ∈ counterSites v large form,
      site.pc.toNat - Extracted.textAddress.toNat + (Blocks.bytes site.block).length < 71757 ∧
      Extracted.textBytes.toListFrom (site.pc.toNat - Extracted.textAddress.toNat)
        (Blocks.bytes site.block).length = Blocks.bytes site.block ∧
      Extracted.textAddress + BitVec.ofNat 64 (site.pc.toNat - Extracted.textAddress.toNat) = site.pc := by
  revert nonDigest register
  cases form <;> cases v <;> cases large <;> decide +revert +kernel

def counterTargetGood (site : Blocks.Site) : Prop :=
  match site.block with
  | .branch _ disp | .jump disp =>
      (branchTarget site.pc (Blocks.bytes site.block).length disp.value).toNat -
        Extracted.textAddress.toNat < 71757 ∧
      Extracted.textAddress + BitVec.ofNat 64
        ((branchTarget site.pc (Blocks.bytes site.block).length disp.value).toNat -
          Extracted.textAddress.toNat) = branchTarget site.pc (Blocks.bytes site.block).length disp.value
  | _ => True

instance (site : Blocks.Site) : Decidable (counterTargetGood site) := by
  unfold counterTargetGood
  split <;> infer_instance

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem counterSites_targets (v : Variant) (large : Bool) (form : Form)
    (nonDigest : form ≠ .digest) (register : (v.traversal form).countReg.isSome = true) :
    ∀ site ∈ counterSites v large form, counterTargetGood site := by
  revert nonDigest register
  cases form <;> cases v <;> cases large <;> decide +revert +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem counterSites_shape (v : Variant) (form : Form)
    (nonDigest : form ≠ .digest) (register : (v.traversal form).countReg.isSome = true) :
    BitVec.ofNat 4 ((v.traversal form).countReg.getD 0) ≠
      BitVec.ofNat 4 (v.traversal form).indexReg ∧
    branchTarget (counterPC v false form + 6) 6
      ((counterBranchDisplacement false v form).signExtend 64) = v.pc (v.traversal form).exit form ∧
    counterPC v false form + 6 + 6 = v.pc (v.traversal form).head form ∧
    branchTarget (counterPC v true form + 6) 6
      ((counterBranchDisplacement true v form).signExtend 64) = v.pc (v.traversal form).head form ∧
    v.pc (v.traversal form).head form ≠ counterPC v true form + 12 ∧
    branchTarget (counterPC v true form + 12) 2 ((14 : BitVec 8).signExtend 64) =
      v.pc (v.traversal form).exit form := by
  revert nonDigest register
  cases form <;> cases v <;> decide +revert +kernel

 theorem run_counter [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    (state : State v initial s form) (large : Bool)
    (nonDigest : form ≠ .digest) (register : (v.traversal form).countReg.isSome = true)
    (rip : s.RIP = counterPC v large form) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      t.RIP = (if v.indexValue form s + 1 = v.countValue form initial s then
        v.pc (v.traversal form).exit form else v.pc (v.traversal form).head form) ∧
      v.indexValue form t = v.indexValue form s + 1 ∧
      AgreesExcept [.reg (BitVec.ofNat 5 (v.traversal form).indexReg), .flags, .rip] s t := by
  let sites := counterSites v large form
  let code := sites.flatMap Blocks.Site.code
  have loaded : CodeIn code s := by
    intro x hx
    obtain ⟨site, hs, hx⟩ := List.mem_flatMap.mp hx
    have facts := counterSites_bytes v large form nonDigest register site hs
    have h := programText_slice (programLoaded_codeIn state.loaded)
      (site.pc.toNat - Extracted.textAddress.toNat) (Blocks.bytes site.block)
      (by omega) facts.2.1
    rw [facts.2.2] at h
    exact h x hx
  have inside : ∀ site ∈ sites, BlockInProgram site.pc (Blocks.bytes site.block).length := by
    intro site hs
    have facts := counterSites_bytes v large form nonDigest register site hs
    rw [← facts.2.2]
    exact blockInProgram_of_textOffset _ _ facts.1
  have targets : ∀ site ∈ sites, match site.block with
      | .branch _ disp | .jump disp => InProgram (branchTarget site.pc (Blocks.bytes site.block).length disp.value)
      | _ => True := by
    intro site hs
    have facts := counterSites_targets v large form nonDigest register site hs
    unfold counterTargetGood at facts
    split <;> simp_all only <;> first | trivial | (rw [← facts.2]; exact inProgram_of_textOffset _ facts.1)
  obtain ⟨fuel,t,run,ready,_,trace⟩ := Blocks.run_sites (returnBoundary initial) sites code
    ctx.stride (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 inside targets
    (fun site hs x hx => List.mem_flatMap.mpr ⟨site,hs,hx⟩) s
    (supportedMachine_readyToStep state.machine) loaded
    (Blocks.SitePre.of_basic code sites (counterSites_basic v large form) s)
  have shape := counterSites_shape v form nonDigest register
  have regs : ∀ (v : Variant) (form : Form), (BitVec.ofNat 4 (v.traversal form).indexReg).setWidth 5 =
      BitVec.ofNat 5 (v.traversal form).indexReg ∧
      (BitVec.ofNat 4 ((v.traversal form).countReg.getD 0)).setWidth 5 =
      BitVec.ofNat 5 ((v.traversal form).countReg.getD 0) := by
    intro v form
    cases form <;> cases v <;> decide +revert +kernel
  have regs := regs v form
  have count : ∀ u, v.countValue form initial u =
      Blocks.readReg u (BitVec.ofNat 4 ((v.traversal form).countReg.getD 0)) := by
    intro u
    unfold Variant.countValue Blocks.readReg
    rw [regs.2]
    split <;> simp_all
  have idx : ∀ u, v.indexValue form u = Blocks.readReg u (BitVec.ofNat 4 (v.traversal form).indexReg) := by
    intro u
    unfold Variant.indexValue Blocks.readReg
    rw [regs.1]
  cases large
  · have trace' := advance_small_trace (disp := .near (counterBranchDisplacement false v form)) shape.1 rip rfl shape.2.1 shape.2.2.1 trace
    exact ⟨fuel,t,run,ready,by simpa only [idx,count] using trace'.1,by simpa only [idx] using trace'.2.1,by simpa only [regs.1] using trace'.2.2⟩
  · have trace' := advance_large_trace (disp := .near (counterBranchDisplacement true v form)) (jump := 14) shape.1 rip rfl shape.2.2.2.1 shape.2.2.2.2.1 shape.2.2.2.2.2 trace
    exact ⟨fuel,t,run,ready,by simpa only [idx,count] using trace'.1,by simpa only [idx] using trace'.2.1,by simpa only [regs.1] using trace'.2.2⟩


theorem advance_register_iteration [Bindings] {variant : Variant} {initial s : RamState}
    {inputs : Array Input} {index : Nat} {form : Form}
    (ctx : Context variant initial inputs form)
    (input : Buffered variant initial s (prefixMessage inputs (index+1)) form)
    (large : Bool) (rip : s.RIP = counterPC variant large form)
    (indexRegister : variant.indexValue form s = BitVec.ofNat 64 index)
    (countRegister : variant.countValue form initial s = BitVec.ofNat 64 inputs.size)
    (remaining : index < inputs.size)
    (nonDigest : form ≠ .digest := by decide)
    (register : (variant.traversal form).countReg.isSome = true := by decide)
    (bufferRegister : form = .reset 1 → s.regValue .rbx = bufferPointer initial form := by intro h; cases h)
    (memcpyTarget : match form with
      | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
      | .finalizeIntoReset true =>
        s.regValue (if variant = .sha384 ∨ variant = .sha512 then .rbx else .r12) = 0x10dd60
      | .traitFinalizeIntoReset second => s.regValue (if second then .rbp else .r13) = 0x10dd60
      | _ => True := by trivial) :
    ∃ t, (LoopState variant initial t inputs (index+1) form ∨
      (Buffered variant initial t (message inputs) form ∧
        t.RIP = variant.pc (variant.dispatchOffset form) form ∧
        variant.countValue form initial t = BitVec.ofNat 64 inputs.size ∧
        (form = .traitFinalizeIntoReset false →
          memLoad t.external (outputSavePointer initial form) 64 = initial.regValue .rcx))) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (variant.routine form).minStackBytes] := by
  have regFacts : ∀ (v : Variant) (f : Form),
      (v.traversal f).countReg.isSome = true →
      BitVec.ofNat 5 (v.traversal f).indexReg ≠ 4 ∧
      BitVec.ofNat 5 ((v.traversal f).countReg.getD 0) ≠
        BitVec.ofNat 5 (v.traversal f).indexReg ∧
      f ≠ .traitFinalizeIntoReset false := by
    intro v f
    cases f <;> cases v <;> decide +revert +kernel
  have facts := regFacts variant form register
  obtain ⟨fuel,t,run,ready,target,idx,frame⟩ := run_counter ctx input.toState large nonDigest register rip
  have current := buffered_of_agrees ctx input run ready frame
    (by simp [Component.Covers]) (by simpa using facts.1.symm)
    (by simp) (fun h => (nonDigest h).elim) (fun h => (facts.2.2 h).elim)
  have count : variant.countValue form initial t = variant.countValue form initial s := by
    unfold Variant.countValue
    split
    · rename_i reg hr
      apply frame.read
      have different := facts.2.1
      rw [hr] at different
      simpa using different
    · rename_i hr
      simp only [hr, Option.isSome_none, Bool.false_eq_true] at register
  have nextWord : BitVec.ofNat 64 index + 1 = BitVec.ofNat 64 (index+1) := by
    rw [BitVec.ofNat_add]
    rfl
  rw [indexRegister,nextWord] at idx target
  rw [countRegister] at target
  have wordEq : (BitVec.ofNat 64 (index+1) = BitVec.ofNat 64 inputs.size) ↔
      index+1 = inputs.size := by
    constructor
    · intro h
      have h := congrArg BitVec.toNat h
      have bound := ctx.count_bound
      simp only [BitVec.toNat_ofNat] at h
      rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at h
      exact h
    · intro h
      rw [h]
  simp only [wordEq] at target
  refine ⟨t, ?_, ⟨fuel,run⟩,
    frame.memoryWriteFrame (fun c hc a ha => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl <;> exact ha.elim)⟩
  by_cases last : index+1 = inputs.size
  · refine .inr ⟨?_, ?_, count.trans countRegister, fun h => (facts.2.2 h).elim⟩
    · simpa only [last,Wrapper.prefixMessage_size] using current
    · have exitEq : ∀ (v : Variant) (f : Form),
          (v.traversal f).exit = v.dispatchOffset f := by
        intro v f
        cases f <;> rfl
      simpa only [last,ite_true,exitEq] using target
  · have keepFacts : ∀ (v : Variant) (f : Form),
        BitVec.ofNat 5 (v.traversal f).indexReg ≠ 3 ∧
        BitVec.ofNat 5 (v.traversal f).indexReg ≠ 12 := by
      intro v f
      cases f <;> cases v <;> decide +revert +kernel
    have keep3 : t.regValue .rbx = s.regValue .rbx :=
      frame.read (n := 64) (r := 3) (by simpa using (keepFacts variant form).1.symm)
    have keep12 : t.regValue .r12 = s.regValue .r12 :=
      frame.read (n := 64) (r := 12) (by simpa using (keepFacts variant form).2.symm)
    have notTrait : ∀ second, form ≠ .traitFinalizeIntoReset second := by
      intro second eq
      subst form
      cases variant <;> cases second <;> contradiction
    refine .inl ⟨current,by simpa only [last,ite_false] using target,
      idx,count.trans countRegister,by omega,fun h => (facts.2.2 h).elim,
      fun h => keep3.trans (bufferRegister h),?_,fun b h => (notTrait b h).elim⟩
    cases form with
    | slices | digest => trivial
    | reset stage => exact fun h => keep3.trans (memcpyTarget h)
    | finalizeIntoReset second =>
      cases second
      · trivial
      · cases variant <;> first | exact keep3.trans memcpyTarget | exact keep12.trans memcpyTarget
    | traitFinalizeIntoReset second => exact (notTrait second rfl).elim



set_option maxRecDepth 2048 in
theorem trait_counter_bytes (v : Variant) (second : Bool) :
    let f := Form.traitFinalizeIntoReset second
    let offset := (v.traversal f).head - 11
    v.textOffset f + offset + 11 < 71757 ∧
    Extracted.textBytes.toListFrom (v.textOffset f + offset) 5 =
      Blocks.bytes (.compareIndexStack 15 (.d8 8)) ∧
    Extracted.textBytes.toListFrom (v.textOffset f + offset + 5) 6 =
      Blocks.bytes (.branch 4 (.near (BitVec.ofNat 32 ((v.traversal f).exit - (v.traversal f).head)))) ∧
    v.pc offset f + 5 + 6 = v.pc (v.traversal f).head f ∧
    branchTarget (v.pc offset f + 5) 6
      ((BitVec.ofNat 32 ((v.traversal f).exit - (v.traversal f).head)).signExtend 64) =
        v.pc (v.traversal f).exit f ∧
    v.textOffset f + (v.traversal f).exit < 71757 := by
  cases v <;> cases second <;> decide +kernel

theorem trait_counter_compare [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {second : Bool}
    (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (state : State v initial s (.traitFinalizeIntoReset second))
    (rip : s.RIP = v.pc ((v.traversal (.traitFinalizeIntoReset second)).head - 11)
      (.traitFinalizeIntoReset second))
    (readable : MemReadable s (rspOf s + 8) 8) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      t.RIP = (if memLoad s.external (rspOf s + 8) 64 = s.regValue .r15 then
        v.pc (v.traversal (.traitFinalizeIntoReset second)).exit (.traitFinalizeIntoReset second)
        else v.pc (v.traversal (.traitFinalizeIntoReset second)).head (.traitFinalizeIntoReset second)) ∧
      AgreesExcept [.flags,.rip] s t := by
  let f := Form.traitFinalizeIntoReset second
  let offset := (v.traversal f).head - 11
  let p := v.pc offset f
  let disp := BitVec.ofNat 32 ((v.traversal f).exit - (v.traversal f).head)
  have facts := trait_counter_bytes v second
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have code : CodeIn (codeRange p (Blocks.bytes (.compareIndexStack 15 (.d8 8)))) s :=
    programText_slice (programLoaded_codeIn state.loaded) (v.textOffset f + offset) _
      (by change v.textOffset f + offset + 5 ≤ 71757; have hb : v.textOffset f + offset + 11 < 71757 := facts.1; omega) facts.2.1
  have inside : BlockInProgram p 5 :=
    blockInProgram_of_textOffset _ _ (by have hb : v.textOffset f + offset + 11 < 71757 := facts.1; change v.textOffset f + offset + 5 < 71757; omega)
  obtain ⟨n,u,run,ready,_,cmp⟩ := Blocks.run (returnBoundary initial) p
    (.compareIndexStack 15 (.d8 8)) ctx.stride outside inside (by trivial) s
    (supportedMachine_readyToStep state.machine) code ⟨rip,by decide,readable⟩
  have frame : AgreesExcept [.flags,.rip] s u := cmp.agrees
  have loaded : ProgramLoaded u := by
    have memory : u.external = s.external := frame.external (by simp [Component.Covers])
    intro address byte h
    rw [memory]
    exact state.loaded address byte h
  have branchCode : CodeIn (codeRange (p+5) (Blocks.bytes (.branch 4 (.near disp)))) u := by
    have h := programText_slice (programLoaded_codeIn loaded) (v.textOffset f + offset + 5)
      (Blocks.bytes (.branch 4 (.near disp)))
      (by change v.textOffset f + offset + 5 + 6 ≤ 71757; have hb : v.textOffset f + offset + 11 < 71757 := facts.1; omega) facts.2.2.1
    simpa [p,Variant.pc,BitVec.ofNat_add,BitVec.add_assoc] using h
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (memLoad s.external (rspOf s + 8) 64 == s.regValue .r15) := by
    have h := cmp.flag .ZF
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (memLoad s.external (rspOf s + 8) 64 - s.regValue .r15 == 0) at h
    rw [h]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,BitVec.sub_eq_iff_eq_add]
    change (_ = (0 : BitVec 64) + _) ↔ _
    have hz : (0 : BitVec 64) + s.regValue .r15 = s.regValue .r15 := by
      exact BitVec.zero_add _
    rw [hz]
  have fall : p + 5 + (6 : BitVec 64) = v.pc (v.traversal f).head f := facts.2.2.2.1
  have taken : branchTarget (p+5) 6 (disp.signExtend 64) = v.pc (v.traversal f).exit f := facts.2.2.2.2.1
  have after : ∀ w, (jccEffect (p+5) 6 4 (disp.signExtend 64) u).Holds u w →
      w.RIP = (if memLoad s.external (rspOf s + 8) 64 = s.regValue .r15 then
        v.pc (v.traversal f).exit f else v.pc (v.traversal f).head f) := by
    intro w h
    have h := h.rip
    change w.RIP = (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then _ else _) at h
    rw [zero] at h
    by_cases he : memLoad s.external (rspOf s + 8) 64 = s.regValue .r15
    · have hb : (memLoad s.external (rspOf s + 8) 64 == s.regValue .r15) = true := beq_iff_eq.mpr he
      rw [hb] at h
      simp only [he,ite_true]
      exact h.trans taken
    · have hb : (memLoad s.external (rspOf s + 8) 64 == s.regValue .r15) = false := by
        simp only [beq_eq_false_iff_ne]; exact he
      rw [hb] at h
      simp only [he,ite_false]
      exact h.trans fall
  have nextInside : InProgram (jccEffect (p+5) 6 4 (disp.signExtend 64) u).rip := by
    change InProgram (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then _ else _)
    split
    · rw [taken]
      exact inProgram_of_textOffset _ facts.2.2.2.2.2
    · change InProgram (p + 5 + (6 : BitVec 64))
      rw [fall]
      exact inProgram_of_textOffset _ (by have hb : v.textOffset f + offset + 11 < 71757 := facts.1; change v.textOffset f + (v.traversal f).head < 71757; omega)
  obtain ⟨t,runB,readyB,branch⟩ := (jcc_rel32_effect_step (p+5) 4 disp).advances ready branchCode
    ⟨cmp.rip, by
      intro _
      rw [taken]
      cases v <;> cases second <;> decide +kernel⟩
    (boundary_ne_program outside nextInside)
  exact ⟨n+1,t,run.trans runB,readyB,after t branch,
    (frame.trans branch.agrees).mono (by simp [jccEffect,branchEffect,Effect.components])⟩


open Sha2.Proofs.Common.Instructions Sha2.Proofs.Common.Field
open Sha2.Proofs.Common.SHA256.Absorb.Blocks
attribute [local x86_compose] readReg

def traitSetupBytes (second : Bool) : List UInt8 :=
  encodeIncR64 15 ++ encodeMovR32Imm32 2 208 ++
    encodeLeaR64M (if second then 14 else 12) (.sib 4 none 0 (.d32 256)) ++
    encodeMovR64R64 7 (if second then 14 else 12) ++ encodeMovR64R64 6 3

def traitSetupEffect (p : BitVec 64) (second : Bool) (s : RamState) : Effect :=
  { rip := p + 22
    writes := [⟨(.reg 15 : Operand 64), readReg s 15 + 1⟩,
      ⟨(.reg 2 : Operand 64),208⟩,
      ⟨(.reg (if second then 14 else 12) : Operand 64),rspOf s + 256⟩,
      ⟨(.reg 7 : Operand 64),rspOf s + 256⟩,
      ⟨(.reg 6 : Operand 64),readReg s 3⟩]
    flags := (incR64Effect p 15 s).flags }

macro "trait_setup_steps " r:term : tactic => do
  let p := Lean.mkIdent `p
  let outside := Lean.mkIdent `outside
  let inside := Lean.mkIdent `inside
  `(tactic| (
    advance_reloc_begin (increment_step $p 15)
      next (boundary_ne_program $outside ($inside 3 (by omega)))
    try (case sub => exact codeRange_mem_of_take (by rfl))
    advance_reloc_then (constant_step ($p+3) 2 208)
      next (boundary_ne_program $outside ($inside 8 (by omega)))
    try (case sub => exact codeRange_mem_of_drop 3 (by rfl))
    advance_reloc_then (address_step ($p+8) $r (.sib 4 none 0 (.d32 256)) (by decide))
      next (boundary_ne_program $outside ($inside 16 (by omega)))
    try (case sub => exact codeRange_mem_of_drop 8 (by rfl))
    advance_reloc_then (move_step ($p+16) 7 $r)
      next (boundary_ne_program $outside ($inside 19 (by omega)))
    try (case sub => exact codeRange_mem_of_drop 16 (by rfl))
    advance_reloc_then (move_step ($p+19) 6 3)
      next (boundary_ne_program $outside ($inside 22 (by omega)))
    try (case sub => exact codeRange_mem_of_drop 19 (by rfl))
    advance_finish [traitSetupEffect,traitSetupBytes,encodeIncR64,
      encodeMovR32Imm32,encodeLeaR64M,encodeMovR64R64,incR64Effect]))

set_option maxHeartbeats 1000000 in
theorem trait_setup_run [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (second : Bool)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 22) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (traitSetupBytes second)) (Effect.post (traitSetupEffect p second)) := by
  cases second
  · trait_setup_steps 12
  · trait_setup_steps 14

set_option maxRecDepth 2048 in
theorem traitSetup_bytes (v : Variant) (second : Bool) :
    let f := Form.traitFinalizeIntoReset second
    let offset := (v.traversal f).head - (if second then 35 else 36)
    v.textOffset f + offset + 22 < 71757 ∧
    Extracted.textBytes.toListFrom (v.textOffset f + offset) 22 = traitSetupBytes second := by
  cases v <;> cases second <;> decide +kernel


def traitEntryBlock (v : Variant) (second large : Bool) : Blocks.Block :=
  if large then .jump (.near (BitVec.ofNat 32 ((v.traversal (.traitFinalizeIntoReset second)).head -
      (if second then 35 else 36)) -
    BitVec.ofNat 32 (counterOffset v true (.traitFinalizeIntoReset second) + 5)))
  else .address 3 (.sib 4 none 0 (.d8 32))

set_option maxRecDepth 2048 in
theorem traitEntry_facts (v : Variant) (second large : Bool) :
    let f := Form.traitFinalizeIntoReset second
    let offset := counterOffset v large f
    v.textOffset f + offset + 5 < 71757 ∧
    Extracted.textBytes.toListFrom (v.textOffset f + offset) 5 =
      Blocks.bytes (traitEntryBlock v second large) ∧
    (Blocks.bytes (traitEntryBlock v second large)).length = 5 ∧
    (if large then branchTarget (v.pc offset f) 5
      ((BitVec.ofNat 32 ((v.traversal f).head - (if second then 35 else 36)) -
        BitVec.ofNat 32 (offset+5)).signExtend 64) else v.pc offset f + 5) =
      v.pc ((v.traversal f).head - (if second then 35 else 36)) f ∧
    v.textOffset f + ((v.traversal f).head - (if second then 35 else 36)) < 71757 := by
  cases v <;> cases second <;> cases large <;> decide +kernel

theorem trait_counter_enter [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {second : Bool}
    (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (state : State v initial s (.traitFinalizeIntoReset second)) (large : Bool)
    (rip : s.RIP = counterPC v large (.traitFinalizeIntoReset second))
    (buffer : large = true → s.regValue .rbx = rspOf s + 32) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      t.RIP = v.pc ((v.traversal (.traitFinalizeIntoReset second)).head -
        (if second then 35 else 36)) (.traitFinalizeIntoReset second) ∧
      t.regValue .rbx = rspOf s + 32 ∧ AgreesExcept [.reg 3,.rip] s t := by
  let f := Form.traitFinalizeIntoReset second
  have facts := traitEntry_facts v second large
  have code : CodeIn (codeRange (counterPC v large f) (Blocks.bytes (traitEntryBlock v second large))) s :=
    programText_slice (programLoaded_codeIn state.loaded) (v.textOffset f + counterOffset v large f) _
      (by rw [facts.2.2.1]; exact Nat.le_of_lt facts.1)
      (by rw [facts.2.2.1]; exact facts.2.1)
  have inside : BlockInProgram (counterPC v large f) (Blocks.bytes (traitEntryBlock v second large)).length := by
    rw [facts.2.2.1]
    exact blockInProgram_of_textOffset _ _ facts.1
  have targets : match traitEntryBlock v second large with
    | .branch _ disp | .jump disp => InProgram (branchTarget (counterPC v large f)
        (Blocks.bytes (traitEntryBlock v second large)).length disp.value)
    | _ => True := by
    cases large
    · trivial
    · change InProgram (branchTarget (counterPC v true f) 5 _)
      have h : branchTarget (counterPC v true f) 5
          ((BitVec.ofNat 32 ((v.traversal f).head - (if second then 35 else 36)) -
            BitVec.ofNat 32 (counterOffset v true f+5)).signExtend 64) =
          v.pc ((v.traversal f).head - (if second then 35 else 36)) f := facts.2.2.2.1
      exact (congrArg InProgram h).mpr (inProgram_of_textOffset _ facts.2.2.2.2)
  have pre : Blocks.Pre (counterPC v large f) (traitEntryBlock v second large) s := by
    cases large
    · exact ⟨rip,by decide⟩
    · exact rip
  obtain ⟨n,t,run,ready,_,effect⟩ := Blocks.run (returnBoundary initial) (counterPC v large f)
    (traitEntryBlock v second large) ctx.stride
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 inside (by cases large <;> exact targets) s
    (supportedMachine_readyToStep state.machine) code pre
  refine ⟨n,t,run,ready,?_,?_,?_⟩
  · cases large <;> exact effect.rip.trans facts.2.2.2.1
  · cases large
    · exact effect.writes
    · exact (effect.agrees.read (n := 64) (r := 3) (by simp [traitEntryBlock,Blocks.effect,jmpEffect,Effect.components])).trans (buffer rfl)
  · cases large
    · exact effect.agrees
    · exact effect.agrees.mono (by simp [traitEntryBlock,Blocks.effect,jmpEffect,Effect.components])


def traitCopySite (v : Variant) (second : Bool) : Common.SHA256.Absorb.CallSite :=
  ⟨v.pc ((v.traversal (.traitFinalizeIntoReset second)).head - (if second then 13 else 14))
    (.traitFinalizeIntoReset second), .register (if second then 5 else 13)⟩

set_option maxRecDepth 2048 in
theorem traitCopy_facts (v : Variant) (second : Bool) :
    let f := Form.traitFinalizeIntoReset second
    let offset := (v.traversal f).head - (if second then 13 else 14)
    v.textOffset f + offset + (traitCopySite v second).encoding.bytes.length < 71757 ∧
    Extracted.textBytes.toListFrom (v.textOffset f + offset)
      (traitCopySite v second).encoding.bytes.length = (traitCopySite v second).encoding.bytes ∧
    (traitCopySite v second).pc + BitVec.ofNat 64 (traitCopySite v second).encoding.bytes.length =
      v.pc ((v.traversal f).head-11) f ∧
    v.textOffset f + ((v.traversal f).head-11) < 71757 := by
  cases v <;> cases second <;> decide +kernel

def traitCopyLayout (second : Bool) :
    Wrapper.StackCallLayout (Form.traitFinalizeIntoReset second).stackBytes 208 208 0 :=
  ⟨656,616,392,by decide,by change 656 ≤ 1200; decide,by decide,by decide,by decide,by decide,by decide⟩

set_option maxRecDepth 2048 in
theorem trait_copy [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {second : Bool} {message : ByteArray}
    (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (input : Buffered v initial s message (.traitFinalizeIntoReset second)
      (Form.traitFinalizeIntoReset second).activeMemory)
    (rip : s.RIP = (traitCopySite v second).pc)
    (callable : s.regValue (if second then .rbp else .r13) = 0x10dd60)
    (destination : s.regValue .rdi = stackPtr initial - 392)
    (source : s.regValue .rsi = stackPtr initial - 616)
    (length : s.regValue .rdx = 208) :
    ∃ t, Finish.Copy.StackResult v initial s t 208 616 392
        (v.pc ((v.traversal (.traitFinalizeIntoReset second)).head-11)
          (.traitFinalizeIntoReset second)) (.traitFinalizeIntoReset second) ∧
      Buffered v initial t message (.traitFinalizeIntoReset second) := by
  let f := Form.traitFinalizeIntoReset second
  let site := traitCopySite v second
  have facts := traitCopy_facts v second
  have address : pushAddr s = stackPtr initial - 656 := by
    rw [pushAddr,input.rsp,BitVec.sub_sub]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [address]
    exact Machine.Stages.stack_slot_writable ctx input.toState (by change 656 ≤ 1200; decide) (by decide)
  have apart : RangeApart (pushAddr s) 8 site.pc site.encoding.bytes.length := by
    rw [address]
    exact Machine.Stages.stack_slot_codeApart ctx (by change 656 ≤ 1200; decide) (by decide)
      (Nat.le_of_lt facts.1)
  have code : CodeIn (codeRange site.pc site.encoding.bytes) s :=
    programText_slice (programLoaded_codeIn input.loaded) _ _ (Nat.le_of_lt facts.1) facts.2.1
  obtain ⟨u,run,ready,effect⟩ := Common.SHA256.Absorb.CopyCall.enter site (returnBoundary initial)
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    (supportedMachine_readyToStep input.machine) code ⟨rip,writable,apart⟩
    (by cases second <;> exact callable)
  obtain ⟨stateU,rspU,returnU⟩ := ReturnState.of_call ctx input.toState run ready effect input.rsp
  have frame : AgreesExcept [.reg 4,.mem (stackPtr initial-656) 8,.rip] s u := by
    simpa only [callEffect,pushEffect_components,address] using effect.agrees
  have returned : InProgram (returnBoundary u).rip := by
    rw [returnU,facts.2.2.1]
    exact inProgram_of_textOffset _ facts.2.2.2
  obtain ⟨t,result⟩ := Finish.Copy.copy_at ctx input.toState stateU (traitCopyLayout second) rfl
    (by change 256 ≤ 392; decide) (by change 392 ≤ 648; decide) (by decide)
    (by change OffsetsApart (-656) 8 (-616) 208; unfold OffsetsApart; decide +kernel)
    frame effect.rip rspU (returnU.trans facts.2.2.1) returned destination source length ⟨1,run⟩
  have preserved := result.preserved_trait ctx input.toPreserved (Or.inl rfl)
  refine ⟨t,result,?_⟩
  exact result.buffered rfl rfl (by change 200 ≤ 616; decide) (by change 200 ≤ 392; decide) input preserved


def traitPrepareComponents (second : Bool) : List Component :=
  [.reg 3,.reg 15,.reg 2,.reg (if second then 14 else 12),.reg 7,.reg 6,.flags,.rip]

set_option maxRecDepth 2048 in
theorem trait_counter_prepare [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {second : Bool} {message : ByteArray}
    (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (input : Buffered v initial s message (.traitFinalizeIntoReset second)
      (Form.traitFinalizeIntoReset second).activeMemory)
    (large : Bool) (rip : s.RIP = counterPC v large (.traitFinalizeIntoReset second))
    (buffer : large = true → s.regValue .rbx = rspOf s + 32) :
    ∃ t, Buffered v initial t message (.traitFinalizeIntoReset second)
        (Form.traitFinalizeIntoReset second).activeMemory ∧
      t.RIP = (traitCopySite v second).pc ∧
      t.regValue .rdi = stackPtr initial-392 ∧
      t.regValue .rsi = stackPtr initial-616 ∧ t.regValue .rdx = 208 ∧
      t.regValue .r15 = s.regValue .r15 + 1 ∧
      t.regValue (if second then .r14 else .r12) = stackPtr initial-392 ∧
      t.regValue .rbx = stackPtr initial-616 ∧
      AgreesExcept (traitPrepareComponents second) s t ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) := by
  let f := Form.traitFinalizeIntoReset second
  let offset := (v.traversal f).head - (if second then 35 else 36)
  let p := v.pc offset f
  obtain ⟨n,u,run,ready,atInc,bufferU,frame⟩ := trait_counter_enter ctx input.toState large rip buffer
  have inputU := buffered_of_agrees ctx input run ready frame
    (by simp [Component.Covers]) (by simp) (by simp) (by intro h; cases h)
    (by intro _; left; cases v <;> simp)
  have facts := traitSetup_bytes v second
  have setupLength : (traitSetupBytes second).length = 22 := by cases second <;> decide
  have code : CodeIn (codeRange p (traitSetupBytes second)) u :=
    programText_slice (programLoaded_codeIn inputU.loaded) (v.textOffset f + offset) _
      (by rw [setupLength]; exact Nat.le_of_lt facts.1)
      (by rw [setupLength]; exact facts.2)
  obtain ⟨fuel,t,setupRun,setupReady,_,setup⟩ := trait_setup_run (returnBoundary initial) p second
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    (blockInProgram_of_textOffset _ _ facts.1) u ready code atInc
  have setupFrame : AgreesExcept [.reg 15,.reg 2,.reg (if second then 14 else 12),.reg 7,.reg 6,.flags,.rip] u t := by
    cases second <;> exact setup.agrees
  have output := buffered_of_agrees ctx inputU setupRun setupReady setupFrame
    (by cases second <;> simp [Component.Covers])
    (by cases second <;> simp) (by cases second <;> simp) (by intro h; cases h)
    (by intro _; left; cases v <;> cases second <;> simp)
  have rspS : rspOf s = stackPtr initial - 648 := input.rsp
  have rspU : rspOf u = stackPtr initial - 648 := inputU.rsp
  have dest : rspOf u + 256 = stackPtr initial-392 := by rw [rspU]; bv_omega
  have src : u.regValue .rbx = stackPtr initial-616 := by rw [bufferU,rspS]; bv_omega
  have indexU : u.regValue .r15 = s.regValue .r15 := frame.read (n := 64) (r := 15) (by simp)
  have writes : t.regValue .r15 = u.regValue .r15 + 1 ∧
    t.regValue .rdx = 208 ∧
    t.regValue (if second then .r14 else .r12) = rspOf u + 256 ∧
    t.regValue .rdi = rspOf u + 256 ∧ t.regValue .rsi = u.regValue .rbx := by
    cases second <;> (
      have h := setup.writes
      simp only [traitSetupEffect,Write.AllHold] at h
      exact h)

  refine ⟨t,output,?_,writes.2.2.2.1.trans dest,writes.2.2.2.2.trans src,
    writes.2.1,by rw [writes.1,indexU],writes.2.2.1.trans dest,?_,?_,⟨n+fuel,run.trans setupRun⟩⟩
  · have pc : p + 22 = (traitCopySite v second).pc := by
      cases v <;> cases second <;> decide +kernel
    exact setup.rip.trans pc
  · exact (setupFrame.read (n := 64) (r := 3) (by cases second <;> simp)).trans src
  · exact (frame.trans setupFrame).mono (by cases second <;> simp [traitPrepareComponents])


set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem advance_trait_iteration [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {index : Nat} {second : Bool}
    (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (input : Buffered v initial s (prefixMessage inputs (index+1)) (.traitFinalizeIntoReset second)
      (Form.traitFinalizeIntoReset second).activeMemory)
    (large : Bool) (rip : s.RIP = counterPC v large (.traitFinalizeIntoReset second))
    (indexRegister : s.regValue .r15 = BitVec.ofNat 64 index)
    (countRegister : memLoad s.external (stackPtr initial-640) 64 = BitVec.ofNat 64 inputs.size)
    (remaining : index < inputs.size)
    (buffer : large = true → s.regValue .rbx = rspOf s + 32)
    (callable : s.regValue (if second then .rbp else .r13) = 0x10dd60)
    (saved : second = false → memLoad s.external (stackPtr initial-408) 64 = initial.regValue .rcx) :
    ∃ t, (LoopState v initial t inputs (index+1) (.traitFinalizeIntoReset second) ∨
      (Buffered v initial t (message inputs) (.traitFinalizeIntoReset second) ∧
        t.RIP = v.pc (v.dispatchOffset (.traitFinalizeIntoReset second)) (.traitFinalizeIntoReset second) ∧
        v.countValue (.traitFinalizeIntoReset second) initial t = BitVec.ofNat 64 inputs.size ∧
        (Form.traitFinalizeIntoReset second = .traitFinalizeIntoReset false →
          memLoad t.external (outputSavePointer initial (.traitFinalizeIntoReset second)) 64 = initial.regValue .rcx))) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine (.traitFinalizeIntoReset second)).minStackBytes] := by
  let f := Form.traitFinalizeIntoReset second
  obtain ⟨u,inputU,atCall,destination,source,len,idxU,cloneU,bufferU,frame,prepExecution⟩ :=
    trait_counter_prepare ctx input large rip buffer
  have callableU : u.regValue (if second then .rbp else .r13) = 0x10dd60 := by
    refine Eq.trans ?_ callable
    cases second
    · exact frame.read (n := 64) (r := 13) (by simp [traitPrepareComponents])
    · exact frame.read (n := 64) (r := 5) (by simp [traitPrepareComponents])
  obtain ⟨w,result,inputW⟩ := trait_copy ctx inputU atCall callableU destination source len
  have memoryU : u.external = s.external := frame.external (by cases second <;> simp [traitPrepareComponents,Component.Covers])
  have slots (offset : Nat) (bound : offset ≤ 648) (lower : 8 ≤ offset)
      (apart : 400 ≤ offset ∨ offset+208 ≤ 392) :
      memLoad w.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
    rw [← memoryU]
    apply memLoad_congr
    intro j hj
    exact congrArg (fun x : Option UInt8 => x.getD 0)
      (result.kept_bytes ctx (by change 392 ≤ 648; decide) (by decide) bound lower apart j hj)
  have rspW : rspOf w + 8 = stackPtr initial-640 := by
    change stackPtr w + 8 = _
    rw [inputW.rsp]
    change stackPtr initial - 648 + 8 = _
    bv_omega
  have readable : MemReadable w (rspOf w+8) 8 := by
    rw [rspW]
    have hr := Dispatch.stack_sub_readable512 ctx (offset := 640) (len := 8)
      (by change 640 ≤ 1200; decide) (by decide)
    exact ⟨hr.low,fun j hj => inputW.allocated _ (hr.mem j hj)⟩
  obtain ⟨fuel,t,run,ready,target,compareFrame⟩ := trait_counter_compare ctx inputW.toState result.rip readable
  have current := buffered_of_agrees ctx inputW run ready compareFrame
    (by simp [Component.Covers]) (by simp)
  have memoryT : t.external = w.external := compareFrame.external (by simp [Component.Covers])
  have keep (r : Syntax.Reg) : t.regValue r = w.regValue r := by
    have h := compareFrame.read (n := 64) (r := BitVec.ofNat 5 r.fin.val) (by simp)
    cases r <;> exact h
  have keepABI (r : Syntax.Reg) (hr : r ∈ [.rbx,.rbp,.r12,.r13,.r14,.r15]) :
      t.regValue r = u.regValue r := (keep r).trans (result.abi.1 r hr)
  have indexW : w.regValue .r15 = BitVec.ofNat 64 (index+1) := by
    rw [result.abi.1 .r15 (by simp),idxU,indexRegister,BitVec.ofNat_add]
    rfl
  have countW : memLoad w.external (rspOf w+8) 64 = BitVec.ofNat 64 inputs.size := by
    rw [rspW]
    exact (slots 640 (by decide) (by decide) (Or.inl (by decide))).trans countRegister
  rw [countW,indexW] at target
  have wordEq : (BitVec.ofNat 64 inputs.size = BitVec.ofNat 64 (index+1)) ↔ inputs.size = index+1 := by
    constructor
    · intro eq
      have h := congrArg BitVec.toNat eq
      have bound := ctx.count_bound
      simp only [BitVec.toNat_ofNat] at h
      rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at h
      exact h
    · intro eq; rw [eq]
  simp only [wordEq] at target
  have countT : v.countValue (.traitFinalizeIntoReset second) initial t = BitVec.ofNat 64 inputs.size := by
    have h : memLoad t.external (stackPtr initial-640) 64 = BitVec.ofNat 64 inputs.size := by
      rw [memoryT]
      exact (slots 640 (by decide) (by decide) (Or.inl (by decide))).trans countRegister
    cases v <;> cases second <;> exact h
  have savedT : Form.traitFinalizeIntoReset second = .traitFinalizeIntoReset false →
      memLoad t.external (outputSavePointer initial (.traitFinalizeIntoReset second)) 64 = initial.regValue .rcx := by
    intro eq
    have he : second = false := Form.traitFinalizeIntoReset.inj eq
    subst second
    change memLoad t.external (stackPtr initial-408) 64 = _
    rw [memoryT]
    exact (slots 408 (by decide) (by decide) (Or.inl (by decide))).trans (saved rfl)
  obtain ⟨prepFuel,prepRun⟩ := prepExecution
  obtain ⟨copyFuel,copyRun⟩ := result.execution
  have localFrame : MemoryWriteFrame s t
      #v[Stack.region initial (v.routine (.traitFinalizeIntoReset second)).minStackBytes] := by
    intro a ha
    rw [memoryT, result.stackFrame a ha, memoryU]
  refine ⟨t, ?_, ⟨prepFuel+copyFuel+fuel,(prepRun.trans copyRun).trans run⟩, localFrame⟩
  by_cases last : inputs.size = index+1
  · refine .inr ⟨?_,?_,countT,savedT⟩
    · simpa only [← last,prefixMessage_size] using current
    · simpa [last,Variant.traversal,Variant.dispatchOffset] using target
  · refine .inl ⟨current,by simpa only [last,ite_false] using target,?_,?_,by omega,?_,?_,?_,?_⟩
    · have h := (keep .r15).trans indexW
      cases v <;> cases second <;> exact h
    · exact countT
    · exact savedT
    · intro eq; cases eq
    · exact (keepABI _ (by cases second <;> simp)).trans callableU
    · intro b eq
      have he : second = b := Form.traitFinalizeIntoReset.inj eq
      subst b
      constructor
      · exact (keepABI .rbx (by simp)).trans bufferU
      · exact (keepABI _ (by cases second <;> simp)).trans cloneU


theorem advance_iteration [Bindings] {variant : Variant} {initial s : RamState}
    {inputs : Array Input} {index : Nat} {form : Form}
    (ctx : Context variant initial inputs form)
    (input : Buffered variant initial s (prefixMessage inputs (index+1)) form form.activeMemory)
    (large : Bool) (rip : s.RIP = counterPC variant large form)
    (indexRegister : variant.indexValue form s = BitVec.ofNat 64 index)
    (countRegister : variant.countValue form initial s = BitVec.ofNat 64 inputs.size)
    (remaining : index < inputs.size)
    (nonDigest : form ≠ .digest := by decide)
    (bufferRegister : form = .reset 1 → s.regValue .rbx = bufferPointer initial form := by intro h; cases h)
    (memcpyTarget : match form with
      | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
      | .finalizeIntoReset true =>
        s.regValue (if variant = .sha384 ∨ variant = .sha512 then .rbx else .r12) = 0x10dd60
      | .traitFinalizeIntoReset second => s.regValue (if second then .rbp else .r13) = 0x10dd60
      | _ => True := by trivial)
    (traitBuffer : ∀ second, form = .traitFinalizeIntoReset second →
      large = true → s.regValue .rbx = rspOf s + 32 := by intro b h; cases h)
    (outputSaved : form = .traitFinalizeIntoReset false →
      memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx := by intro h; cases h) :
    ∃ t, (LoopState variant initial t inputs (index+1) form ∨
      (Buffered variant initial t (message inputs) form ∧
        t.RIP = variant.pc (variant.dispatchOffset form) form ∧
        variant.countValue form initial t = BitVec.ofNat 64 inputs.size ∧
        (form = .traitFinalizeIntoReset false →
          memLoad t.external (outputSavePointer initial form) 64 = initial.regValue .rcx))) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (variant.routine form).minStackBytes] := by
  cases form with
  | slices =>
    exact advance_register_iteration ctx input large rip indexRegister countRegister remaining
      nonDigest rfl bufferRegister memcpyTarget
  | digest => exact (nonDigest rfl).elim
  | reset stage =>
    exact advance_register_iteration ctx input large rip indexRegister countRegister remaining
      nonDigest (by
        have facts : ∀ (v : Variant) (stage : Fin 3), (v.traversal (.reset stage)).countReg.isSome = true := by
          intro v stage
          cases v <;> decide +revert +kernel
        exact facts variant stage) bufferRegister memcpyTarget
  | finalizeIntoReset second =>
    exact advance_register_iteration ctx input large rip indexRegister countRegister remaining
      nonDigest (by cases variant <;> cases second <;> rfl) bufferRegister memcpyTarget
  | traitFinalizeIntoReset second =>
    apply advance_trait_iteration ctx input large rip
    · cases variant <;> cases second <;> exact indexRegister
    · cases variant <;> cases second <;> exact countRegister
    · exact remaining
    · exact traitBuffer second rfl
    · exact memcpyTarget
    · intro h
      subst second
      exact outputSaved rfl

end Sha2.Proofs.Wrapper512.Absorb
