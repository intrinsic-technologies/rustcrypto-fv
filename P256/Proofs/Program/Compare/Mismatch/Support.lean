import P256.Proofs.Program.Compare.Execution
import P256.Proofs.Program.Compare.Model
import P256.Proofs.Program.Compare.Instructions.CmpByte
import P256.Proofs.Program.Compare.Instructions.Movzx
import X86Proofs.Instructions.Branch.Triple

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def changes : List Component := [.reg 0, .reg 1, .reg 6, .reg 7, .reg 8, .flags, .rip]

structure Run [Bindings] (boundary : ReturnBoundary) (s t : RamState)
    (frameChanges : List Component := changes) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programSections.toCodeMap t
  frame : AgreesExcept frameChanges s t

theorem Run.stack [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {frameChanges : List Component} (h : Run boundary s t frameChanges)
    (hstack : .reg 4 ∉ frameChanges := by decide) : stackPtr t = stackPtr s :=
  h.frame.read (n := 64) hstack

theorem Run.boundary [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {frameChanges : List Component} (h : Run boundary s t frameChanges)
    (hb : RegisterBoundary boundary s) (hstack : .reg 4 ∉ frameChanges := by decide) :
    RegisterBoundary boundary t :=
  hb.of_stack_eq (h.stack hstack)

theorem Run.trans [Bindings] {boundary : ReturnBoundary} {s t u : RamState}
    {frameChanges : List Component} (h : Run boundary s t frameChanges)
    (h' : Run boundary t u frameChanges) : Run boundary s u frameChanges := by
  obtain ⟨n, hn⟩ := h.advances
  obtain ⟨m, hm⟩ := h'.advances
  refine ⟨⟨n + m, hn.trans hm⟩, h'.ready, h'.code, ?_⟩
  exact (h.frame.trans h'.frame).mono (by simp)

theorem Run.mono [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {before after : List Component} (h : Run boundary s t before)
    (hsub : ∀ c ∈ before, c ∈ after) : Run boundary s t after :=
  ⟨h.advances, h.ready, h.code, h.frame.mono hsub⟩

theorem run_step [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {pre : RamState → Prop} {code : CodeMap} {effect : RamState → Effect}
    (hStep : StepEffect pre code effect) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programSections.toCodeMap s) (hb : RegisterBoundary boundary s)
    (hp : pre s) (hcode : CodeIn code s)
    (hchanges : ∀ c ∈ (effect s).components, c ∈ changes)
    (hip : InRoutine (effect s).rip) :
    ∃ t, Run boundary s t ∧ (effect s).Holds s t := by
  obtain ⟨t, hs, ht, he⟩ := hStep s hr hcode hp
  have hf := he.agrees.mono hchanges
  have hsp : stackPtr t = stackPtr s := hf.read (n := 64) (by decide)
  refine ⟨t, ⟨⟨1, hb.advances hs hsp (he.rip ▸ hip)⟩, ht, ?_, hf⟩, he⟩
  exact hf.codeIn (by simp [changes, Component.Covers]) hc

theorem run_block [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {pre : RamState → Prop} {code : CodeMap} {effect : RamState → Effect}
    (hBlock : RegisterBlock pre code effect) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programSections.toCodeMap s) (hb : RegisterBoundary boundary s)
    (hp : pre s) (hcode : CodeIn code s)
    (hchanges : ∀ c ∈ (effect s).components, c ∈ changes) :
    ∃ t, Run boundary s t ∧ (effect s).Holds s t := by
  obtain ⟨fuel, t, hs, ht, _, he, _⟩ := hBlock boundary s hr hcode hp hb
  have hf := he.agrees.mono hchanges
  exact ⟨t, ⟨⟨fuel, hs⟩, ht, hf.codeIn (by simp [changes, Component.Covers]) hc, hf⟩, he⟩

def compareEffect (p : BitVec 64) (len width : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg dst : Operand width).read s)
      ((Operand.reg src : Operand width).read s))) }

theorem compare_branch [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (p : BitVec 64) (len width : Nat) (dst src : BitVec 5)
    (code : CodeMap) (cc : BitVec 4) (disp : BitVec 8)
    (hStep : StepEffect (fun s ↦ s.RIP = p) code (compareEffect p len width dst src))
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = p) (hcode : CodeIn code s)
    (hbranch : CodeIn (codeRange (p + BitVec.ofNat 64 len)
      (jccOpcode8 cc :: immBytes 8 disp)) s)
    (hcmp : InRoutine (p + BitVec.ofNat 64 len))
    (hnext : InRoutine (p + BitVec.ofNat 64 len + 2))
    (htarget : InRoutine (branchTarget (p + BitVec.ofNat 64 len) 2 (disp.signExtend 64))) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if condHolds cc
        (cmpSpec ((Operand.reg dst : Operand width).read s)
          ((Operand.reg src : Operand width).read s))
        then branchTarget (p + BitVec.ofNat 64 len) 2 (disp.signExtend 64)
        else p + BitVec.ofNat 64 len + 2 := by
  obtain ⟨u, hu, he⟩ := run_step hStep hr hc hb hp hcode
    (by simp [compareEffect, Effect.components, changes]) hcmp
  have hbu : CodeIn (codeRange (p + BitVec.ofNat 64 len)
      (jccOpcode8 cc :: immBytes 8 disp)) u :=
    he.codeIn (Effect.Avoids.of_noMem
      (by simp [compareEffect, Effect.components, Component.Covers]) _) hbranch
  obtain ⟨t, ht, hf⟩ := run_step
    (jcc_rel8_effect_step (p + BitVec.ofNat 64 len) cc disp)
    hu.ready hu.code (hu.boundary hb) ⟨he.rip, fun _ ↦ by have := htarget.2; omega⟩ hbu
    (by simp [jccEffect, changes])
    (by unfold jccEffect branchEffect; split <;> assumption)
  refine ⟨t, hu.trans ht, ?_, ?_⟩
  · exact (he.agrees.trans hf.agrees).mono
      (by simp [compareEffect, Effect.components, jccEffect, branchEffect])
  · rw [hf.rip]
    have hflags : StatusFlags.ofRFLAGS u.RFLAGS =
        cmpSpec ((Operand.reg dst : Operand width).read s)
          ((Operand.reg src : Operand width).read s) := by
      have flags_eq (a b : StatusFlags)
          (h : (StatusFlagsOutcome.ofStatusFlags b).Allows a) : a = b := by
        cases a
        cases b
        simpa only [StatusFlagsOutcome.Allows, StatusFlagsOutcome.ofStatusFlags,
          FlagAllows, StatusFlags.mk.injEq] using h
      exact flags_eq _ _ he.flags
    simp [jccEffect, branchEffect, hflags]

theorem cmp_zf {n : Nat} (x y : BitVec n) : (cmpSpec x y).ZF = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  simp [cmpSpec, subSpec, BitVec.sub_eq_iff_eq_add]

theorem register_setWidth (s : RamState) (r : BitVec 5) (n m : Nat) (h : m ≤ n) :
    ((Operand.reg r : Operand n).read s).setWidth m = (Operand.reg r : Operand m).read s := by
  simp [Operand.read, BitVec.setWidth_setWidth_of_le _ h]

end P256.Proofs.Program.Compare.Mismatch
