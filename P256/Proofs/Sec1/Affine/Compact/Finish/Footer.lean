import P256.Proofs.Sec1.Affine.Compressed.Finish.Footer
import P256.Proofs.Sec1.Affine.Uncompressed.Output.OutputMemory
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish.Footer

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open ScalarFrame P256.Proofs.Common.Instructions

def pc (last : Bool) : BitVec 64 := if last then 0x110d1e else 0x11060a

def size (last : Bool) : Nat := if last then 4 else 3

def offset (last : Bool) : Nat := if last then 72 else 64

def register (last : Bool) : Syntax.Reg := if last then .rbp else .rax

def code (last : Bool) : List UInt8 :=
  if last then [0x40,0x88,0x6b,0x48] else [0x88,0x43,0x40]

def effect (last : Bool) (s : RamState) : Effect :=
  { rip := pc last + BitVec.ofNat 64 (size last)
    writes := [⟨(.mem (s.regValue .rbx + BitVec.ofNat 64 (offset last)) : Operand 8),
      (s.regValue (register last)).setWidth 8⟩] }

theorem step [Bindings] (last : Bool) :
    StepEffect (StorePre (pc last) (size last)
      (fun s => s.regValue .rbx + BitVec.ofNat 64 (offset last)) 1)
      (codeRange (pc last) (code last)) (effect last) := by
  cases last
  · exact mov_m8_r8_legacy_effect_step 0x11060a 0 (by decide) (.base 3 (.d8 64))
      (by decide) rfl rfl
  · exact mov_m8_r8_effect_step 0x110d1e 0x40 (by simp [RexPrefix]) 5
      (.base 3 (.d8 72)) (by decide) rfl rfl

theorem store [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t) (last : Bool)
    (rip : t.RIP = pc last) (output : t.regValue .rbx = s.regValue .rdi) :
    ∃ u, Advances boundary 1 t u ∧ Frame s u ∧
      u.RIP = pc last+BitVec.ofNat 64 (size last) ∧
      memLoad u.external (s.regValue .rdi+BitVec.ofNat 64 (offset last)) 8 =
        (t.regValue (register last)).setWidth 8 ∧
      AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 (offset last)) 1,.rip] t u := by
  have codeBound : (pc last).toNat-0x100000+(code last).length ≤ 118431 := by cases last <;> decide
  have codeAddress : Extracted.textAddress+BitVec.ofNat 64 ((pc last).toNat-0x100000)=pc last := by
    cases last <;> decide
  have bytes := programText_slice (programLoaded_codeIn state.loaded)
    ((pc last).toNat-0x100000) (code last) codeBound (by cases last <;> decide +kernel)
  rw [codeAddress] at bytes
  have writable := (output_writable pre.toCalleePre (by decide) state.allocated).add
    (offset last) (len := 1) (by cases last <;> decide)
  obtain ⟨u,run,ready,value⟩ := (step last).advances
    (readyToStep state.machine state.bindingsSupported) bytes
    ⟨rip,by rw [output]; exact ⟨writable.low, writable.mem, writable.tables⟩,by
      rw [output]
      have length : (code last).length=size last := by cases last <;> rfl
      have h := P256.Proofs.Common.Instructions.RangeApart.add_left
        (output_code pre.toCalleePre (by simpa only [length] using codeBound))
        (offset last) (len := 1) (by cases last <;> decide)
      rwa [codeAddress] at h⟩
    (boundary_ne_program pre.outerBoundary (by
      cases last
      · exact inProgram_of_textOffset 0x1060d (by decide)
      · exact inProgram_of_textOffset 0x10d22 (by decide)))
  have agrees : AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 (offset last)) 1,.rip] t u := by
    have h := value.agrees
    simpa only [effect,Effect.components,List.map_cons,List.map_nil,Write.component,
      Operand.component,Nat.reduceDiv,List.append_nil,List.cons_append,List.nil_append,output] using h
  have frame := Uncompressed.Output.after_output pre state ready agrees (by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_,by simp,output_contains pre.toCalleePre (by cases last <;> decide) ha⟩
    · exact ha.elim) (by simp)
  exact ⟨u,run,frame,value.rip,by simpa only [effect,Write.AllHold,Operand.read,output] using value.writes,agrees⟩

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x11060a) (output : t.regValue .rbx = s.regValue .rdi) :
    ∃ u, Advances boundary 3 t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      (∀ i < 64, u.external[s.regValue .rdi+BitVec.ofNat 64 i]? =
        t.external[s.regValue .rdi+BitVec.ofNat 64 i]?) ∧
      memLoad u.external (s.regValue .rdi+64) 8 = (t.regValue .rax).setWidth 8 ∧
      memLoad u.external (s.regValue .rdi+72) 8 = (t.regValue .rbp).setWidth 8 := by
  obtain ⟨a,runA,frameA,ripA,flagA,agreesA⟩ := store pre state false rip output
  obtain ⟨b,runB,readyB,effectB⟩ := (jmp_rel32_effect_step 0x11060d 0x70c (by decide)).advances
    (readyToStep frameA.machine frameA.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameA.loaded) 0x1060d _ (by decide) (by decide +kernel))
    ripA (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10d1e (by decide)))
  have agreesB : AgreesExcept [.rip] a b := effectB.agrees
  have frameB := frameA.after_registers readyB agreesB (by simp [Component.Covers]) (by simp)
  have outputB : b.regValue .rbx=s.regValue .rdi :=
    ((agreesA.trans agreesB).read (n := 64) (r := 3) (by simp)).trans output
  obtain ⟨u,runU,frameU,ripU,validity,agreesU⟩ := store pre frameB true effectB.rip outputB
  have all := (agreesA.trans agreesB).trans agreesU
  refine ⟨u,(runA.trans runB).trans runU,frameU,ripU,?_,?_,?_⟩
  · intro i hi
    apply all.byte
    intro c hc covered
    simp only [offset,Bool.false_eq_true,ite_false,ite_true,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals
      obtain ⟨j,hj,he⟩ := covered
      have zero : j=0 := by omega
      subst j
      simp only [BitVec.add_zero,BitVec.add_right_inj] at he
      have h := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at h
      omega
  · have kept : u.external[s.regValue .rdi+64]? = b.external[s.regValue .rdi+64]? := by
      apply agreesU.byte
      intro c hc covered
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j,hj,he⟩ := covered
        have zero : j=0 := by omega
        subst j
        have : (72 : BitVec 64)=64 := by simpa only [offset,ite_true,BitVec.ofNat_eq_ofNat,
          BitVec.add_zero,BitVec.add_right_inj] using he.symm
        contradiction
      · exact covered.elim
    rw [memLoad_congr (fun i hi => by
      have zero : i=0 := by omega
      subst i
      exact memByte_congr (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using kept)),
      agreesB.external (by simp [Component.Covers])]
    exact flagA
  · exact validity.trans (congrArg (BitVec.setWidth 8)
      ((agreesA.trans agreesB).read (n := 64) (r := 5) (by simp)))

end P256.Proofs.Sec1.Affine.Compact.Finish.Footer
