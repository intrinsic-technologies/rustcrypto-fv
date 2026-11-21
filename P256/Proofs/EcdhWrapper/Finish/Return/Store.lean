import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.CrossPageStore
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem store [Bindings] {s : RamState} {boundary : ReturnBoundary} {address : BitVec 64}
    (outside : ¬ InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP=0x106cd5) (pointer : s.regValue .rcx=address) (count : s.regValue .rax=32)
    (writable : CrossPageStore.Writable s address 8)
    (apart : RangeApart address 8 0x106cd5 7) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ t.RIP=0x106cdc ∧
      t.regValue .rax=0 ∧ memLoad t.external address 64=32 ∧
      AgreesExcept [.reg 0,.reg 5,.flags,.mem address 8,.rip] s t := by
  have addr : storeAddrAt 0x106cd5 (.base 1 .none) 3 s=address := by
    change s.regValue .rcx+0=_
    simp only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,pointer]
  obtain ⟨a,ha,ra,ea⟩ := (CrossPageStore.mov_m64_r64_effect_step_any
    0x106cd5 0x48 (by simp [RexWPrefix]) 0 (.base 1 .none) (by decide) rfl rfl).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x6cd5 _ (by decide) (by decide +kernel))
    ⟨rip,by change CrossPageStore.Writable s (storeAddrAt _ _ 3 s) 8; rw [addr]; exact writable,
      by change RangeApart (storeAddrAt _ _ 3 s) 8 0x106cd5 3
         rw [addr]; exact fun i hi j hj ↦ apart i hi j (by omega)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6cd8 (by decide)))
  change (storeEffect (n := 64) 0x106cd5 3 (storeAddrAt 0x106cd5 (.base 1 .none) 3)
    (fun v ↦ (Operand.reg 0 : Operand 64).read v) s).Holds s a at ea
  have fa : AgreesExcept [.mem address 8,.rip] s a := by
    simpa only [storeEffect_components,Nat.reduceDiv,addr] using ea.agrees
  have codeA : CodeIn (codeRange 0x106cd8 [0x31,0xed,0x89,0xe8]) a := by
    apply (programText_slice (programLoaded_codeIn loaded) 0x6cd8 _
      (by decide) (by decide +kernel)).of_agreesExcept fa
    intro x hx c hc hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i,hi,hit⟩ := hv
      obtain ⟨j,hj,eq⟩ := exists_of_mem_codeRange hx
      exact apart i hi (3+j) (by change j<4 at hj; omega) (by simpa only [BitVec.ofNat_add,← BitVec.add_assoc,Extracted.textAddress,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using hit.symm.trans eq)
    · exact hv.elim
  have word : memLoad a.external address 64=32 := by
    have h := ea.writes
    change memLoad a.external (storeAddrAt 0x106cd5 (.base 1 .none) 3 s) 64=s.regValue .rax at h
    simpa only [addr,count] using h
  obtain ⟨b,hb,rb,eb⟩ := (xor_r32_r32_effect_step 0x106cd8 0xed (by decide)).advances ra
    (codeA.mono (codeRange_slice_subset 0x106cd8 [0x31,0xed,0x89,0xe8] 0 2)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6cda (by decide)))
  have fb : AgreesExcept [.reg 5,.flags,.rip] a b := eb.agrees
  have mb := fb.external (by simp [Component.Covers])
  have bp : b.regValue .rbp=0 := by
    have h := eb.writes
    change b.regValue .rbp=(((Operand.reg 5 : Operand 32).read a) ^^^
      ((Operand.reg 5 : Operand 32).read a)).setWidth 64 at h
    simpa only [BitVec.xor_self,BitVec.setWidth_zero,BitVec.ofNat_eq_ofNat] using h
  obtain ⟨t,ht,rt,et⟩ := (mov_r32_r32_effect_step 0x106cda 0xe8 (by decide)).advances rb
    ((codeA.of_external_eq mb).mono (codeRange_slice_subset 0x106cd8 [0x31,0xed,0x89,0xe8] 2 2)) eb.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6cdc (by decide)))
  have ft : AgreesExcept [.reg 0,.rip] b t := et.agrees
  refine ⟨t,(ha.trans hb).trans ht,rt,et.rip,?_,?_,((fa.trans fb).trans ft).mono (by simp)⟩
  · have h : t.regValue .rax=((b.regValue .rbp).setWidth 32).setWidth 64 := et.writes
    rw [h,bp]; rfl
  · rw [ft.external (by simp [Component.Covers]),mb]; exact word

end P256.Proofs.EcdhWrapper.Finish.Return
