import P256.Proofs.Signing.Core.Iteration.Output.Memory
import P256.Proofs.Signing.Core.Iteration.Choice
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Field.Operations.Select.TestAl
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Setcc.Generated.R8.Triple
import X86Proofs.Instructions.Add.Generated.R8.Triple
import X86Proofs.Instructions.Or.Generated.R8.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Common.Instructions.MovzxByte Common.Instructions.ByteOps.ByteOps
open Common.Field

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {r scalarS : Nat}

theorem y_arguments (pre : SignPre s boundary) (frame : Frame s t)
    (payload : Payload s t r scalarS) (rip : t.RIP = 0x10d48a) :
    ∃ u, Advances boundary 4 t u ∧ Frame s u ∧ Payload s u r scalarS ∧
      u.RIP = 0x10d4a0 ∧ u.regValue .rsi = frameBase s+136 ∧ u.regValue .rdi = frameBase s+528 ∧ AgreesExcept [.reg 5,.reg 7,.reg 6,.flags,.rip] t u := by
  obtain ⟨a,runa,readya,ea⟩ := (test_r32_r32_effect_step 0x10d48a 0xc0 rfl).advances (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd48a _ (by decide) (by decide +kernel))
    rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd48c (by decide)))
  have aga : AgreesExcept [.flags,.rip] t a := ea.agrees
  have fa := after_registers frame readya aga (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨b,runb,readyb,eb⟩ := (setcc_r8_rex_effect_step 0x10d48c 5 0x40 (by simp [RexPrefix]) 0xc5 rfl (condHolds 5 (StatusFlags.ofRFLAGS a.RFLAGS))).advances readya
    (programText_slice (programLoaded_codeIn fa.loaded) 0xd48c _ (by decide) (by decide +kernel))
    ⟨ea.rip,rfl⟩ (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd490 (by decide)))
  have agb : AgreesExcept [.reg 5,.rip] a b := eb.agrees
  have fb := after_registers fa readyb agb (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨c,runc,readyc,ec⟩ := (lea_r64_effect_step 0x10d490 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 528)) (by decide) rfl rfl).advances readyb
    (programText_slice (programLoaded_codeIn fb.loaded) 0xd490 _ (by decide) (by decide +kernel))
    eb.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd498 (by decide)))
  have agc : AgreesExcept [.reg 7,.rip] b c := ec.agrees
  have fc := after_registers fb readyc agc (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨d,rund,readyd,ed⟩ := (lea_r64_effect_step 0x10d498 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl).advances readyc
    (programText_slice (programLoaded_codeIn fc.loaded) 0xd498 _ (by decide) (by decide +kernel))
    ec.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4a0 (by decide)))
  have agd : AgreesExcept [.reg 6,.rip] c d := ed.agrees
  have fd := after_registers fc readyd agd (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  have agrees : AgreesExcept [.reg 5,.reg 7,.reg 6,.flags,.rip] t d := (((aga.trans agb).trans agc).trans agd).mono (by simp)
  refine ⟨d,(((runa.trans runb).trans runc).trans rund),fd,payload.after_registers agrees (by simp [Component.Covers])
    (by simp) (by simp) (by simp),ed.rip,?_⟩
  have di : c.regValue .rdi = stackPtr b+528 := ec.writes
  have si : d.regValue .rsi = stackPtr c+136 := ed.writes
  exact ⟨si.trans (congrArg (·+136) fc.rsp),
    (agd.read (n:=64) (r:=7) (by simp)).trans (di.trans (congrArg (·+528) fb.rsp)),agrees⟩

theorem choice_arguments (pre : SignPre s boundary) (frame : Frame s t)
    (payload : Payload s t r scalarS) (rip : t.RIP = 0x10d4a5) :
    ∃ u, Advances boundary 3 t u ∧ Frame s u ∧ Payload s u r scalarS ∧
      u.RIP = 0x10d4b2 ∧ AgreesExcept [.reg 0,.reg 7,.flags,.rip] t u := by
  obtain ⟨a,runa,readya,ea⟩ := (movzx_r32_m8_effect_step 0x10d4a5 0 (.sib 4 none 0 (.d32 528)) (by decide) rfl rfl).advances (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd4a5 _ (by decide) (by decide +kernel))
    ⟨rip,by change MemReadable t (stackPtr t+528) 1; rw [frame.rsp]; exact local_readable pre frame (by decide)⟩ (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4ad (by decide)))
  have aga : AgreesExcept [.reg 0,.rip] t a := ea.agrees
  have fa := after_registers frame readya aga (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨b,runb,readyb,eb⟩ := (and_al_imm8_effect_step 0x10d4ad 1).advances readya
    (programText_slice (programLoaded_codeIn fa.loaded) 0xd4ad _ (by decide) (by decide +kernel))
    ea.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4af (by decide)))
  have agb : AgreesExcept [.reg 0,.flags,.rip] a b := eb.agrees
  have fb := after_registers fa readyb agb (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨c,runc,readyc,ec⟩ := (movzx_r32_r8_effect_step 0x10d4af 0xf8 rfl (by decide)).advances readyb
    (programText_slice (programLoaded_codeIn fb.loaded) 0xd4af _ (by decide) (by decide +kernel))
    eb.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4b2 (by decide)))
  have agc : AgreesExcept [.reg 7,.rip] b c := ec.agrees
  have fc := after_registers fb readyc agc (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  have agrees : AgreesExcept [.reg 0,.reg 7,.flags,.rip] t c := ((aga.trans agb).trans agc).mono (by simp)
  refine ⟨c,((runa.trans runb).trans runc),fc,payload.after_registers agrees (by simp [Component.Covers])
    (by simp) (by simp) (by simp),ec.rip,?_⟩
  exact agrees

theorem recovery_byte (pre : SignPre s boundary) (frame : Frame s t)
    (payload : Payload s t r scalarS) (rip : t.RIP = 0x10d4b7) :
    ∃ u, Advances boundary 4 t u ∧ Frame s u ∧ Payload s u r scalarS ∧
      u.RIP = 0x10d4c2 ∧ AgreesExcept [.reg 0,.reg 5,.flags,.rip] t u := by
  obtain ⟨a,runa,readya,ea⟩ := (test_al_al_effect_step 0x10d4b7).advances (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd4b7 _ (by decide) (by decide +kernel))
    rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4b9 (by decide)))
  have aga : AgreesExcept [.flags,.rip] t a := ea.agrees
  have fa := after_registers frame readya aga (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨b,runb,readyb,eb⟩ := (setcc_r8_effect_step 0x10d4b9 5 0xc0 rfl (by decide) (condHolds 5 (StatusFlags.ofRFLAGS a.RFLAGS))).advances readya
    (programText_slice (programLoaded_codeIn fa.loaded) 0xd4b9 _ (by decide) (by decide +kernel))
    ⟨ea.rip,rfl⟩ (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4bc (by decide)))
  have agb : AgreesExcept [.reg 0,.rip] a b := eb.agrees
  have fb := after_registers fa readyb agb (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨c,runc,readyc,ec⟩ := (add_r8_r8_rex_effect_step 0x10d4bc 0x40 0xed (by simp [RexPrefix]) rfl).advances readyb
    (programText_slice (programLoaded_codeIn fb.loaded) 0xd4bc _ (by decide) (by decide +kernel))
    eb.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4bf (by decide)))
  have agc : AgreesExcept [.reg 5,.flags,.rip] b c := ec.agrees
  have fc := after_registers fb readyc agc (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨d,rund,readyd,ed⟩ := (or_r8_r8_rex_effect_step 0x10d4bf 0x40 0xc5 (by simp [RexPrefix]) rfl).advances readyc
    (programText_slice (programLoaded_codeIn fc.loaded) 0xd4bf _ (by decide) (by decide +kernel))
    ec.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4c2 (by decide)))
  have agd : AgreesExcept [.reg 5,.flags,.rip] c d := ed.agrees
  have fd := after_registers fc readyd agd (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  have agrees : AgreesExcept [.reg 0,.reg 5,.flags,.rip] t d := (((aga.trans agb).trans agc).trans agd).mono (by simp)
  refine ⟨d,(((runa.trans runb).trans runc).trans rund),fd,payload.after_registers agrees (by simp [Component.Covers])
    (by simp) (by simp) (by simp),ed.rip,?_⟩
  exact agrees

theorem recovery_choice (pre : SignPre s boundary) (frame : Frame s t)
    (payload : Payload s t r scalarS) (rip : t.RIP = 0x10d4b2) :
    ∃ u, Advances boundary 6 t u ∧ Frame s u ∧ Payload s u r scalarS ∧ u.RIP = 0x10d4b7 := by
  obtain ⟨u,run,fu,ipu,_,ag⟩ := choice_call pre frame 0xd4b2 0xbbb9
    (by decide) (by decide +kernel) (by decide) rip
  have memory : MemoryWriteFrame t u #v[ScalarFrame.workRegion s 4584] := by
    apply ag.memoryWriteFrame
    intro c hc a ha
    simp only [ScalarFrame.choiceClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> try exact ha.elim
    all_goals exact ⟨ScalarFrame.workRegion s 4584,by simp,
      ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha⟩
  have pu := payload.copy (fun i hi => output_of_stack_frame pre memory i (by omega)) (by
    intro reg hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ag.read (n:=64) (r:=12) (by simp [ScalarFrame.choiceClobbers])
    · exact ag.read (n:=64) (r:=3) (by simp [ScalarFrame.choiceClobbers])
    · exact ag.read (n:=64) (r:=15) (by simp [ScalarFrame.choiceClobbers]))
  exact ⟨u,run,fu,pu,ipu⟩

end P256.Proofs.Signing.Core.Iteration.Output
