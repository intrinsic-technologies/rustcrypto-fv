import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Memory
import P256.Proofs.Common.Instructions.Neg64
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftCount.Triple
import P256.Proofs.Common.Instructions.ByteLogic.XorImmediate
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

open P256.Proofs.Common.Instructions.Neg64
open P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftCount
open P256.Proofs.Common.Encoding.Parser.ResultTag (xorR8Imm8Effect)
open P256.Proofs.Common.Instructions.ByteLogic

private theorem mix_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p : BitVec 64} {bytes : List UInt8} {e : RamState → Effect}
    (pre : CalleePre s boundary 0x109530 32 32 128)
    (stage : Stage s t boundary)
    (step : StepEffect (fun t => t.RIP = p) (codeRange p bytes) e)
    (code : CodeIn (codeRange p bytes) t) (rip : t.RIP = p)
    (next : InProgram (e t).rip)
    (components : ∀ c ∈ (e t).components, BodyComponent (rspOf t) c)
    (rsp : Component.reg 4 ∉ (e t).components) :
    ∃ u, Stage s u boundary ∧ (e t).Holds t u := by
  obtain ⟨u, run, ready, effect⟩ := step.advances stage.ready code rip
    (boundary_ne_program pre.outerBoundary next)
  exact ⟨u, stage.of_effect pre run ready effect components rsp, effect⟩

private theorem mix_register_read {s t : RamState} {p : BitVec 64}
    {dst : BitVec 5} {value : BitVec 64} {flags : Option StatusFlagsOutcome}
    (effect : (Effect.mk p [⟨(Operand.reg dst : Operand 64), value⟩] flags).Holds s t)
    (r : BitVec 5) :
    (Operand.reg r : Operand 64).read t =
      if dst = r then value else (Operand.reg r : Operand 64).read s := by
  by_cases h : dst = r
  · subst r
    exact (ite_eq_left rfl).symm ▸ effect.writes
  · rw [ite_eq_right h]
    apply effect.agrees.read
    cases flags <;> simp [Effect.components, Ne.symm h]

theorem mix_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a : Limbs}
    (pre : CalleePre s boundary 0x109530 32 32 128)
    (state : SelectedState s t boundary a) :
    ∃ u, MixedState s u boundary a := by
  obtain ⟨u1, stage1, effect1⟩ := mix_step pre state.toStage
    (show StepEffect _ _ (decR64Effect 0x1095e6 3) from
      dec_r64_effect_step 0x1095e6 0x48 0xcb (by simp [RexWPrefix]) rfl rfl)
    (programText_slice (programLoaded_codeIn state.loaded) 0x95e6
      [0x48, 0xff, 0xcb] (by decide +kernel) rfl) state.rip
    (inProgram_of_textOffset 0x95e9 (by decide +kernel))
    (by simp [decR64Effect_components, BodyComponent])
    (by simp [decR64Effect_components])
  have reads1 := mix_register_read effect1
  obtain ⟨u2, stage2, effect2⟩ := mix_step pre stage1
    (show StepEffect _ _ (decR64Effect 0x1095e9 5) from
      dec_r64_effect_step 0x1095e9 0x48 0xcd (by simp [RexWPrefix]) rfl rfl)
    (programText_slice (programLoaded_codeIn stage1.loaded) 0x95e9
      [0x48, 0xff, 0xcd] (by decide +kernel) rfl) effect1.rip
    (inProgram_of_textOffset 0x95ec (by decide +kernel))
    (by simp [decR64Effect_components, BodyComponent])
    (by simp [decR64Effect_components])
  have reads2 := mix_register_read effect2
  obtain ⟨u3, stage3, effect3⟩ := mix_step pre stage2
    (show StepEffect _ _ (andR64R64Effect 0x1095ec 5 13) from
      and_r64_r64_effect_step 0x1095ec 0x4c 0xed (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage2.loaded) 0x95ec
      [0x4c, 0x21, 0xed] (by decide +kernel) rfl) effect2.rip
    (inProgram_of_textOffset 0x95ef (by decide +kernel))
    (by simp [andR64R64Effect_components, BodyComponent])
    (by simp [andR64R64Effect_components])
  have reads3 := mix_register_read effect3
  obtain ⟨u4, stage4, effect4⟩ := mix_step pre stage3
    (show StepEffect _ _ (andR64R64Effect 0x1095ef 3 5) from
      and_r64_r64_effect_step 0x1095ef 0x48 0xeb (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage3.loaded) 0x95ef
      [0x48, 0x21, 0xeb] (by decide +kernel) rfl) effect3.rip
    (inProgram_of_textOffset 0x95f2 (by decide +kernel))
    (by simp [andR64R64Effect_components, BodyComponent])
    (by simp [andR64R64Effect_components])
  have reads4 := mix_register_read effect4
  obtain ⟨u5, stage5, effect5⟩ := mix_step pre stage4
    (show StepEffect _ _ (decR64Effect 0x1095f2 8) from
      dec_r64_effect_step 0x1095f2 0x49 0xc8 (by simp [RexWPrefix]) rfl rfl)
    (programText_slice (programLoaded_codeIn stage4.loaded) 0x95f2
      [0x49, 0xff, 0xc8] (by decide +kernel) rfl) effect4.rip
    (inProgram_of_textOffset 0x95f5 (by decide +kernel))
    (by simp [decR64Effect_components, BodyComponent])
    (by simp [decR64Effect_components])
  have reads5 := mix_register_read effect5
  obtain ⟨u6, stage6, effect6⟩ := mix_step pre stage5
    (show StepEffect _ _ (xorR64R64Effect 0x1095f5 13 15) from
      xor_r64_r64_effect_step 0x1095f5 0x4d 0xfd (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage5.loaded) 0x95f5
      [0x4d, 0x31, 0xfd] (by decide +kernel) rfl) effect5.rip
    (inProgram_of_textOffset 0x95f8 (by decide +kernel))
    (by simp [xorR64R64Effect_components, BodyComponent])
    (by simp [xorR64R64Effect_components])
  have reads6 := mix_register_read effect6
  obtain ⟨u7, stage7, effect7⟩ := mix_step pre stage6
    (show StepEffect _ _ (negR64Effect 0x1095f8 11) from
      neg_r64_effect_step 0x1095f8 0x49 0xdb (by simp [RexWPrefix]) rfl rfl)
    (programText_slice (programLoaded_codeIn stage6.loaded) 0x95f8
      [0x49, 0xf7, 0xdb] (by decide +kernel) rfl) effect6.rip
    (inProgram_of_textOffset 0x95fb (by decide +kernel))
    (by simp [negR64Effect, Effect.components, BodyComponent])
    (by simp [negR64Effect, Effect.components])
  have reads7 := mix_register_read effect7
  obtain ⟨u8, stage8, effect8⟩ := mix_step pre stage7
    (show StepEffect _ _ (andR64R64Effect 0x1095fb 11 13) from
      and_r64_r64_effect_step 0x1095fb 0x4d 0xeb (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage7.loaded) 0x95fb
      [0x4d, 0x21, 0xeb] (by decide +kernel) rfl) effect7.rip
    (inProgram_of_textOffset 0x95fe (by decide +kernel))
    (by simp [andR64R64Effect_components, BodyComponent])
    (by simp [andR64R64Effect_components])
  have reads8 := mix_register_read effect8
  obtain ⟨u9, stage9, effect9⟩ := mix_step pre stage8
    (show StepEffect _ _ (xorR64R64Effect 0x1095fe 11 15) from
      xor_r64_r64_effect_step 0x1095fe 0x4d 0xfb (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage8.loaded) 0x95fe
      [0x4d, 0x31, 0xfb] (by decide +kernel) rfl) effect8.rip
    (inProgram_of_textOffset 0x9601 (by decide +kernel))
    (by simp [xorR64R64Effect_components, BodyComponent])
    (by simp [xorR64R64Effect_components])
  have reads9 := mix_register_read effect9
  obtain ⟨u10, stage10, effect10⟩ := mix_step pre stage9
    (show StepEffect _ _ (andR64R64Effect 0x109601 8 11) from
      and_r64_r64_effect_step 0x109601 0x4d 0xd8 (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage9.loaded) 0x9601
      [0x4d, 0x21, 0xd8] (by decide +kernel) rfl) effect9.rip
    (inProgram_of_textOffset 0x9604 (by decide +kernel))
    (by simp [andR64R64Effect_components, BodyComponent])
    (by simp [andR64R64Effect_components])
  have reads10 := mix_register_read effect10
  obtain ⟨u11, stage11, effect11⟩ := mix_step pre stage10
    (show StepEffect _ _ (xorR64R64Effect 0x109604 15 14) from
      xor_r64_r64_effect_step 0x109604 0x4d 0xf7 (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage10.loaded) 0x9604
      [0x4d, 0x31, 0xf7] (by decide +kernel) rfl) effect10.rip
    (inProgram_of_textOffset 0x9607 (by decide +kernel))
    (by simp [xorR64R64Effect_components, BodyComponent])
    (by simp [xorR64R64Effect_components])
  have reads11 := mix_register_read effect11
  obtain ⟨u12, stage12, effect12⟩ := mix_step pre stage11
    (show StepEffect _ _ (negR64Effect 0x109607 12) from
      neg_r64_effect_step 0x109607 0x49 0xdc (by simp [RexWPrefix]) rfl rfl)
    (programText_slice (programLoaded_codeIn stage11.loaded) 0x9607
      [0x49, 0xf7, 0xdc] (by decide +kernel) rfl) effect11.rip
    (inProgram_of_textOffset 0x960a (by decide +kernel))
    (by simp [negR64Effect, Effect.components, BodyComponent])
    (by simp [negR64Effect, Effect.components])
  have reads12 := mix_register_read effect12
  obtain ⟨u13, stage13, effect13⟩ := mix_step pre stage12
    (show StepEffect _ _ (andR64R64Effect 0x10960a 12 15) from
      and_r64_r64_effect_step 0x10960a 0x4d 0xfc (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage12.loaded) 0x960a
      [0x4d, 0x21, 0xfc] (by decide +kernel) rfl) effect12.rip
    (inProgram_of_textOffset 0x960d (by decide +kernel))
    (by simp [andR64R64Effect_components, BodyComponent])
    (by simp [andR64R64Effect_components])
  have reads13 := mix_register_read effect13
  obtain ⟨u14, stage14, effect14⟩ := mix_step pre stage13
    (show StepEffect _ _ (xorR64R64Effect 0x10960d 12 14) from
      xor_r64_r64_effect_step 0x10960d 0x4d 0xf4 (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage13.loaded) 0x960d
      [0x4d, 0x31, 0xf4] (by decide +kernel) rfl) effect13.rip
    (inProgram_of_textOffset 0x9610 (by decide +kernel))
    (by simp [xorR64R64Effect_components, BodyComponent])
    (by simp [xorR64R64Effect_components])
  have reads14 := mix_register_read effect14
  obtain ⟨u15, stage15, effect15⟩ := mix_step pre stage14
    (show StepEffect _ _ (xorR64R64Effect 0x109610 5 12) from
      xor_r64_r64_effect_step 0x109610 0x4c 0xe5 (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage14.loaded) 0x9610
      [0x4c, 0x31, 0xe5] (by decide +kernel) rfl) effect14.rip
    (inProgram_of_textOffset 0x9613 (by decide +kernel))
    (by simp [xorR64R64Effect_components, BodyComponent])
    (by simp [xorR64R64Effect_components])
  have reads15 := mix_register_read effect15
  obtain ⟨u16, stage16, effect16⟩ := mix_step pre stage15
    (show StepEffect _ _ (negR64Effect 0x109613 6) from
      neg_r64_effect_step 0x109613 0x48 0xde (by simp [RexWPrefix]) rfl rfl)
    (programText_slice (programLoaded_codeIn stage15.loaded) 0x9613
      [0x48, 0xf7, 0xde] (by decide +kernel) rfl) effect15.rip
    (inProgram_of_textOffset 0x9616 (by decide +kernel))
    (by simp [negR64Effect, Effect.components, BodyComponent])
    (by simp [negR64Effect, Effect.components])
  have reads16 := mix_register_read effect16
  obtain ⟨u17, stage17, effect17⟩ := mix_step pre stage16
    (show StepEffect _ _ (andR64R64Effect 0x109616 6 5) from
      and_r64_r64_effect_step 0x109616 0x48 0xee (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage16.loaded) 0x9616
      [0x48, 0x21, 0xee] (by decide +kernel) rfl) effect16.rip
    (inProgram_of_textOffset 0x9619 (by decide +kernel))
    (by simp [andR64R64Effect_components, BodyComponent])
    (by simp [andR64R64Effect_components])
  have reads17 := mix_register_read effect17
  obtain ⟨u18, stage18, effect18⟩ := mix_step pre stage17
    (show StepEffect _ _ (xorR64R64Effect 0x109619 6 12) from
      xor_r64_r64_effect_step 0x109619 0x4c 0xe6 (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage17.loaded) 0x9619
      [0x4c, 0x31, 0xe6] (by decide +kernel) rfl) effect17.rip
    (inProgram_of_textOffset 0x961c (by decide +kernel))
    (by simp [xorR64R64Effect_components, BodyComponent])
    (by simp [xorR64R64Effect_components])
  have reads18 := mix_register_read effect18
  obtain ⟨u19, stage19, effect19⟩ := mix_step pre stage18
    (show StepEffect _ _ (xorR64R64Effect 0x10961c 14 10) from
      xor_r64_r64_effect_step 0x10961c 0x4d 0xd6 (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage18.loaded) 0x961c
      [0x4d, 0x31, 0xd6] (by decide +kernel) rfl) effect18.rip
    (inProgram_of_textOffset 0x961f (by decide +kernel))
    (by simp [xorR64R64Effect_components, BodyComponent])
    (by simp [xorR64R64Effect_components])
  have reads19 := mix_register_read effect19
  obtain ⟨u20, stage20, effect20⟩ := mix_step pre stage19
    (show StepEffect _ _ (negR64Effect 0x10961f 9) from
      neg_r64_effect_step 0x10961f 0x49 0xd9 (by simp [RexWPrefix]) rfl rfl)
    (programText_slice (programLoaded_codeIn stage19.loaded) 0x961f
      [0x49, 0xf7, 0xd9] (by decide +kernel) rfl) effect19.rip
    (inProgram_of_textOffset 0x9622 (by decide +kernel))
    (by simp [negR64Effect, Effect.components, BodyComponent])
    (by simp [negR64Effect, Effect.components])
  have reads20 := mix_register_read effect20
  obtain ⟨u21, stage21, effect21⟩ := mix_step pre stage20
    (show StepEffect _ _ (andR64R64Effect 0x109622 9 14) from
      and_r64_r64_effect_step 0x109622 0x4d 0xf1 (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage20.loaded) 0x9622
      [0x4d, 0x21, 0xf1] (by decide +kernel) rfl) effect20.rip
    (inProgram_of_textOffset 0x9625 (by decide +kernel))
    (by simp [andR64R64Effect_components, BodyComponent])
    (by simp [andR64R64Effect_components])
  have reads21 := mix_register_read effect21
  obtain ⟨u22, stage22, effect22⟩ := mix_step pre stage21
    (show StepEffect _ _ (xorR64R64Effect 0x109625 9 10) from
      xor_r64_r64_effect_step 0x109625 0x4d 0xd1 (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage21.loaded) 0x9625
      [0x4d, 0x31, 0xd1] (by decide +kernel) rfl) effect21.rip
    (inProgram_of_textOffset 0x9628 (by decide +kernel))
    (by simp [xorR64R64Effect_components, BodyComponent])
    (by simp [xorR64R64Effect_components])
  have reads22 := mix_register_read effect22
  obtain ⟨u23, stage23, effect23⟩ := mix_step pre stage22
    (show StepEffect _ _ (xorR64R64Effect 0x109628 11 9) from
      xor_r64_r64_effect_step 0x109628 0x4d 0xcb (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage22.loaded) 0x9628
      [0x4d, 0x31, 0xcb] (by decide +kernel) rfl) effect22.rip
    (inProgram_of_textOffset 0x962b (by decide +kernel))
    (by simp [xorR64R64Effect_components, BodyComponent])
    (by simp [xorR64R64Effect_components])
  have reads23 := mix_register_read effect23
  obtain ⟨u24, stage24, effect24⟩ := mix_step pre stage23
    (show StepEffect _ _ (negR64Effect 0x10962b 0) from
      neg_r64_effect_step 0x10962b 0x48 0xd8 (by simp [RexWPrefix]) rfl rfl)
    (programText_slice (programLoaded_codeIn stage23.loaded) 0x962b
      [0x48, 0xf7, 0xd8] (by decide +kernel) rfl) effect23.rip
    (inProgram_of_textOffset 0x962e (by decide +kernel))
    (by simp [negR64Effect, Effect.components, BodyComponent])
    (by simp [negR64Effect, Effect.components])
  have reads24 := mix_register_read effect24
  obtain ⟨u25, stage25, effect25⟩ := mix_step pre stage24
    (show StepEffect _ _ (xorR8Imm8Effect 0x10962e 3 2 1) from
      xor_r8_imm8_legacy_effect_step 0x10962e 0xf2 1 rfl rfl (by decide +kernel))
    (programText_slice (programLoaded_codeIn stage24.loaded) 0x962e
      [0x80, 0xf2, 0x1] (by decide +kernel) rfl) effect24.rip
    (inProgram_of_textOffset 0x9631 (by decide +kernel))
    (by simp [xorR8Imm8Effect, Effect.components, BodyComponent])
    (by simp [xorR8Imm8Effect, Effect.components])
  have reads25 := mix_register_read effect25
  obtain ⟨u26, stage26, effect26⟩ := mix_step pre stage25
    (show StepEffect _ _ (movR64R64Effect 0x109631 10 3) from
      mov_r64_r64_effect_step 0x109631 0x49 0xda (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage25.loaded) 0x9631
      [0x49, 0x89, 0xda] (by decide +kernel) rfl) effect25.rip
    (inProgram_of_textOffset 0x9634 (by decide +kernel))
    (by simp [movR64R64Effect_components, BodyComponent])
    (by simp [movR64R64Effect_components])
  have reads26 := mix_register_read effect26
  obtain ⟨u27, stage27, effect27⟩ := mix_step pre stage26
    (show StepEffect _ _ (movR32R32Effect 0x109634 2 1 2) from
      mov_r32_r32_effect_step 0x109634 0xd1 rfl)
    (programText_slice (programLoaded_codeIn stage26.loaded) 0x9634
      [0x89, 0xd1] (by decide +kernel) rfl) effect26.rip
    (inProgram_of_textOffset 0x9636 (by decide +kernel))
    (by simp [movR32R32Effect_components, BodyComponent])
    (by simp [movR32R32Effect_components])
  have reads27 := mix_register_read effect27
  obtain ⟨u28, stage28, effect28⟩ := mix_step pre stage27
    (show StepEffect _ _ (shrR64CLEffect 0x109636 10) from
      shr_r64_cl_effect_step 0x109636 0x49 0xea (by simp [RexWPrefix]) rfl rfl)
    (programText_slice (programLoaded_codeIn stage27.loaded) 0x9636
      [0x49, 0xd3, 0xea] (by decide +kernel) rfl) effect27.rip
    (inProgram_of_textOffset 0x9639 (by decide +kernel))
    (by simp [shrR64CLEffect, shrR64Effect_components, BodyComponent])
    (by simp [shrR64CLEffect, shrR64Effect_components])
  have reads28 := mix_register_read effect28
  obtain ⟨u29, stage29, effect29⟩ := mix_step pre stage28
    (show StepEffect _ _ (andR64R64Effect 0x109639 0 11) from
      and_r64_r64_effect_step 0x109639 0x4c 0xd8 (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage28.loaded) 0x9639
      [0x4c, 0x21, 0xd8] (by decide +kernel) rfl) effect28.rip
    (inProgram_of_textOffset 0x963c (by decide +kernel))
    (by simp [andR64R64Effect_components, BodyComponent])
    (by simp [andR64R64Effect_components])
  have reads29 := mix_register_read effect29
  obtain ⟨u30, stage30, effect30⟩ := mix_step pre stage29
    (show StepEffect _ _ (xorR64R64Effect 0x10963c 0 9) from
      xor_r64_r64_effect_step 0x10963c 0x4c 0xc8 (by simp [RexWPrefix]) rfl)
    (programText_slice (programLoaded_codeIn stage29.loaded) 0x963c
      [0x4c, 0x31, 0xc8] (by decide +kernel) rfl) effect29.rip
    (inProgram_of_textOffset 0x963f (by decide +kernel))
    (by simp [xorR64R64Effect_components, BodyComponent])
    (by simp [xorR64R64Effect_components])
  have reads30 := mix_register_read effect30
  have initial0 : (Operand.reg 0 : Operand 64).read t = 0 := state.rax
  have initial2 : (Operand.reg 2 : Operand 64).read t = 0 := state.rdx
  have initial3 : (Operand.reg 3 : Operand 64).read t = 0 := state.rbx
  have initial5 : (Operand.reg 5 : Operand 64).read t = 0 := state.rbp
  have initial6 : (Operand.reg 6 : Operand 64).read t = 0 := state.rsi
  have initial8 : (Operand.reg 8 : Operand 64).read t = 0 := state.r8
  have initial9 : (Operand.reg 9 : Operand 64).read t = 0 := state.r9
  have initial10 : (Operand.reg 10 : Operand 64).read t = a.l0 := state.r10
  have initial11 : (Operand.reg 11 : Operand 64).read t = 0 := state.r11
  have initial12 : (Operand.reg 12 : Operand 64).read t = 0 := state.r12
  have initial13 : (Operand.reg 13 : Operand 64).read t = a.l3 := state.r13
  have initial14 : (Operand.reg 14 : Operand 64).read t = a.l1 := state.r14
  have initial15 : (Operand.reg 15 : Operand 64).read t = a.l2 := state.r15
  have lowRdx : (Operand.reg 2 : Operand 8).read u24 =
      ((Operand.reg 2 : Operand 64).read u24).setWidth 8 := rfl
  have sameMemory : u30.external = t.external := by
    rw [effect30.agrees.external (by simp [xorR64R64Effect_components, Component.Covers])]
    rw [effect29.agrees.external (by simp [andR64R64Effect_components, Component.Covers])]
    rw [effect28.agrees.external (by simp [shrR64CLEffect, shrR64Effect_components, Component.Covers])]
    rw [effect27.agrees.external (by simp [movR32R32Effect_components, Component.Covers])]
    rw [effect26.agrees.external (by simp [movR64R64Effect_components, Component.Covers])]
    rw [effect25.agrees.external (by simp [xorR8Imm8Effect, Effect.components, Component.Covers])]
    rw [effect24.agrees.external (by simp [negR64Effect, Effect.components, Component.Covers])]
    rw [effect23.agrees.external (by simp [xorR64R64Effect_components, Component.Covers])]
    rw [effect22.agrees.external (by simp [xorR64R64Effect_components, Component.Covers])]
    rw [effect21.agrees.external (by simp [andR64R64Effect_components, Component.Covers])]
    rw [effect20.agrees.external (by simp [negR64Effect, Effect.components, Component.Covers])]
    rw [effect19.agrees.external (by simp [xorR64R64Effect_components, Component.Covers])]
    rw [effect18.agrees.external (by simp [xorR64R64Effect_components, Component.Covers])]
    rw [effect17.agrees.external (by simp [andR64R64Effect_components, Component.Covers])]
    rw [effect16.agrees.external (by simp [negR64Effect, Effect.components, Component.Covers])]
    rw [effect15.agrees.external (by simp [xorR64R64Effect_components, Component.Covers])]
    rw [effect14.agrees.external (by simp [xorR64R64Effect_components, Component.Covers])]
    rw [effect13.agrees.external (by simp [andR64R64Effect_components, Component.Covers])]
    rw [effect12.agrees.external (by simp [negR64Effect, Effect.components, Component.Covers])]
    rw [effect11.agrees.external (by simp [xorR64R64Effect_components, Component.Covers])]
    rw [effect10.agrees.external (by simp [andR64R64Effect_components, Component.Covers])]
    rw [effect9.agrees.external (by simp [xorR64R64Effect_components, Component.Covers])]
    rw [effect8.agrees.external (by simp [andR64R64Effect_components, Component.Covers])]
    rw [effect7.agrees.external (by simp [negR64Effect, Effect.components, Component.Covers])]
    rw [effect6.agrees.external (by simp [xorR64R64Effect_components, Component.Covers])]
    rw [effect5.agrees.external (by simp [decR64Effect_components, Component.Covers])]
    rw [effect4.agrees.external (by simp [andR64R64Effect_components, Component.Covers])]
    rw [effect3.agrees.external (by simp [andR64R64Effect_components, Component.Covers])]
    rw [effect2.agrees.external (by simp [decR64Effect_components, Component.Covers])]
    rw [effect1.agrees.external (by simp [decR64Effect_components, Component.Covers])]
  refine ⟨u30, ⟨stage30, effect30.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [sameMemory]
    exact state.outputSaved
  · change ((Operand.reg 7 : Operand 64).read u30).setWidth 8 = 0
    have hdil : ((Operand.reg 7 : Operand 64).read t).setWidth 8 = 0 := state.dil
    simpa only [reads30, reads29, reads28, reads27, reads26, reads25, reads24, reads23, reads22, reads21,
      reads20, reads19, reads18, reads17, reads16, reads15, reads14, reads13, reads12, reads11, reads10,
      reads9, reads8, reads7, reads6, reads5, reads4, reads3, reads2, reads1, BitVec.reduceEq, ↓reduceIte] using hdil
  · change (Operand.reg 2 : Operand 64).read u30 = 1
    simp only [lowRdx, reads30, reads29, reads28, reads27, reads26, reads25, reads24, reads23, reads22,
      reads21, reads20, reads19, reads18, reads17, reads16, reads15, reads14, reads13, reads12, reads11,
      reads10, reads9, reads8, reads7, reads6, reads5, reads4, reads3, reads2, reads1, initial2,
      BitVec.reduceEq, ↓reduceIte]
    decide +kernel
  · change (Operand.reg 3 : Operand 64).read u30 = a.l3
    simp only [reads30, reads29, reads28, reads27, reads26, reads25, reads24, reads23, reads22, reads21,
      reads20, reads19, reads18, reads17, reads16, reads15, reads14, reads13, reads12, reads11, reads10,
      reads9, reads8, reads7, reads6, reads5, reads4, reads3, reads2, reads1, initial3, initial5,
      initial13, BitVec.reduceEq, ↓reduceIte]
    change BitVec.allOnes 64 &&& (BitVec.allOnes 64 &&& a.l3) = a.l3
    simp only [BitVec.allOnes_and]
  · change (Operand.reg 8 : Operand 64).read u30 = a.l2
    simp only [reads30, reads29, reads28, reads27, reads26, reads25, reads24, reads23, reads22, reads21,
      reads20, reads19, reads18, reads17, reads16, reads15, reads14, reads13, reads12, reads11, reads10,
      reads9, reads8, reads7, reads6, reads5, reads4, reads3, reads2, reads1, initial8, initial11,
      initial13, initial15, BitVec.reduceEq, ↓reduceIte]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.neg_zero, BitVec.zero_and, BitVec.zero_xor]
    change BitVec.allOnes 64 &&& a.l2 = a.l2
    exact BitVec.allOnes_and
  · change (Operand.reg 6 : Operand 64).read u30 = a.l1
    simp only [reads30, reads29, reads28, reads27, reads26, reads25, reads24, reads23, reads22, reads21,
      reads20, reads19, reads18, reads17, reads16, reads15, reads14, reads13, reads12, reads11, reads10,
      reads9, reads8, reads7, reads6, reads5, reads4, reads3, reads2, reads1, initial5, initial6,
      initial12, initial13, initial14, initial15, BitVec.reduceEq, ↓reduceIte]
    simp
  · change (Operand.reg 0 : Operand 64).read u30 = a.l0
    simp only [reads30, reads29, reads28, reads27, reads26, reads25, reads24, reads23, reads22, reads21,
      reads20, reads19, reads18, reads17, reads16, reads15, reads14, reads13, reads12, reads11, reads10,
      reads9, reads8, reads7, reads6, reads5, reads4, reads3, reads2, reads1, initial0, initial9,
      initial10, initial11, initial13, initial14, initial15, BitVec.reduceEq, ↓reduceIte]
    simp

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
