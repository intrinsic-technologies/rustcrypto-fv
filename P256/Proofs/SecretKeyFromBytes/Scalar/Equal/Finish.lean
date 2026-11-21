import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Instructions
import P256.Proofs.Common.Encoding.Parser.CompressedRoute.Movzx
import P256.Proofs.Common.Encoding.Parser.ResultTag.Cmove
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Common.Encoding.Parser.CompressedRoute (movzxAlEffect movzx_r32_al_effect_step)
open P256.Proofs.Common.Encoding.Parser.ResultTag (cmove_r32_r32_effect_step)
open P256.Proofs.Common.Instructions (cmovR32R32Effect cmovR32R32Value)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.SecretKeyFromBytes.Scalar.Equal

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {b : Bool}
    (pre : Pre s boundary) (stage : Stage s t boundary) (rip : t.RIP = 0x1192aa)
    (al : (t.regValue .rax).setWidth 8 = if b then 1 else 0) :
    ∃ u, Result s u boundary ∧ (u.regValue .rax).setWidth 8 = if b then 1 else 0 := by
  obtain ⟨t1, run1, ready1, e1⟩ := (movzx_r32_al_effect_step 0x1192aa 0xc8 rfl rfl).advances
    stage.ready (programText_slice (programLoaded_codeIn (stage.loaded pre.loaded))
      0x192aa [0x0f,0xb6,0xc8] (by decide +kernel) rfl) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x192ad (by decide)))
  change (movzxAlEffect 0x1192aa 1 t).Holds t t1 at e1
  have st1 := stage.extend run1 ready1 e1 (by simp [movzxAlEffect, Effect.components, clobbers])
  have cx1 : t1.regValue .rcx = if b then 1 else 0 := by
    have hw : t1.regValue .rcx = ((t.regValue .rax).setWidth 8).setWidth 64 := e1.writes
    rw [hw, al]
    cases b <;> rfl
  obtain ⟨t2, run2, ready2, e2⟩ := (xor_r32_r32_effect_step 0x1192ad 0xc0 rfl).advances ready1
    (programText_slice (programLoaded_codeIn (st1.loaded pre.loaded)) 0x192ad [0x31,0xc0]
      (by decide +kernel) rfl) e1.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x192af (by decide)))
  change (xorR32R32Effect 0x1192ad 2 0 0 t1).Holds t1 t2 at e2
  have st2 := st1.extend run2 ready2 e2 (by simp [clobbers])
  have ax2 : t2.regValue .rax = 0 := by
    have hw : t2.regValue .rax = ((t1.regValue .rax).setWidth 32 ^^^
      (t1.regValue .rax).setWidth 32).setWidth 64 := e2.writes
    simpa using hw
  obtain ⟨t3, run3, ready3, e3⟩ :=
    (mov_r16_imm16_effect_step 0x1192af 0xba (by decide) 1).advances ready2
    (programText_slice (programLoaded_codeIn (st2.loaded pre.loaded)) 0x192af [0x66,0xba,1,0]
      (by decide +kernel) rfl) e2.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x192b3 (by decide)))
  change (movR16Imm16Effect 0x1192af 2 1 t2).Holds t2 t3 at e3
  have st3 := st2.extend run3 ready3 e3 (by simp [movR16Imm16Effect_components, clobbers])
  have dx3 : (t3.regValue .rdx).setWidth 16 = 1 := by
    have hw : t3.regValue .rdx = mergeGPR 16 1 (t2.regValue .rdx) := e3.writes
    rw [hw, mergeGPR16_low (by decide)]
    rfl
  have cx3 : t3.regValue .rcx = if b then 1 else 0 :=
    ((e2.agrees.trans e3.agrees).read (n := 64) (r := 1)
      (by simp [movR16Imm16Effect_components])).trans cx1
  obtain ⟨t4, run4, ready4, e4⟩ := (xor_r16_r16_effect_step 0x1192b3 0xd1 rfl).advances ready3
    (programText_slice (programLoaded_codeIn (st3.loaded pre.loaded)) 0x192b3 [0x66,0x31,0xd1]
      (by decide +kernel) rfl) e3.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x192b6 (by decide)))
  change (xorR16R16Effect 0x1192b3 1 2 t3).Holds t3 t4 at e4
  have st4 := st3.extend run4 ready4 e4 (by simp [xorR16R16Effect_components, clobbers])
  have zf4 : (StatusFlags.ofRFLAGS t4.RFLAGS).ZF = b := by
    have hf := e4.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t4.RFLAGS).ZF =
      (((t3.regValue .rcx).setWidth 16 ^^^ (t3.regValue .rdx).setWidth 16) == 0) at hf
    rw [cx3, dx3] at hf
    cases b <;> exact hf
  obtain ⟨t5, run5, ready5, e5⟩ := (cmove_r32_r32_effect_step 0x1192b6 0xc2 rfl).advances ready4
    (programText_slice (programLoaded_codeIn (st4.loaded pre.loaded)) 0x192b6 [0x0f,0x44,0xc2]
      (by decide +kernel) rfl) e4.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x192b9 (by decide)))
  change (cmovR32R32Effect 0x1192b6 4 0 2 t4).Holds t4 t5 at e5
  have st5 := st4.extend run5 ready5 e5 (by simp [cmovR32R32Effect, Effect.components, clobbers])
  have ax4 : t4.regValue .rax = 0 :=
    ((e3.agrees.trans e4.agrees).read (n := 64) (r := 0)
      (by simp [movR16Imm16Effect_components, xorR16R16Effect_components])).trans ax2
  have dx4 : (t4.regValue .rdx).setWidth 16 = 1 :=
    (e4.agrees.read (n := 16) (r := 2) (by simp [xorR16R16Effect_components])).trans dx3
  have al5 : (t5.regValue .rax).setWidth 8 = if b then 1 else 0 := by
    have hw : t5.regValue .rax = (cmovR32R32Value 4 0 2 t4).setWidth 64 := e5.writes
    rw [hw]
    simp only [cmovR32R32Value, condHolds, zf4]
    change ((if b then (t4.regValue .rdx).setWidth 32 else
      (t4.regValue .rax).setWidth 32).setWidth 64).setWidth 8 = _
    cases hb : b
    · simp [ax4]
    · have h := congrArg (BitVec.setWidth 8) dx4
      simpa using h
  have top5 : stackTop t5 = (returnBoundary s).rip := by
    change memLoad t5.external (stackPtr t5) 64 = memLoad s.external (stackPtr s) 64
    rw [st5.rsp, st5.memory]
  have read5 : MemReadable t5 (stackPtr t5) 8 := by
    rw [st5.rsp]
    exact pre.returnReadable.of_external_eq st5.memory
  obtain ⟨u, run6, ready6, e6⟩ := (ret_effect_step 0x1192b9).advances ready5
    (programText_slice (programLoaded_codeIn (st5.loaded pre.loaded)) 0x192b9 [0xc3]
      (by decide +kernel) rfl)
    ⟨⟨e5.rip, read5⟩, top5 ▸ P256.Proofs.Program.inProgram_low pre.returnInProgram⟩
    (by change stackTop t5 ≠ boundary.rip
        rw [top5]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  obtain ⟨fuel, hf⟩ := st5.execution
  refine ⟨u, ⟨⟨fuel+1, hf.trans run6⟩, ready6, e6.rip.trans top5, ?_, ?_⟩, ?_⟩
  · have hw : stackPtr u = stackPtr t5 + 8 := e6.writes
    rw [hw, st5.rsp]
    rfl
  · exact (st5.agrees.trans e6.agrees).mono (by simp [clobbers])
  · exact (e6.agrees.read (n := 8) (r := 0) (by simp)).trans al5

end P256.Proofs.SecretKeyFromBytes.Scalar.Equal
