import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.InputValue
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure InputEntry [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop where
  execution : Advances boundary 16 s t
  frame : Frame s t
  rip : t.RIP = 0x114be3
  memory : t.external = inputCopyMemory s (saveMemory s)
  parameter : t.regValue .r15 = s.regValue .rsi + 32
  agrees : AgreesExcept (saveComponents s ++ [.reg 15] ++ inputCopyComponents s) s t

theorem initialize_input [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) : ∃ t, InputEntry s t boundary := by
  obtain ⟨t, entry⟩ := prologue ctx
  obtain ⟨v, run, ready, effect⟩ :=
    (mov_r64_r64_effect_step 0x114bb1 0x4d 0xc7 (by simp [RexWPrefix]) rfl).advances
      entry.ready (programText_slice (programLoaded_codeIn entry.loaded) 0x14bb1
        [0x4d, 0x89, 0xc7] (by decide) (by decide +kernel)) entry.rip
      (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x14bb4 (by decide)))
  have agrees : AgreesExcept [.reg 15, .rip] t v := effect.agrees
  have frame : Frame s v := (entry.frame ctx).after_registers ready agrees
    (by simp [Component.Covers]) (by decide)
  have input : v.regValue .rsi = s.regValue .rsi :=
    (agrees.read (n := 64) (r := 6) (by decide)).trans
      (entry.agrees.read (n := 64) (r := 6) (by simp [saveComponents, saveFrame]))
  have parameter : v.regValue .r15 = s.regValue .rsi + 32 := by
    have h : v.regValue .r15 = t.regValue .r8 := effect.writes
    exact h.trans ((entry.agrees.read (n := 64) (r := 8)
      (by simp [saveComponents, saveFrame])).trans ctx.parameters)
  obtain ⟨u, run2, frame2, rip2, agrees2, memory2⟩ := copy_input ctx frame effect.rip input
  refine ⟨u, ⟨(entry.execution.trans run).trans run2, frame2, rip2, ?_, ?_, ?_⟩⟩
  · rw [memory2, agrees.external (by simp [Component.Covers]), entry.memory]
  · exact (agrees2.read (n := 64) (r := 15) (by simp [inputCopyComponents])).trans parameter
  · apply ((entry.agrees.trans agrees).trans agrees2).mono
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with ((hc | (rfl | rfl)) | hc)
    · exact .inl (.inl hc)
    · exact .inl (.inr rfl)
    · exact .inr (by simp [inputCopyComponents])
    · exact .inr hc

theorem InputEntry.value [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (entry : InputEntry s t boundary) (ctx : ExponentPre s boundary x) :
    Field.MontgomeryAt t (exponentFrameBase s + 0x2f8) x :=
  inputCopyMemory_value ctx entry.frame (saveMemory s) entry.memory

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
