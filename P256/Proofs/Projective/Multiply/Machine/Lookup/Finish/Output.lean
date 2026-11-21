import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.Transfer
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Run

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure OutputPre (s : RamState) : Prop where
  rip : s.RIP = 0x10494b
  readable : MemReadable s (stackPtr s+208) 8

def outputBytes : List UInt8 :=
  [0xb9,12,0,0,0,0x48,0x8b,0xbc,0x24,0xd0,0,0,0,0x4c,0x89,0xf6]

def outputEffect (s : RamState) : Effect :=
  { rip := 0x10495b
    writes := [⟨(Operand.reg 1 : Operand 64),12⟩,
      ⟨(Operand.reg 7 : Operand 64),(Operand.mem (stackPtr s+208) : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64),s.regValue .r14⟩] }

theorem output_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OutputPre (codeRange 0x10494b outputBytes) (Effect.post outputEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10494b 0xb9 (by decide) 12)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4950 (by decide))
  advance_then (mov_r64_m64_effect_step 0x104950 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 208)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10494b outputBytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x4958 (by decide))⟩
    x86_norm
    exact hP.readable
  advance_then (mov_r64_r64_effect_step 0x104958 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10494b outputBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x495b (by decide))⟩
  advance_finish [outputEffect]

theorem output_result [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (execution : ∃ fuel, Advances boundary fuel s t)
    (rip : t.RIP = 0x10494b) (input : ProjectiveAt t (stackPtr s-344) point)
    (r14 : t.regValue .r14 = stackPtr s-344)
    (saved : (Operand.mem (stackPtr s-152) : Operand 64).read t = s.regValue .rdi) :
    ∃ u, CalleeResult s u boundary 96 496 ∧ ProjectiveAt u (s.regValue .rdi) point := by
  obtain ⟨n,u,run,ready,_,effect⟩ := output_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x494b outputBytes
      (by decide) (by decide +kernel))
    ⟨rip,stack_readable pre state (offset := 208) (by decide)⟩
  have frame := state.after_registers ready effect.agrees
    (by simp [outputEffect,Effect.components,Component.Covers])
    (by simp [outputEffect,Effect.components])
  have memory : u.external = t.external :=
    effect.agrees.external (by simp [outputEffect,Effect.components,Component.Covers])
  have hw := effect.writes
  change u.regValue .rcx = 12 ∧
    u.regValue .rdi = (Operand.mem (stackPtr t+208) : Operand 64).read t ∧
    u.regValue .rsi = t.regValue .r14 at hw
  have dst : u.regValue .rdi = s.regValue .rdi := by
    have a : stackPtr t+208 = stackPtr s-152 := stack_address state.rsp (by decide)
    rw [a,saved] at hw
    exact hw.2.1
  obtain ⟨v,run',frame',rip',value,_⟩ := transfer pre frame effect.rip
    (hw.2.2.trans r14) dst hw.1 (Scanning.projective_mem input memory)
  obtain ⟨w,result,mem⟩ := epilogue pre frame' rip' (by
    obtain ⟨m,initial⟩ := execution
    exact ⟨m+n+12,(initial.trans run).trans run'⟩)
  exact ⟨w,result,Scanning.projective_mem value mem⟩

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
