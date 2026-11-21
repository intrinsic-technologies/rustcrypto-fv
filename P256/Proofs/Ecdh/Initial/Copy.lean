import P256.Proofs.Ecdh.Initial.Support
import P256.Proofs.Projective.Copy
import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Common.EffectCompose.Advance

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open P256.Proofs.Common.Field (AdvanceTriple)

def copySetupBytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0xf8,0x03,0,0,0xb9,0x0c,0,0,0,0x4c,0x89,0xfe]

def copySetupEffect (s : RamState) : Effect :=
  { rip := 0x10014a
    writes := [⟨(Operand.reg 7 : Operand 64),stackPtr s+1016⟩,
      ⟨(Operand.reg 1 : Operand 64),12⟩,
      ⟨(Operand.reg 6 : Operand 64),s.regValue .r15⟩] }

theorem copy_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun t => t.RIP = 0x10013a)
      (codeRange 0x10013a copySetupBytes) (Effect.post copySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x10013a 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 1016)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x142 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x100142 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x10013a copySetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x147 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x100147 0x4c 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10013a copySetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x14a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [copySetupEffect]
  · x86_norm [copySetupEffect]
    rfl
  · intro i; cases i <;> x86_norm [copySetupEffect]
  · x86_norm [copySetupEffect]

theorem copy_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Standards.SECG.ECC.Curve.Point} (pre : Ecdh.Pre s boundary)
    (state : Selected s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Ecdh.Initial s u point := by
  obtain ⟨fuel,v,run,frame,effect,memory⟩ := registers (offset := 0x13a) (bytes := copySetupBytes) (effect := copySetupEffect) state.toFrameState
    (copy_setup boundary pre.outerBoundary) (by decide) (by decide +kernel) state.rip
    (by simp [copySetupEffect,Effect.components,Component.Covers])
    (by simp [copySetupEffect,Effect.components]) (by simp [copySetupEffect,Effect.components])
    (by simp [copySetupEffect,Effect.components]) (by simp [copySetupEffect,Effect.components])
  have baseAddr : frameBase s+1784 = stackPtr s-272 := frame_address s 1784 (by decide)
  have firstAddr : frameBase s+1016 = stackPtr s-1040 := frame_address s 1016 (by decide)
  have scalarAddr : frameBase s+8 = stackPtr s-2048 := frame_address s 8 (by decide)
  have src : v.regValue .rsi = stackPtr s-272 :=
    effect.writes.2.2.trans (state.r15.trans (frame_address s 1784 (by decide)))
  have dst : v.regValue .rdi = stackPtr s-1040 :=
    effect.writes.1.trans (scalar_stack_address state.rsp (by decide) (by decide))
  have source : MemReadable v (v.regValue .rsi) 96 := by
    rw [src]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := 272)
      (by decide) (by decide)) frame.allocated
  have apart : (v.regValue .rsi).toNat+96 ≤ (v.regValue .rdi).toNat ∨
      (v.regValue .rdi).toNat+96 ≤ (v.regValue .rsi).toNat := by
    rw [src,dst]
    right
    have hs := stack_bounds pre.stack
    have h1 := stack_sub_toNat pre.stack (offset := 272) (by decide)
    have h2 := stack_sub_toNat pre.stack (offset := 1040) (by decide)
    change (stackPtr s-272).toNat = _ at h1
    change (stackPtr s-1040).toNat = _ at h2
    rw [h1,h2]
    omega
  have input : ProjectiveAt v (v.regValue .rsi) (ProjectiveWrapper.Decode.projective point) := by
    rw [src, ← baseAddr]
    exact state.base.of_bytes_eq (by intro i hi; rw [memory])
  obtain ⟨u,runU,frameU,ripU,value,agrees⟩ := Projective.Copy.copy_to_stack pre.toCalleePre frame
    0x14a (by decide) (by decide +kernel) effect.rip 1040 (by decide) (by decide)
    dst effect.writes.2.1 source apart input
  have keep (offset len : Nat) (ho : offset ≤ 2056) (hl : len ≤ offset+8)
      (ha : 1040+len ≤ offset ∨ offset+96 ≤ 1040) {i : Nat} (hi : i < len) :
      u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        v.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    apply agrees.byte
    intro c hc covered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j,hj,eq⟩ := covered
    exact stack_sub_apart pre.stack (by decide) (by omega) (by decide) hl ha.symm j hj i hi eq.symm
  refine ⟨fuel+12,u,run.trans runU,frameU,ripU,?_,?_,?_,?_,?_⟩
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp [copySetupEffect,Effect.components])).trans state.output)
  · have eq : memLoad u.external (frameBase s+8) 64 = memLoad v.external (frameBase s+8) 64 := by
      rw [scalarAddr]
      apply memLoad_congr
      intro i hi
      change (u.external[stackPtr s-2048#64+BitVec.ofNat 64 i]?).getD 0 = _
      rw [keep 2048 8 (by decide) (by decide) (by decide) hi]
      rfl
    rw [eq,memory]
    exact state.scalar
  · apply state.base.of_bytes_eq
    intro i hi
    rw [baseAddr]
    exact (keep 272 96 (by decide) (by decide) (by decide) hi).trans (by rw [memory]; rfl)
  · rw [firstAddr]
    exact value
  · exact (agrees.read (n := 64) (r := 15) (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 15) (by simp [copySetupEffect,Effect.components])).trans state.r15)

end P256.Proofs.Ecdh.Initial
