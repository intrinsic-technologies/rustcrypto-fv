import Hkdf.Proofs.NewExpand.Wrapper.Prologue.Arguments
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Wrapper

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def prepareBytes : List UInt8 :=
  [0x48, 0x81, 0xec, 0x40, 0x01, 0, 0,
   0x4c, 0x89, 0xcb, 0x4d, 0x89, 0xc6, 0x49, 0x89, 0xc8,
   0x48, 0x89, 0xd1, 0x48, 0x89, 0xf2, 0x48, 0x89, 0xfe,
   0x4c, 0x8b, 0xbc, 0x24, 0x70, 0x01, 0, 0,
   0x4c, 0x8b, 0xa4, 0x24, 0x78, 0x01, 0, 0,
   0x48, 0x89, 0xe7]

private def prepareEffect (s : RamState) : Effect where
  rip := 0x102005
  writes := [
    ⟨(.reg 4 : Operand 64), rspOf s - 320⟩,
    ⟨(.reg 3 : Operand 64), s.regValue .r9⟩,
    ⟨(.reg 14 : Operand 64), s.regValue .r8⟩,
    ⟨(.reg 8 : Operand 64), s.regValue .rcx⟩,
    ⟨(.reg 1 : Operand 64), s.regValue .rdx⟩,
    ⟨(.reg 2 : Operand 64), s.regValue .rsi⟩,
    ⟨(.reg 6 : Operand 64), s.regValue .rdi⟩,
    ⟨(.reg 15 : Operand 64), (.mem (rspOf s - 320 + 368) : Operand 64).read s⟩,
    ⟨(.reg 12 : Operand 64), (.mem (rspOf s - 320 + 376) : Operand 64).read s⟩,
    ⟨(.reg 7 : Operand 64), rspOf s - 320⟩]
  flags := some (.ofStatusFlags (subSpec (rspOf s) 320).2)

private theorem prepare_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x101fd9 ∧
      MemReadable s (rspOf s - 320 + 368) 8 ∧ MemReadable s (rspOf s - 320 + 376) 8)
      (codeRange 0x101fd9 prepareBytes) (Effect.post prepareEffect) := by
  advance_begin (sub_r64_imm32_effect_step 0x101fd9 0x48 0xec 320
    (by simp [RexWPrefix]) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x1fe0 (by decide))
  advance_then (mov_r64_r64_effect_step 0x101fe0 0x4c 0xcb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101fd9 prepareBytes 7 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1fe3 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x101fe3 0x4d 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101fd9 prepareBytes 10 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1fe6 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x101fe6 0x49 0xc8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101fd9 prepareBytes 13 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1fe9 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x101fe9 0x48 0xd1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101fd9 prepareBytes 16 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1fec (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x101fec 0x48 0xf2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101fd9 prepareBytes 19 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1fef (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x101fef 0x48 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101fd9 prepareBytes 22 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1ff2 (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x101ff2 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 368)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101fd9 prepareBytes 25 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1ffa (by decide))⟩
    x86_norm
    exact hp.2.1
  advance_then (mov_r64_m64_effect_step 0x101ffa 0x4c (by simp [RexWPrefix]) 4
    (.sib 4 none 0 (.d32 376)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101fd9 prepareBytes 33 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x2002 (by decide))⟩
    x86_norm
    exact hp.2.2
  advance_then (mov_r64_r64_effect_step 0x102002 0x48 0xe7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101fd9 prepareBytes 41 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x2005 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ effect
  apply effect.weaken
  · x86_norm [prepareEffect]
  · x86_norm [prepareEffect]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i
    cases i <;> x86_norm [prepareEffect] <;> rfl
  · x86_norm [prepareEffect]

theorem prepareExtract [Bindings] {initial t : RamState}
    {salt : Option ByteArray} {ikm info : ByteArray} {length : Nat}
    (hCall : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (run : Running initial t) (rip : t.RIP = 0x101fd9)
    (rsp : stackPtr t = stackPtr initial - 40) (saved : SavedFrame initial t)
    (regs : ∀ r, r ≠ .rsp → t.regValue r = initial.regValue r) :
    ∃ u, Running initial u ∧ u.RIP = 0x102005 ∧ stackPtr u = stackPtr initial - 360 ∧
      SavedFrame initial u ∧ Arguments initial u ∧ u.regValue .rdi = stackPtr initial - 360 ∧
      u.regValue .rsi = initial.regValue .rdi ∧ u.regValue .rdx = initial.regValue .rsi ∧
      u.regValue .rcx = initial.regValue .rdx ∧ u.regValue .r8 = initial.regValue .rcx := by
  obtain ⟨outputReadable, outputWord⟩ := stackArgumentRead hCall run 1 (by decide) (by decide)
  obtain ⟨lengthReadable, lengthWord⟩ := stackArgumentRead hCall run 2 (by decide) (by decide)
  have base : rspOf t - 320 = stackPtr initial - 360 := by
    change stackPtr t - 320 = _
    rw [rsp, BitVec.sub_sub]
    rfl
  have outputAddr : rspOf t - 320 + 368 = stackPtr initial + BitVec.ofNat 64 (8*1) := by
    rw [base, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have lengthAddr : rspOf t - 320 + 376 = stackPtr initial + BitVec.ofNat 64 (8*2) := by
    rw [base, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨_, u, executed, ready, _, effect⟩ := prepare_run _ outside t
    (supportedMachine_readyToStep run.machine)
    (programText_slice (programLoaded_codeIn run.loaded) 0x1fd9 prepareBytes
      (by decide) (by decide +kernel))
    ⟨rip, outputAddr ▸ outputReadable, lengthAddr ▸ lengthReadable⟩
  have noMem : ∀ c ∈ (prepareEffect t).components, ∀ a, ¬ c.Covers a := by
    simp [prepareEffect, Effect.components, Component.Covers]
  have avoids : ∀ r ∈ #v[Stack.region initial hkdfSha256NewExpandMinStackBytes],
      r.Avoids InProgram := by
    intro r hr a ha hp
    exact (hCall.stackSeparation.2 r hr).2 a ha (.inl hp)
  have running := run.of_agrees executed ready effect.agrees
    (fun c hc a ha ↦ (noMem c hc a ha).elim) avoids (by simp [prepareEffect, Effect.components])
  have rbp : u.regValue .rbp = t.regValue .rbp :=
    effect.agrees.read (n := 64) (r := 5) (by simp [prepareEffect, Effect.components])
  have savedU : SavedFrame initial u := by
    constructor
    · exact rbp.trans saved.rbp
    all_goals rw [effect.agrees.external noMem]
    all_goals first | exact saved.rbx | exact saved.r12 | exact saved.r13 |
      exact saved.r14 | exact saved.r15 | exact saved.ret
  have values := effect.writes
  change stackPtr u = rspOf t - 320 ∧ u.regValue .rbx = t.regValue .r9 ∧
    u.regValue .r14 = t.regValue .r8 ∧ u.regValue .r8 = t.regValue .rcx ∧
    u.regValue .rcx = t.regValue .rdx ∧ u.regValue .rdx = t.regValue .rsi ∧
    u.regValue .rsi = t.regValue .rdi ∧
    u.regValue .r15 = memLoad t.external (rspOf t - 320 + 368) 64 ∧
    u.regValue .r12 = memLoad t.external (rspOf t - 320 + 376) 64 ∧
    u.regValue .rdi = rspOf t - 320 at values
  rw [outputAddr, lengthAddr, outputWord, lengthWord, base] at values
  obtain ⟨sp, infoLen, infoPtr, ikmLen, ikmPtr, saltLen, saltPtr, output, len, dest⟩ := values
  exact ⟨u, running, effect.rip, sp, savedU,
    ⟨infoPtr.trans (regs .r8 (by decide)), infoLen.trans (regs .r9 (by decide)), output, len⟩,
    dest, saltPtr.trans (regs .rdi (by decide)), saltLen.trans (regs .rsi (by decide)),
    ikmPtr.trans (regs .rdx (by decide)), ikmLen.trans (regs .rcx (by decide))⟩

end Hkdf.Proofs.NewExpand.Wrapper
