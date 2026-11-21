import Md5.Proofs.NewEntries.UpdateFinalize.Epilogue
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Frame
import Md5.Proofs.Block.Bytes
import Md5.Proofs.MemoryRoutines.Ranges
import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.Block.Rounds.Store.Compose
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Call.Triple

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

inductive EpilogueKind where
  | slices
  | updateFinalizeInto
  | resetSecond
  | finalizeResetSecond
  | resetDiscardSecond
  deriving DecidableEq

namespace EpilogueKind

def entry : EpilogueKind → BitVec 64
  | .slices => 0x1005b9
  | .updateFinalizeInto => 0x101b69
  | .resetSecond => 0x100c68
  | .finalizeResetSecond => 0x1012f8
  | .resetDiscardSecond => 0x1017f9

def restore : EpilogueKind → BitVec 64
  | .slices => 0x1005e1
  | .updateFinalizeInto => 0x101b81
  | .resetSecond => 0x100c98
  | .finalizeResetSecond => 0x101328
  | .resetDiscardSecond => 0x101825

def frame : EpilogueKind → Nat
  | .slices => 296
  | .updateFinalizeInto => 280
  | .resetSecond => 328
  | .finalizeResetSecond => 312
  | .resetDiscardSecond => 312

def source : EpilogueKind → Nat
  | .slices => 0
  | .updateFinalizeInto => 0
  | .resetSecond => 216
  | .finalizeResetSecond => 216
  | .resetDiscardSecond => 120

def outputSlot : EpilogueKind → Nat
  | .slices => 168
  | .updateFinalizeInto => 168
  | .resetSecond => 184
  | .finalizeResetSecond => 184
  | .resetDiscardSecond => 288

def outputOffset : EpilogueKind → Nat
  | .slices => 0
  | .updateFinalizeInto => 0
  | .resetSecond => 16
  | .finalizeResetSecond => 16
  | .resetDiscardSecond => 0

def restoreBytes (kind : EpilogueKind) : List UInt8 :=
  [0x48, 0x81, 0xc4] ++ immBytes 32 (BitVec.ofNat 32 kind.frame) ++
    [0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]

end EpilogueKind

structure RestorePre (kind : EpilogueKind) (s : RamState) : Prop where
  rip : s.RIP = kind.restore
  read : MemReadable s (stackPtr s + BitVec.ofNat 64 kind.frame) 56

def restoreEffect (kind : EpilogueKind) (s : RamState) : Effect :=
  { rip := kind.restore + 17
    writes := [
      ⟨.reg 3, (Operand.mem (stackPtr s + BitVec.ofNat 64 kind.frame) : Operand 64).read s⟩,
      ⟨.reg 12, (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.frame + 8)) : Operand 64).read s⟩,
      ⟨.reg 13, (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.frame + 16)) : Operand 64).read s⟩,
      ⟨.reg 14, (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.frame + 24)) : Operand 64).read s⟩,
      ⟨.reg 15, (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.frame + 32)) : Operand 64).read s⟩,
      ⟨.reg 5, (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.frame + 40)) : Operand 64).read s⟩,
      ⟨.reg 4, stackPtr s + BitVec.ofNat 64 (kind.frame + 48)⟩]
    flags := some (.ofStatusFlags (addSpec (stackPtr s) (BitVec.ofNat 64 kind.frame)).2) }

private theorem pop_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    Effect.Local (popR64Effect p len dst) := by
  refine ⟨fun _ _ _ ↦ rfl, ?_, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro t t' h
    have hsp : stackPtr t = stackPtr t' := congrArg (fun g ↦ g[gprIndex 4]) h.gpr
    simp only [popR64Effect, hsp, h.read_mem]
  · intro t t' _ i hi
    exact congrArg some hi
  · intro t
    simp [popR64Effect, Write.Full, Operand.Full]

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_local] pop_local
attribute [local x86_compose] popR64Effect addR64Imm32Effect stackPtr_read

private theorem pop_pre {s t : RamState} {e : Effect} {p : BitVec 64}
    (h : e.Holds s t) (ho : Obs (e.after s true) t) (hp : e.rip = p)
    (hr : MemReadable s (stackPtr (e.after s true)) 8) : PopPre p t := by
  refine ⟨h.rip_of hp, ?_⟩
  have hsp : stackPtr (e.after s true) = stackPtr t := ho.read (.reg 4 : Operand 64) trivial
  rw [← hsp]
  exact hr.of_holds h

set_option maxHeartbeats 600000 in
theorem slices_restore [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (RestorePre .slices)
      (codeRange 0x1005e1 (EpilogueKind.restoreBytes .slices)) (restoreEffect .slices) := by
  change AdvancesBlock boundary (RestorePre .slices)
    (codeRange 0x1005e1 [0x48, 0x81, 0xc4, 0x28, 0x01, 0x00, 0x00,
      0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]) _
  have hAdd : StepEffect (fun s ↦ s.RIP = 0x1005e1)
      (codeRange 0x1005e1 [0x48, 0x81, 0xc4, 0x28, 1, 0, 0])
      (addR64Imm32Effect 0x1005e1 4 296) :=
    add_r64_imm32_effect_step 0x1005e1 0x48 0xc4 296
      (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hPop0 : StepEffect (PopPre (0x1005e1 + 7)) (codeRange (0x1005e1 + 7) [0x5b])
      (popR64Effect (0x1005e1 + 7) 1 3) :=
    pop_r64_effect_step (0x1005e1 + 7) 0x5b (by decide) (by decide)
  have hPop1 : StepEffect (PopPre (0x1005e1 + 8)) (codeRange (0x1005e1 + 8) [0x41, 0x5c])
      (popR64Effect (0x1005e1 + 8) 2 12) :=
    pop_r64_rex_effect_step (0x1005e1 + 8) 0x41 0x5c
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop2 : StepEffect (PopPre (0x1005e1 + 10)) (codeRange (0x1005e1 + 10) [0x41, 0x5d])
      (popR64Effect (0x1005e1 + 10) 2 13) :=
    pop_r64_rex_effect_step (0x1005e1 + 10) 0x41 0x5d
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop3 : StepEffect (PopPre (0x1005e1 + 12)) (codeRange (0x1005e1 + 12) [0x41, 0x5e])
      (popR64Effect (0x1005e1 + 12) 2 14) :=
    pop_r64_rex_effect_step (0x1005e1 + 12) 0x41 0x5e
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop4 : StepEffect (PopPre (0x1005e1 + 14)) (codeRange (0x1005e1 + 14) [0x41, 0x5f])
      (popR64Effect (0x1005e1 + 14) 2 15) :=
    pop_r64_rex_effect_step (0x1005e1 + 14) 0x41 0x5f
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop5 : StepEffect (PopPre (0x1005e1 + 16)) (codeRange (0x1005e1 + 16) [0x5d])
      (popR64Effect (0x1005e1 + 16) 1 5) :=
    pop_r64_effect_step (0x1005e1 + 16) 0x5d (by decide) (by decide)
  md5_run_begin hAdd
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x5e8 (by decide +kernel)
  md5_run_then hPop0
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x5e9 (by decide +kernel)
  md5_run_then hPop1
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x5eb (by decide +kernel)
  md5_run_then hPop2
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x5ed (by decide +kernel)
  md5_run_then hPop3
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x5ef (by decide +kernel)
  md5_run_then hPop4
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x5f1 (by decide +kernel)
  md5_run_then hPop5
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x5f2 (by decide +kernel)
  md5_run_finish [restoreEffect, EpilogueKind.restore, EpilogueKind.frame]
  all_goals
    intro s t hP hH hO
    refine ⟨pop_pre hH (hO true) (by x86_norm) ?_, popR64Effect_avoids _ _ _ _ _⟩
    x86_norm
    first
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 0 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 8 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 16 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 24 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 32 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 40 8 (by decide +kernel)

set_option maxHeartbeats 600000 in
theorem resetSecond_restore [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (RestorePre .resetSecond)
      (codeRange 0x100c98 (EpilogueKind.restoreBytes .resetSecond))
      (restoreEffect .resetSecond) := by
  change AdvancesBlock boundary (RestorePre .resetSecond)
    (codeRange 0x100c98 [0x48, 0x81, 0xc4, 0x48, 0x01, 0x00, 0x00,
      0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]) _
  have hAdd : StepEffect (fun s ↦ s.RIP = 0x100c98)
      (codeRange 0x100c98 [0x48, 0x81, 0xc4, 0x48, 1, 0, 0])
      (addR64Imm32Effect 0x100c98 4 328) :=
    add_r64_imm32_effect_step 0x100c98 0x48 0xc4 328
      (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hPop0 : StepEffect (PopPre (0x100c98 + 7)) (codeRange (0x100c98 + 7) [0x5b])
      (popR64Effect (0x100c98 + 7) 1 3) :=
    pop_r64_effect_step (0x100c98 + 7) 0x5b (by decide) (by decide)
  have hPop1 : StepEffect (PopPre (0x100c98 + 8)) (codeRange (0x100c98 + 8) [0x41, 0x5c])
      (popR64Effect (0x100c98 + 8) 2 12) :=
    pop_r64_rex_effect_step (0x100c98 + 8) 0x41 0x5c
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop2 : StepEffect (PopPre (0x100c98 + 10)) (codeRange (0x100c98 + 10) [0x41, 0x5d])
      (popR64Effect (0x100c98 + 10) 2 13) :=
    pop_r64_rex_effect_step (0x100c98 + 10) 0x41 0x5d
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop3 : StepEffect (PopPre (0x100c98 + 12)) (codeRange (0x100c98 + 12) [0x41, 0x5e])
      (popR64Effect (0x100c98 + 12) 2 14) :=
    pop_r64_rex_effect_step (0x100c98 + 12) 0x41 0x5e
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop4 : StepEffect (PopPre (0x100c98 + 14)) (codeRange (0x100c98 + 14) [0x41, 0x5f])
      (popR64Effect (0x100c98 + 14) 2 15) :=
    pop_r64_rex_effect_step (0x100c98 + 14) 0x41 0x5f
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop5 : StepEffect (PopPre (0x100c98 + 16)) (codeRange (0x100c98 + 16) [0x5d])
      (popR64Effect (0x100c98 + 16) 1 5) :=
    pop_r64_effect_step (0x100c98 + 16) 0x5d (by decide) (by decide)
  md5_run_begin hAdd
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xc9f (by decide +kernel)
  md5_run_then hPop0
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xca0 (by decide +kernel)
  md5_run_then hPop1
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xca2 (by decide +kernel)
  md5_run_then hPop2
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xca4 (by decide +kernel)
  md5_run_then hPop3
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xca6 (by decide +kernel)
  md5_run_then hPop4
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xca8 (by decide +kernel)
  md5_run_then hPop5
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xca9 (by decide +kernel)
  md5_run_finish [restoreEffect, EpilogueKind.restore, EpilogueKind.frame]
  all_goals
    intro s t hP hH hO
    refine ⟨pop_pre hH (hO true) (by x86_norm) ?_, popR64Effect_avoids _ _ _ _ _⟩
    x86_norm
    first
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 0 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 8 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 16 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 24 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 32 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 40 8 (by decide +kernel)

set_option maxHeartbeats 600000 in
theorem finalizeResetSecond_restore [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (RestorePre .finalizeResetSecond)
      (codeRange 0x101328 (EpilogueKind.restoreBytes .finalizeResetSecond))
      (restoreEffect .finalizeResetSecond) := by
  change AdvancesBlock boundary (RestorePre .finalizeResetSecond)
    (codeRange 0x101328 [0x48, 0x81, 0xc4, 0x38, 0x01, 0x00, 0x00,
      0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]) _
  have hAdd : StepEffect (fun s ↦ s.RIP = 0x101328)
      (codeRange 0x101328 [0x48, 0x81, 0xc4, 0x38, 1, 0, 0])
      (addR64Imm32Effect 0x101328 4 312) :=
    add_r64_imm32_effect_step 0x101328 0x48 0xc4 312
      (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hPop0 : StepEffect (PopPre (0x101328 + 7)) (codeRange (0x101328 + 7) [0x5b])
      (popR64Effect (0x101328 + 7) 1 3) :=
    pop_r64_effect_step (0x101328 + 7) 0x5b (by decide) (by decide)
  have hPop1 : StepEffect (PopPre (0x101328 + 8)) (codeRange (0x101328 + 8) [0x41, 0x5c])
      (popR64Effect (0x101328 + 8) 2 12) :=
    pop_r64_rex_effect_step (0x101328 + 8) 0x41 0x5c
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop2 : StepEffect (PopPre (0x101328 + 10)) (codeRange (0x101328 + 10) [0x41, 0x5d])
      (popR64Effect (0x101328 + 10) 2 13) :=
    pop_r64_rex_effect_step (0x101328 + 10) 0x41 0x5d
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop3 : StepEffect (PopPre (0x101328 + 12)) (codeRange (0x101328 + 12) [0x41, 0x5e])
      (popR64Effect (0x101328 + 12) 2 14) :=
    pop_r64_rex_effect_step (0x101328 + 12) 0x41 0x5e
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop4 : StepEffect (PopPre (0x101328 + 14)) (codeRange (0x101328 + 14) [0x41, 0x5f])
      (popR64Effect (0x101328 + 14) 2 15) :=
    pop_r64_rex_effect_step (0x101328 + 14) 0x41 0x5f
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop5 : StepEffect (PopPre (0x101328 + 16)) (codeRange (0x101328 + 16) [0x5d])
      (popR64Effect (0x101328 + 16) 1 5) :=
    pop_r64_effect_step (0x101328 + 16) 0x5d (by decide) (by decide)
  md5_run_begin hAdd
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x132f (by decide +kernel)
  md5_run_then hPop0
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1330 (by decide +kernel)
  md5_run_then hPop1
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1332 (by decide +kernel)
  md5_run_then hPop2
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1334 (by decide +kernel)
  md5_run_then hPop3
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1336 (by decide +kernel)
  md5_run_then hPop4
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1338 (by decide +kernel)
  md5_run_then hPop5
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1339 (by decide +kernel)
  md5_run_finish [restoreEffect, EpilogueKind.restore, EpilogueKind.frame]
  all_goals
    intro s t hP hH hO
    refine ⟨pop_pre hH (hO true) (by x86_norm) ?_, popR64Effect_avoids _ _ _ _ _⟩
    x86_norm
    first
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 0 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 8 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 16 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 24 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 32 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 40 8 (by decide +kernel)

set_option maxHeartbeats 600000 in
theorem resetDiscardSecond_restore [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (RestorePre .resetDiscardSecond)
      (codeRange 0x101825 (EpilogueKind.restoreBytes .resetDiscardSecond))
      (restoreEffect .resetDiscardSecond) := by
  change AdvancesBlock boundary (RestorePre .resetDiscardSecond)
    (codeRange 0x101825 [0x48, 0x81, 0xc4, 0x38, 0x01, 0x00, 0x00,
      0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]) _
  have hAdd : StepEffect (fun s ↦ s.RIP = 0x101825)
      (codeRange 0x101825 [0x48, 0x81, 0xc4, 0x38, 1, 0, 0])
      (addR64Imm32Effect 0x101825 4 312) :=
    add_r64_imm32_effect_step 0x101825 0x48 0xc4 312
      (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hPop0 : StepEffect (PopPre (0x101825 + 7)) (codeRange (0x101825 + 7) [0x5b])
      (popR64Effect (0x101825 + 7) 1 3) :=
    pop_r64_effect_step (0x101825 + 7) 0x5b (by decide) (by decide)
  have hPop1 : StepEffect (PopPre (0x101825 + 8)) (codeRange (0x101825 + 8) [0x41, 0x5c])
      (popR64Effect (0x101825 + 8) 2 12) :=
    pop_r64_rex_effect_step (0x101825 + 8) 0x41 0x5c
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop2 : StepEffect (PopPre (0x101825 + 10)) (codeRange (0x101825 + 10) [0x41, 0x5d])
      (popR64Effect (0x101825 + 10) 2 13) :=
    pop_r64_rex_effect_step (0x101825 + 10) 0x41 0x5d
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop3 : StepEffect (PopPre (0x101825 + 12)) (codeRange (0x101825 + 12) [0x41, 0x5e])
      (popR64Effect (0x101825 + 12) 2 14) :=
    pop_r64_rex_effect_step (0x101825 + 12) 0x41 0x5e
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop4 : StepEffect (PopPre (0x101825 + 14)) (codeRange (0x101825 + 14) [0x41, 0x5f])
      (popR64Effect (0x101825 + 14) 2 15) :=
    pop_r64_rex_effect_step (0x101825 + 14) 0x41 0x5f
      (by unfold RexPrefix; decide) (by decide) (by decide)
  have hPop5 : StepEffect (PopPre (0x101825 + 16)) (codeRange (0x101825 + 16) [0x5d])
      (popR64Effect (0x101825 + 16) 1 5) :=
    pop_r64_effect_step (0x101825 + 16) 0x5d (by decide) (by decide)
  md5_run_begin hAdd
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x182c (by decide +kernel)
  md5_run_then hPop0
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x182d (by decide +kernel)
  md5_run_then hPop1
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x182f (by decide +kernel)
  md5_run_then hPop2
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1831 (by decide +kernel)
  md5_run_then hPop3
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1833 (by decide +kernel)
  md5_run_then hPop4
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1835 (by decide +kernel)
  md5_run_then hPop5
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1836 (by decide +kernel)
  md5_run_finish [restoreEffect, EpilogueKind.restore, EpilogueKind.frame]
  all_goals
    intro s t hP hH hO
    refine ⟨pop_pre hH (hO true) (by x86_norm) ?_, popR64Effect_avoids _ _ _ _ _⟩
    x86_norm
    first
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 0 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 8 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 16 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 24 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 32 8 (by decide +kernel)
      | simpa [stackPtr, Operand.read_reg64, gprIndex, BitVec.add_assoc,
          BitVec.reduceAdd, EpilogueKind.frame] using
          MemoryRoutines.memReadable_slice hP.read 40 8 (by decide +kernel)

private theorem writableRange_write {s : RamState} {a : BitVec 64} {n : Nat}
    (h : MemoryRoutines.WritableRange s a n) : Memory.MemWritable s a n :=
  ⟨h.readable.low, h.readable.mem, h.tables⟩

private theorem writableRange_textApart {s : RamState} {a : BitVec 64} {n : Nat}
    (h : MemoryRoutines.WritableRange s a n) (offset count : Nat)
    (hbound : offset + count ≤ Extracted.textBytes.size) :
    RangeApart a n (Extracted.textAddress + BitVec.ofNat 64 offset) count := by
  intro i hi j hj he
  apply h.code i hi
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program (offset + j) (by omega)

structure PreparePre (kind : EpilogueKind) (s : RamState) : Prop where
  rip : s.RIP = kind.entry
  read : MemReadable s (stackPtr s) (kind.frame + 56)
  scratch : MemoryRoutines.WritableRange s
    (stackPtr s + BitVec.ofNat 64 (kind.frame - 16)) 16

def prepareEffect (kind : EpilogueKind) (s : RamState) : Effect :=
  if kind = .updateFinalizeInto then NewEntries.UpdateFinalize.Epilogue.prepareEffect s else {
  rip := match kind with
    | .slices => 0x1005da
    | .updateFinalizeInto => 0x101b7a
    | .resetSecond => 0x100c90
    | .finalizeResetSecond => 0x101320
    | .resetDiscardSecond => 0x10181e
  writes :=
    [⟨(.reg 0 : Operand 64),
      (Operand.mem (stackPtr s + BitVec.ofNat 64 kind.source) : Operand 64).read s⟩,
     ⟨(.reg 1 : Operand 64),
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.source + 8)) : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s + BitVec.ofNat 64 (kind.frame - 16)) : Operand 64),
      (Operand.mem (stackPtr s + BitVec.ofNat 64 kind.source) : Operand 64).read s⟩,
     ⟨(.mem (stackPtr s + BitVec.ofNat 64 (kind.frame - 8)) : Operand 64),
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.source + 8)) : Operand 64).read s⟩,
     ⟨(.reg 2 : Operand 64),
      (Operand.mem (stackPtr s + BitVec.ofNat 64 kind.outputSlot) : Operand 64).read s⟩] }

private theorem prepare_registers {kind : EpilogueKind} {s t : RamState}
    (h : (prepareEffect kind s).Holds s t) :
    (Operand.reg 0 : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 kind.source) : Operand 64).read s ∧
    (Operand.reg 1 : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.source + 8)) : Operand 64).read s ∧
    (Operand.reg 2 : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 kind.outputSlot) : Operand 64).read s := by
  cases kind with
  | updateFinalizeInto =>
    refine ⟨?_, ?_, h.writes.2.2⟩
    · simpa only [EpilogueKind.source, BitVec.add_zero] using h.writes.1
    · exact h.writes.2.1
  | slices | resetSecond | finalizeResetSecond | resetDiscardSecond =>
    exact ⟨h.writes.1, h.writes.2.1, h.writes.2.2.2.2⟩

private theorem prepare_components {kind : EpilogueKind} {s : RamState} {c : Component}
    (h : c ∈ (prepareEffect kind s).components) :
    c ∈ [.reg 0, .reg 1, .mem (stackPtr s + BitVec.ofNat 64 (kind.frame - 16)) 8,
      .mem (stackPtr s + BitVec.ofNat 64 (kind.frame - 8)) 8, .reg 2, .rip] := by
  cases kind <;>
    simp_all [prepareEffect, NewEntries.UpdateFinalize.Epilogue.prepareEffect,
      Effect.components, Write.component, Operand.component]
  rcases h with h | h | h | h <;> simp_all

def slicesPrepareBytes : List UInt8 :=
  [0x48, 0x8b, 0x4, 0x24, 0x48, 0x8b, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x84,
    0x24, 0x18, 0x1, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0x20, 0x1, 0x0,
    0x0, 0x48, 0x8b, 0x94, 0x24, 0xa8, 0x0, 0x0, 0x0]

set_option maxHeartbeats 800000 in
theorem slices_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PreparePre .slices) (codeRange 0x1005b9 slicesPrepareBytes)
      (prepareEffect .slices) := by
  unfold slicesPrepareBytes
  have h0 : StepEffect
      (LoadPre 0x1005b9 (storeAddrAt 0x1005b9 (.sib 4 none 0 .none) 4) 8)
      (codeRange 0x1005b9 [ 0x48, 0x8b, 0x4, 0x24 ])
      (movR64M64Effect 0x1005b9 0 (.sib 4 none 0 .none)) :=
    mov_r64_m64_effect_step 0x1005b9 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 .none) (by decide) (by decide) (by decide)
  have h1 : StepEffect
      (LoadPre (0x1005b9 + 4) (storeAddrAt (0x1005b9 + 4) (.sib 4 none 0 (.d8 8)) 5) 8)
      (codeRange (0x1005b9 + 4) [ 0x48, 0x8b, 0x4c, 0x24, 0x8 ])
      (movR64M64Effect (0x1005b9 + 4) 1 (.sib 4 none 0 (.d8 8))) :=
    mov_r64_m64_effect_step (0x1005b9 + 4) 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide)
  have h2 : StepEffect (Memory.StorePre (0x1005b9 + 9) 8
      (storeAddrAt (0x1005b9 + 9) (.sib 4 none 0 (.d32 280)) 8) 8)
      (codeRange (0x1005b9 + 9) [ 0x48, 0x89, 0x84, 0x24, 0x18, 0x1, 0x0, 0x0 ])
      (movM64R64Effect (0x1005b9 + 9) 0 (.sib 4 none 0 (.d32 280))) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x1005b9 + 9) 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d32 280)) (by decide) (by decide) (by decide)
  have h3 : StepEffect (Memory.StorePre (0x1005b9 + 17) 8
      (storeAddrAt (0x1005b9 + 17) (.sib 4 none 0 (.d32 288)) 8) 8)
      (codeRange (0x1005b9 + 17) [ 0x48, 0x89, 0x8c, 0x24, 0x20, 0x1, 0x0, 0x0 ])
      (movM64R64Effect (0x1005b9 + 17) 1 (.sib 4 none 0 (.d32 288))) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x1005b9 + 17) 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d32 288)) (by decide) (by decide) (by decide)
  have h4 : StepEffect
      (LoadPre (0x1005b9 + 25) (storeAddrAt (0x1005b9 + 25) (.sib 4 none 0 (.d32 168)) 8) 8)
      (codeRange (0x1005b9 + 25) [ 0x48, 0x8b, 0x94, 0x24, 0xa8, 0x0, 0x0, 0x0 ])
      (movR64M64Effect (0x1005b9 + 25) 2 (.sib 4 none 0 (.d32 168))) :=
    mov_r64_m64_effect_step (0x1005b9 + 25) 0x48 (by unfold RexWPrefix; decide) 2
      (.sib 4 none 0 (.d32 168)) (by decide) (by decide) (by decide)
  md5_run_begin h0
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using
      MemoryRoutines.memReadable_slice h.read 0 8 (by decide)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x5bd (by decide +kernel)
  md5_run_then h1
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      simpa [stackPtr, EpilogueKind.frame] using
        MemoryRoutines.memReadable_slice h.read 8 8 (by decide)
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x5c2 (by decide +kernel)
  md5_run_then h2
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc] using
          writableRange_write (h.scratch.slice 0 8 (by decide))
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
          writableRange_textApart (h.scratch.slice 0 8 (by decide))
            0x5c2 8 (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.scratch.slice 0 8 (by decide))
          0x5b9 33 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x5ca (by decide +kernel)
  md5_run_then h3
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc] using
          writableRange_write (h.scratch.slice 8 8 (by decide))
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
          writableRange_textApart (h.scratch.slice 8 8 (by decide))
            0x5ca 8 (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.scratch.slice 8 8 (by decide))
          0x5b9 33 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x5d2 (by decide +kernel)
  md5_run_then h4
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      simpa [stackPtr, EpilogueKind.frame] using
        MemoryRoutines.memReadable_slice h.read 168 8 (by decide)
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x5da (by decide +kernel)
  md5_run_finish [prepareEffect, EpilogueKind.source, EpilogueKind.frame,
    EpilogueKind.outputSlot, BitVec.add_zero]

def resetSecondPrepareBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xd8, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24,
    0xe0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x38, 0x1, 0x0, 0x0,
    0x48, 0x89, 0x8c, 0x24, 0x40, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x94, 0x24,
    0xb8, 0x0, 0x0, 0x0]

set_option maxHeartbeats 800000 in
theorem resetSecond_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PreparePre .resetSecond) (codeRange 0x100c68 resetSecondPrepareBytes)
      (prepareEffect .resetSecond) := by
  unfold resetSecondPrepareBytes
  have h0 : StepEffect
      (LoadPre 0x100c68 (storeAddrAt 0x100c68 (.sib 4 none 0 (.d32 216)) 8) 8)
      (codeRange 0x100c68 [ 0x48, 0x8b, 0x84, 0x24, 0xd8, 0x0, 0x0, 0x0 ])
      (movR64M64Effect 0x100c68 0 (.sib 4 none 0 (.d32 216))) :=
    mov_r64_m64_effect_step 0x100c68 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d32 216)) (by decide) (by decide) (by decide)
  have h1 : StepEffect
      (LoadPre (0x100c68 + 8) (storeAddrAt (0x100c68 + 8) (.sib 4 none 0 (.d32 224)) 8) 8)
      (codeRange (0x100c68 + 8) [ 0x48, 0x8b, 0x8c, 0x24, 0xe0, 0x0, 0x0, 0x0 ])
      (movR64M64Effect (0x100c68 + 8) 1 (.sib 4 none 0 (.d32 224))) :=
    mov_r64_m64_effect_step (0x100c68 + 8) 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d32 224)) (by decide) (by decide) (by decide)
  have h2 : StepEffect (Memory.StorePre (0x100c68 + 16) 8
      (storeAddrAt (0x100c68 + 16) (.sib 4 none 0 (.d32 312)) 8) 8)
      (codeRange (0x100c68 + 16) [ 0x48, 0x89, 0x84, 0x24, 0x38, 0x1, 0x0, 0x0 ])
      (movM64R64Effect (0x100c68 + 16) 0 (.sib 4 none 0 (.d32 312))) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x100c68 + 16) 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d32 312)) (by decide) (by decide) (by decide)
  have h3 : StepEffect (Memory.StorePre (0x100c68 + 24) 8
      (storeAddrAt (0x100c68 + 24) (.sib 4 none 0 (.d32 320)) 8) 8)
      (codeRange (0x100c68 + 24) [ 0x48, 0x89, 0x8c, 0x24, 0x40, 0x1, 0x0, 0x0 ])
      (movM64R64Effect (0x100c68 + 24) 1 (.sib 4 none 0 (.d32 320))) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x100c68 + 24) 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d32 320)) (by decide) (by decide) (by decide)
  have h4 : StepEffect
      (LoadPre (0x100c68 + 32) (storeAddrAt (0x100c68 + 32) (.sib 4 none 0 (.d32 184)) 8) 8)
      (codeRange (0x100c68 + 32) [ 0x48, 0x8b, 0x94, 0x24, 0xb8, 0x0, 0x0, 0x0 ])
      (movR64M64Effect (0x100c68 + 32) 2 (.sib 4 none 0 (.d32 184))) :=
    mov_r64_m64_effect_step (0x100c68 + 32) 0x48 (by unfold RexWPrefix; decide) 2
      (.sib 4 none 0 (.d32 184)) (by decide) (by decide) (by decide)
  md5_run_begin h0
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using
      MemoryRoutines.memReadable_slice h.read 216 8 (by decide)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xc70 (by decide +kernel)
  md5_run_then h1
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      simpa [stackPtr, EpilogueKind.frame] using
        MemoryRoutines.memReadable_slice h.read 224 8 (by decide)
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xc78 (by decide +kernel)
  md5_run_then h2
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc] using
          writableRange_write (h.scratch.slice 0 8 (by decide))
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
          writableRange_textApart (h.scratch.slice 0 8 (by decide))
            0xc78 8 (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.scratch.slice 0 8 (by decide))
          0xc68 40 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xc80 (by decide +kernel)
  md5_run_then h3
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc] using
          writableRange_write (h.scratch.slice 8 8 (by decide))
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
          writableRange_textApart (h.scratch.slice 8 8 (by decide))
            0xc80 8 (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.scratch.slice 8 8 (by decide))
          0xc68 40 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xc88 (by decide +kernel)
  md5_run_then h4
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      simpa [stackPtr, EpilogueKind.frame] using
        MemoryRoutines.memReadable_slice h.read 184 8 (by decide)
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xc90 (by decide +kernel)
  md5_run_finish [prepareEffect, EpilogueKind.source, EpilogueKind.frame,
    EpilogueKind.outputSlot, BitVec.add_zero]

def finalizeResetSecondPrepareBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xd8, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24,
    0xe0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x28, 0x1, 0x0, 0x0,
    0x48, 0x89, 0x8c, 0x24, 0x30, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x94, 0x24,
    0xb8, 0x0, 0x0, 0x0]

set_option maxHeartbeats 800000 in
theorem finalizeResetSecond_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PreparePre .finalizeResetSecond) (codeRange 0x1012f8 finalizeResetSecondPrepareBytes)
      (prepareEffect .finalizeResetSecond) := by
  unfold finalizeResetSecondPrepareBytes
  have h0 : StepEffect
      (LoadPre 0x1012f8 (storeAddrAt 0x1012f8 (.sib 4 none 0 (.d32 216)) 8) 8)
      (codeRange 0x1012f8 [ 0x48, 0x8b, 0x84, 0x24, 0xd8, 0x0, 0x0, 0x0 ])
      (movR64M64Effect 0x1012f8 0 (.sib 4 none 0 (.d32 216))) :=
    mov_r64_m64_effect_step 0x1012f8 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d32 216)) (by decide) (by decide) (by decide)
  have h1 : StepEffect
      (LoadPre (0x1012f8 + 8) (storeAddrAt (0x1012f8 + 8) (.sib 4 none 0 (.d32 224)) 8) 8)
      (codeRange (0x1012f8 + 8) [ 0x48, 0x8b, 0x8c, 0x24, 0xe0, 0x0, 0x0, 0x0 ])
      (movR64M64Effect (0x1012f8 + 8) 1 (.sib 4 none 0 (.d32 224))) :=
    mov_r64_m64_effect_step (0x1012f8 + 8) 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d32 224)) (by decide) (by decide) (by decide)
  have h2 : StepEffect (Memory.StorePre (0x1012f8 + 16) 8
      (storeAddrAt (0x1012f8 + 16) (.sib 4 none 0 (.d32 296)) 8) 8)
      (codeRange (0x1012f8 + 16) [ 0x48, 0x89, 0x84, 0x24, 0x28, 0x1, 0x0, 0x0 ])
      (movM64R64Effect (0x1012f8 + 16) 0 (.sib 4 none 0 (.d32 296))) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x1012f8 + 16) 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d32 296)) (by decide) (by decide) (by decide)
  have h3 : StepEffect (Memory.StorePre (0x1012f8 + 24) 8
      (storeAddrAt (0x1012f8 + 24) (.sib 4 none 0 (.d32 304)) 8) 8)
      (codeRange (0x1012f8 + 24) [ 0x48, 0x89, 0x8c, 0x24, 0x30, 0x1, 0x0, 0x0 ])
      (movM64R64Effect (0x1012f8 + 24) 1 (.sib 4 none 0 (.d32 304))) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x1012f8 + 24) 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d32 304)) (by decide) (by decide) (by decide)
  have h4 : StepEffect
      (LoadPre (0x1012f8 + 32) (storeAddrAt (0x1012f8 + 32) (.sib 4 none 0 (.d32 184)) 8) 8)
      (codeRange (0x1012f8 + 32) [ 0x48, 0x8b, 0x94, 0x24, 0xb8, 0x0, 0x0, 0x0 ])
      (movR64M64Effect (0x1012f8 + 32) 2 (.sib 4 none 0 (.d32 184))) :=
    mov_r64_m64_effect_step (0x1012f8 + 32) 0x48 (by unfold RexWPrefix; decide) 2
      (.sib 4 none 0 (.d32 184)) (by decide) (by decide) (by decide)
  md5_run_begin h0
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using
      MemoryRoutines.memReadable_slice h.read 216 8 (by decide)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1300 (by decide +kernel)
  md5_run_then h1
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      simpa [stackPtr, EpilogueKind.frame] using
        MemoryRoutines.memReadable_slice h.read 224 8 (by decide)
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1308 (by decide +kernel)
  md5_run_then h2
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc] using
          writableRange_write (h.scratch.slice 0 8 (by decide))
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
          writableRange_textApart (h.scratch.slice 0 8 (by decide))
            0x1308 8 (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.scratch.slice 0 8 (by decide))
          0x12f8 40 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1310 (by decide +kernel)
  md5_run_then h3
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc] using
          writableRange_write (h.scratch.slice 8 8 (by decide))
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
          writableRange_textApart (h.scratch.slice 8 8 (by decide))
            0x1310 8 (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.scratch.slice 8 8 (by decide))
          0x12f8 40 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1318 (by decide +kernel)
  md5_run_then h4
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      simpa [stackPtr, EpilogueKind.frame] using
        MemoryRoutines.memReadable_slice h.read 184 8 (by decide)
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1320 (by decide +kernel)
  md5_run_finish [prepareEffect, EpilogueKind.source, EpilogueKind.frame,
    EpilogueKind.outputSlot, BitVec.add_zero]

def resetDiscardSecondPrepareBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x78, 0x48, 0x8b, 0x8c, 0x24,
    0x80, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x28, 0x1, 0x0, 0x0,
    0x48, 0x89, 0x8c, 0x24, 0x30, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x94, 0x24,
    0x20, 0x1, 0x0, 0x0]

set_option maxHeartbeats 800000 in
theorem resetDiscardSecond_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PreparePre .resetDiscardSecond) (codeRange 0x1017f9 resetDiscardSecondPrepareBytes)
      (prepareEffect .resetDiscardSecond) := by
  unfold resetDiscardSecondPrepareBytes
  have h0 : StepEffect
      (LoadPre 0x1017f9 (storeAddrAt 0x1017f9 (.sib 4 none 0 (.d8 120)) 5) 8)
      (codeRange 0x1017f9 [ 0x48, 0x8b, 0x44, 0x24, 0x78 ])
      (movR64M64Effect 0x1017f9 0 (.sib 4 none 0 (.d8 120))) :=
    mov_r64_m64_effect_step 0x1017f9 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 120)) (by decide) (by decide) (by decide)
  have h1 : StepEffect
      (LoadPre (0x1017f9 + 5) (storeAddrAt (0x1017f9 + 5) (.sib 4 none 0 (.d32 128)) 8) 8)
      (codeRange (0x1017f9 + 5) [ 0x48, 0x8b, 0x8c, 0x24, 0x80, 0x0, 0x0, 0x0 ])
      (movR64M64Effect (0x1017f9 + 5) 1 (.sib 4 none 0 (.d32 128))) :=
    mov_r64_m64_effect_step (0x1017f9 + 5) 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d32 128)) (by decide) (by decide) (by decide)
  have h2 : StepEffect (Memory.StorePre (0x1017f9 + 13) 8
      (storeAddrAt (0x1017f9 + 13) (.sib 4 none 0 (.d32 296)) 8) 8)
      (codeRange (0x1017f9 + 13) [ 0x48, 0x89, 0x84, 0x24, 0x28, 0x1, 0x0, 0x0 ])
      (movM64R64Effect (0x1017f9 + 13) 0 (.sib 4 none 0 (.d32 296))) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x1017f9 + 13) 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d32 296)) (by decide) (by decide) (by decide)
  have h3 : StepEffect (Memory.StorePre (0x1017f9 + 21) 8
      (storeAddrAt (0x1017f9 + 21) (.sib 4 none 0 (.d32 304)) 8) 8)
      (codeRange (0x1017f9 + 21) [ 0x48, 0x89, 0x8c, 0x24, 0x30, 0x1, 0x0, 0x0 ])
      (movM64R64Effect (0x1017f9 + 21) 1 (.sib 4 none 0 (.d32 304))) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x1017f9 + 21) 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d32 304)) (by decide) (by decide) (by decide)
  have h4 : StepEffect
      (LoadPre (0x1017f9 + 29) (storeAddrAt (0x1017f9 + 29) (.sib 4 none 0 (.d32 288)) 8) 8)
      (codeRange (0x1017f9 + 29) [ 0x48, 0x8b, 0x94, 0x24, 0x20, 0x1, 0x0, 0x0 ])
      (movR64M64Effect (0x1017f9 + 29) 2 (.sib 4 none 0 (.d32 288))) :=
    mov_r64_m64_effect_step (0x1017f9 + 29) 0x48 (by unfold RexWPrefix; decide) 2
      (.sib 4 none 0 (.d32 288)) (by decide) (by decide) (by decide)
  md5_run_begin h0
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using
      MemoryRoutines.memReadable_slice h.read 120 8 (by decide)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x17fe (by decide +kernel)
  md5_run_then h1
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      simpa [stackPtr, EpilogueKind.frame] using
        MemoryRoutines.memReadable_slice h.read 128 8 (by decide)
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1806 (by decide +kernel)
  md5_run_then h2
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc] using
          writableRange_write (h.scratch.slice 0 8 (by decide))
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
          writableRange_textApart (h.scratch.slice 0 8 (by decide))
            0x1806 8 (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.scratch.slice 0 8 (by decide))
          0x17f9 37 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x180e (by decide +kernel)
  md5_run_then h3
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc] using
          writableRange_write (h.scratch.slice 8 8 (by decide))
      · x86_norm
        simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
          writableRange_textApart (h.scratch.slice 8 8 (by decide))
            0x180e 8 (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [stackPtr, EpilogueKind.frame, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.scratch.slice 8 8 (by decide))
          0x17f9 37 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1816 (by decide +kernel)
  md5_run_then h4
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine LoadPre.of_holds hE (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      simpa [stackPtr, EpilogueKind.frame] using
        MemoryRoutines.memReadable_slice h.read 288 8 (by decide)
    · x86_avoid
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x181e (by decide +kernel)
  md5_run_finish [prepareEffect, EpilogueKind.source, EpilogueKind.frame,
    EpilogueKind.outputSlot, BitVec.add_zero]

def epilogueOutput (kind : EpilogueKind) (s : RamState) : BitVec 64 :=
  (Operand.reg 2 : Operand 64).read s + BitVec.ofNat 64 kind.outputOffset

structure OutputPre (kind : EpilogueKind) (s : RamState) : Prop where
  rip : s.RIP = (prepareEffect kind s).rip
  write : MemoryRoutines.WritableRange s (epilogueOutput kind s) 16

def outputEffect (kind : EpilogueKind) (s : RamState) : Effect where
  rip := kind.restore
  writes :=
    [⟨(.mem (epilogueOutput kind s + 8) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
     ⟨(.mem (epilogueOutput kind s) : Operand 64), (Operand.reg 0 : Operand 64).read s⟩]

def slicesOutputBytes : List UInt8 := [0x48, 0x89, 0x4a, 0x8, 0x48, 0x89, 0x2]

set_option maxHeartbeats 400000 in
theorem slices_output [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (OutputPre .slices) (codeRange 0x1005da slicesOutputBytes)
      (outputEffect .slices) := by
  unfold slicesOutputBytes
  have h0 : StepEffect (Memory.StorePre 0x1005da 4
      (storeAddrAt 0x1005da (.base 2 (.d8 8)) 4) 8)
      (codeRange 0x1005da [0x48, 0x89, 0x4a, 0x8])
      (movM64R64Effect 0x1005da 1 (.base 2 (.d8 8))) :=
    Buffered.Stores.mov_m64_r64_effect_step 0x1005da 0x48 (by unfold RexWPrefix; decide) 1
      (.base 2 (.d8 8)) (by decide) (by decide) (by decide)
  have h1 : StepEffect (Memory.StorePre (0x1005da + 4) 3
      (storeAddrAt (0x1005da + 4) (.base 2 .none) 3) 8)
      (codeRange (0x1005da + 4) [0x48, 0x89, 0x2])
      (movM64R64Effect (0x1005da + 4) 0 (.base 2 .none)) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x1005da + 4) 0x48 (by unfold RexWPrefix; decide) 0
      (.base 2 .none) (by decide) (by decide) (by decide)
  refine AdvancesBlock.block_first ?k h0 (by x86_sub) ?pre ?av ?boundary
  case' k => x86_norm
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, epilogueOutput,
        EpilogueKind.outputOffset, BitVec.add_assoc] using
        writableRange_write (h.write.slice 8 8 (by decide))
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, epilogueOutput,
        EpilogueKind.outputOffset, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.write.slice 8 8 (by decide)) 0x5da 4
          (by decide +kernel)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa [epilogueOutput, EpilogueKind.outputOffset, BitVec.add_assoc, Extracted.textAddress] using
      writableRange_textApart (h.write.slice 8 8 (by decide)) 0x5da 7
        (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x5de (by decide +kernel)
  refine AdvancesBlock.block_then ?copyEnd h1 (by x86_local) (by x86_sub)
    (by x86_full) ?mid ?boundary2
  case' copyEnd => x86_norm
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [epilogueOutput, EpilogueKind.outputOffset] using
          writableRange_write (h.write.slice 0 8 (by decide))
      · x86_norm
        simpa [epilogueOutput, EpilogueKind.outputOffset, Extracted.textAddress] using
          writableRange_textApart (h.write.slice 0 8 (by decide)) 0x5de 3
            (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [epilogueOutput, EpilogueKind.outputOffset, Extracted.textAddress] using
        writableRange_textApart (h.write.slice 0 8 (by decide)) 0x5da 7
          (by decide +kernel)
  case boundary2 =>
    intro _ _
    exact text_address_ne_return hOutside 0x5e1 (by decide +kernel)
  md5_run_finish [outputEffect, epilogueOutput, EpilogueKind.restore,
    EpilogueKind.outputOffset, BitVec.add_zero]

def resetSecondOutputBytes : List UInt8 := [0x48, 0x89, 0x4a, 0x18, 0x48, 0x89, 0x42, 0x10]

set_option maxHeartbeats 400000 in
theorem resetSecond_output [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (OutputPre .resetSecond) (codeRange 0x100c90 resetSecondOutputBytes)
      (outputEffect .resetSecond) := by
  unfold resetSecondOutputBytes
  have h0 : StepEffect (Memory.StorePre 0x100c90 4
      (storeAddrAt 0x100c90 (.base 2 (.d8 24)) 4) 8)
      (codeRange 0x100c90 [0x48, 0x89, 0x4a, 0x18])
      (movM64R64Effect 0x100c90 1 (.base 2 (.d8 24))) :=
    Buffered.Stores.mov_m64_r64_effect_step 0x100c90 0x48 (by unfold RexWPrefix; decide) 1
      (.base 2 (.d8 24)) (by decide) (by decide) (by decide)
  have h1 : StepEffect (Memory.StorePre (0x100c90 + 4) 4
      (storeAddrAt (0x100c90 + 4) (.base 2 (.d8 16)) 4) 8)
      (codeRange (0x100c90 + 4) [0x48, 0x89, 0x42, 0x10])
      (movM64R64Effect (0x100c90 + 4) 0 (.base 2 (.d8 16))) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x100c90 + 4) 0x48 (by unfold RexWPrefix; decide) 0
      (.base 2 (.d8 16)) (by decide) (by decide) (by decide)
  refine AdvancesBlock.block_first ?k h0 (by x86_sub) ?pre ?av ?boundary
  case' k => x86_norm
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, epilogueOutput,
        EpilogueKind.outputOffset, BitVec.add_assoc] using
        writableRange_write (h.write.slice 8 8 (by decide))
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, epilogueOutput,
        EpilogueKind.outputOffset, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.write.slice 8 8 (by decide)) 0xc90 4
          (by decide +kernel)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa [epilogueOutput, EpilogueKind.outputOffset, BitVec.add_assoc, Extracted.textAddress] using
      writableRange_textApart (h.write.slice 8 8 (by decide)) 0xc90 8
        (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xc94 (by decide +kernel)
  refine AdvancesBlock.block_then ?copyEnd h1 (by x86_local) (by x86_sub)
    (by x86_full) ?mid ?boundary2
  case' copyEnd => x86_norm
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [epilogueOutput, EpilogueKind.outputOffset] using
          writableRange_write (h.write.slice 0 8 (by decide))
      · x86_norm
        simpa [epilogueOutput, EpilogueKind.outputOffset, Extracted.textAddress] using
          writableRange_textApart (h.write.slice 0 8 (by decide)) 0xc94 4
            (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [epilogueOutput, EpilogueKind.outputOffset, Extracted.textAddress] using
        writableRange_textApart (h.write.slice 0 8 (by decide)) 0xc90 8
          (by decide +kernel)
  case boundary2 =>
    intro _ _
    exact text_address_ne_return hOutside 0xc98 (by decide +kernel)
  md5_run_finish [outputEffect, epilogueOutput, EpilogueKind.restore,
    EpilogueKind.outputOffset, BitVec.add_zero]

def finalizeResetSecondOutputBytes : List UInt8 := [0x48, 0x89, 0x4a, 0x18, 0x48, 0x89, 0x42, 0x10]

set_option maxHeartbeats 400000 in
theorem finalizeResetSecond_output [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (OutputPre .finalizeResetSecond) (codeRange 0x101320 finalizeResetSecondOutputBytes)
      (outputEffect .finalizeResetSecond) := by
  unfold finalizeResetSecondOutputBytes
  have h0 : StepEffect (Memory.StorePre 0x101320 4
      (storeAddrAt 0x101320 (.base 2 (.d8 24)) 4) 8)
      (codeRange 0x101320 [0x48, 0x89, 0x4a, 0x18])
      (movM64R64Effect 0x101320 1 (.base 2 (.d8 24))) :=
    Buffered.Stores.mov_m64_r64_effect_step 0x101320 0x48 (by unfold RexWPrefix; decide) 1
      (.base 2 (.d8 24)) (by decide) (by decide) (by decide)
  have h1 : StepEffect (Memory.StorePre (0x101320 + 4) 4
      (storeAddrAt (0x101320 + 4) (.base 2 (.d8 16)) 4) 8)
      (codeRange (0x101320 + 4) [0x48, 0x89, 0x42, 0x10])
      (movM64R64Effect (0x101320 + 4) 0 (.base 2 (.d8 16))) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x101320 + 4) 0x48 (by unfold RexWPrefix; decide) 0
      (.base 2 (.d8 16)) (by decide) (by decide) (by decide)
  refine AdvancesBlock.block_first ?k h0 (by x86_sub) ?pre ?av ?boundary
  case' k => x86_norm
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, epilogueOutput,
        EpilogueKind.outputOffset, BitVec.add_assoc] using
        writableRange_write (h.write.slice 8 8 (by decide))
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, epilogueOutput,
        EpilogueKind.outputOffset, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.write.slice 8 8 (by decide)) 0x1320 4
          (by decide +kernel)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa [epilogueOutput, EpilogueKind.outputOffset, BitVec.add_assoc, Extracted.textAddress] using
      writableRange_textApart (h.write.slice 8 8 (by decide)) 0x1320 8
        (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1324 (by decide +kernel)
  refine AdvancesBlock.block_then ?copyEnd h1 (by x86_local) (by x86_sub)
    (by x86_full) ?mid ?boundary2
  case' copyEnd => x86_norm
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [epilogueOutput, EpilogueKind.outputOffset] using
          writableRange_write (h.write.slice 0 8 (by decide))
      · x86_norm
        simpa [epilogueOutput, EpilogueKind.outputOffset, Extracted.textAddress] using
          writableRange_textApart (h.write.slice 0 8 (by decide)) 0x1324 4
            (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [epilogueOutput, EpilogueKind.outputOffset, Extracted.textAddress] using
        writableRange_textApart (h.write.slice 0 8 (by decide)) 0x1320 8
          (by decide +kernel)
  case boundary2 =>
    intro _ _
    exact text_address_ne_return hOutside 0x1328 (by decide +kernel)
  md5_run_finish [outputEffect, epilogueOutput, EpilogueKind.restore,
    EpilogueKind.outputOffset, BitVec.add_zero]

def resetDiscardSecondOutputBytes : List UInt8 := [0x48, 0x89, 0x4a, 0x8, 0x48, 0x89, 0x2]

set_option maxHeartbeats 400000 in
theorem resetDiscardSecond_output [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (OutputPre .resetDiscardSecond) (codeRange 0x10181e resetDiscardSecondOutputBytes)
      (outputEffect .resetDiscardSecond) := by
  unfold resetDiscardSecondOutputBytes
  have h0 : StepEffect (Memory.StorePre 0x10181e 4
      (storeAddrAt 0x10181e (.base 2 (.d8 8)) 4) 8)
      (codeRange 0x10181e [0x48, 0x89, 0x4a, 0x8])
      (movM64R64Effect 0x10181e 1 (.base 2 (.d8 8))) :=
    Buffered.Stores.mov_m64_r64_effect_step 0x10181e 0x48 (by unfold RexWPrefix; decide) 1
      (.base 2 (.d8 8)) (by decide) (by decide) (by decide)
  have h1 : StepEffect (Memory.StorePre (0x10181e + 4) 3
      (storeAddrAt (0x10181e + 4) (.base 2 .none) 3) 8)
      (codeRange (0x10181e + 4) [0x48, 0x89, 0x2])
      (movM64R64Effect (0x10181e + 4) 0 (.base 2 .none)) :=
    Buffered.Stores.mov_m64_r64_effect_step (0x10181e + 4) 0x48 (by unfold RexWPrefix; decide) 0
      (.base 2 .none) (by decide) (by decide) (by decide)
  refine AdvancesBlock.block_first ?k h0 (by x86_sub) ?pre ?av ?boundary
  case' k => x86_norm
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, epilogueOutput,
        EpilogueKind.outputOffset, BitVec.add_assoc] using
        writableRange_write (h.write.slice 8 8 (by decide))
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, epilogueOutput,
        EpilogueKind.outputOffset, BitVec.add_assoc, Extracted.textAddress] using
        writableRange_textApart (h.write.slice 8 8 (by decide)) 0x181e 4
          (by decide +kernel)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa [epilogueOutput, EpilogueKind.outputOffset, BitVec.add_assoc, Extracted.textAddress] using
      writableRange_textApart (h.write.slice 8 8 (by decide)) 0x181e 7
        (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1822 (by decide +kernel)
  refine AdvancesBlock.block_then ?copyEnd h1 (by x86_local) (by x86_sub)
    (by x86_full) ?mid ?boundary2
  case' copyEnd => x86_norm
  case mid =>
    intro s t h hE hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_
      · x86_norm
        simpa [epilogueOutput, EpilogueKind.outputOffset] using
          writableRange_write (h.write.slice 0 8 (by decide))
      · x86_norm
        simpa [epilogueOutput, EpilogueKind.outputOffset, Extracted.textAddress] using
          writableRange_textApart (h.write.slice 0 8 (by decide)) 0x1822 3
            (by decide +kernel)
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [epilogueOutput, EpilogueKind.outputOffset, Extracted.textAddress] using
        writableRange_textApart (h.write.slice 0 8 (by decide)) 0x181e 7
          (by decide +kernel)
  case boundary2 =>
    intro _ _
    exact text_address_ne_return hOutside 0x1825 (by decide +kernel)
  md5_run_finish [outputEffect, epilogueOutput, EpilogueKind.restore,
    EpilogueKind.outputOffset, BitVec.add_zero]

theorem bytes_of_two_memLoads {s t : RamState} {src dst : BitVec 64}
    {f : Nat → UInt8} (hbytes : Bytes s.external src 16 f)
    (halloc : ∀ i < 16, (t.external[dst + BitVec.ofNat 64 i]?).isSome)
    (hfirst : memLoad t.external dst 64 = memLoad s.external src 64)
    (hsecond : memLoad t.external (dst + 8) 64 = memLoad s.external (src + 8) 64) :
    Bytes t.external dst 16 f := by
  intro i hi
  have hbyte : memByte t.external (dst + BitVec.ofNat 64 i) =
      memByte s.external (src + BitVec.ofNat 64 i) := by
    by_cases h : i < 8
    · exact memByte_of_memLoad_eq hfirst i h
    · have he := memByte_of_memLoad_eq hsecond (i - 8) (by omega)
      have had (a : BitVec 64) : a + 8 + BitVec.ofNat 64 (i - 8) =
          a + BitVec.ofNat 64 i := by
        have hnat : 8 + (i - 8) = i := by omega
        rw [BitVec.add_assoc]
        congr 1
        change BitVec.ofNat 64 8 + BitVec.ofNat 64 (i - 8) = BitVec.ofNat 64 i
        rw [← BitVec.ofNat_add, hnat]
      simpa only [had] using he
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (halloc i hi)
  have he : b = f i := by
    change (t.external[dst + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[src + BitVec.ofNat 64 i]?).getD 0 at hbyte
    simpa only [hb, hbytes i hi, Option.getD_some] using hbyte
  exact hb.trans (congrArg some he)

private theorem read_memory_of_agrees {s t : RamState} {cs : List Component}
    (h : AgreesExcept cs s t) {address : BitVec 64} {n : Nat}
    (ha : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (address + BitVec.ofNat 64 i)) :
    (Operand.mem address : Operand n).read t = (Operand.mem address : Operand n).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[address + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[address + BitVec.ofNat 64 i]?).getD 0
  rw [h.byte (ha i hi)]

private theorem source_bytes {s : RamState} {offset : Nat} {digest : Vector UInt8 16}
    (h : (⟨(stackPtr s).toNat + offset, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨digest.toArray⟩) :
    Bytes s.external (stackPtr s + BitVec.ofNat 64 offset) 16 (fun i ↦ digest[i]!) := by
  intro i hi
  have hb := h.2 ⟨i, by simpa only [ByteArray.size, Vector.size_toArray] using hi⟩
  change s.external[BitVec.ofNat 64 ((stackPtr s).toNat + offset + i)]? =
    some digest[i] at hb
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    getElem!_pos digest i hi] using hb

private theorem hasBytes_of_bytes {t : RamState} {dst : BitVec 64}
    {digest : Vector UInt8 16}
    (h : Bytes t.external dst 16 (fun i ↦ digest[i]!)) :
    (⟨dst.toNat, 16⟩ : MemoryRegion).HasBytes t.external ⟨digest.toArray⟩ := by
  refine ⟨by simp [MemoryRegion.HasLength, ByteArray.size], ?_⟩
  intro i
  have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
  change t.external[BitVec.ofNat 64 (dst.toNat + i.val)]? = some digest[i.val]
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    getElem!_pos digest i.val hi] using h i.val hi

structure EpiloguePre [Bindings] (kind : EpilogueKind) (initial : RamState)
    (boundary : ReturnBoundary)
    (digest : Vector UInt8 16) (output : BitVec 64) (s : RamState) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  prepare : PreparePre kind s
  outputSlot : (Operand.mem (stackPtr s + BitVec.ofNat 64 kind.outputSlot) : Operand 64).read s +
    BitVec.ofNat 64 kind.outputOffset = output
  outputWritable : MemoryRoutines.WritableRange s output 16
  outputApart : RangeApart output 16 (stackPtr s) (kind.frame + 56)
  digestBytes : (⟨(stackPtr s).toNat + kind.source, 16⟩ : MemoryRegion).HasBytes
    s.external ⟨digest.toArray⟩
  saved : ∀ i : Fin 6,
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.frame + 8 * i.val)) : Operand 64).read s =
      (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val] : Operand 64).read initial
  returnSlot : (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.frame + 48)) : Operand 64).read s =
    boundary.rip
  boundaryRsp : stackPtr s + BitVec.ofNat 64 (kind.frame + 56) = boundary.rsp
  boundaryLow : boundary.rip.toNat < userAddressLimit
  boundaryOutside : ¬ InProgram boundary.rip
  df : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS

structure EpiloguePost [bindings : Bindings] (kind : EpilogueKind) (initial : RamState)
    (boundary : ReturnBoundary) (digest : Vector UInt8 16) (output : BitVec 64)
    (s t : RamState) : Prop where
  returns : ∃ fuel, Returns boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  digestBytes : (⟨output.toNat, 16⟩ : MemoryRegion).HasBytes t.external ⟨digest.toArray⟩
  calleeSaved : CalleeSavedRegistersUnchanged initial t
  df : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  memoryFrame : MemoryWriteFrame s t
    #v[⟨output.toNat, 16⟩, ⟨(stackPtr s).toNat + kind.frame - 16, 16⟩]
  sse : SupportedSSE bindings.processor s → SupportedSSE bindings.processor t

private theorem prepare_run [Bindings] {kind : EpilogueKind} {boundary : ReturnBoundary}
    {s : RamState} (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hPre : PreparePre kind s) (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (prepareEffect kind s).Holds s t := by
  have hrun : ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      (prepareEffect kind s).Holds s t := by
    cases kind with
    | updateFinalizeInto =>
      have hc : CodeIn (codeRange 0x101b69 NewEntries.UpdateFinalize.Epilogue.prepareBytes) s :=
        program_text_slice hCode 0x1b69 17 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ :=
        NewEntries.UpdateFinalize.Epilogue.prepare boundary hOutside s hReady hc ⟨hPre.rip, hPre.read⟩
      exact ⟨fuel, t, ha, hr, he⟩
    | slices =>
      have hc : CodeIn (codeRange 0x1005b9 slicesPrepareBytes) s :=
        program_text_slice hCode 0x5b9 33 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := slices_prepare boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
    | resetSecond =>
      have hc : CodeIn (codeRange 0x100c68 resetSecondPrepareBytes) s :=
        program_text_slice hCode 0xc68 40 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := resetSecond_prepare boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
    | finalizeResetSecond =>
      have hc : CodeIn (codeRange 0x1012f8 (finalizeResetSecondPrepareBytes)) s :=
        program_text_slice hCode 0x12f8 40 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := finalizeResetSecond_prepare boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
    | resetDiscardSecond =>
      have hc : CodeIn (codeRange 0x1017f9 (resetDiscardSecondPrepareBytes)) s :=
        program_text_slice hCode 0x17f9 37 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := resetDiscardSecond_prepare boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
  obtain ⟨fuel, t, ha, hr, he⟩ := hrun
  refine ⟨fuel, t, ha, hr, he.codeIn ?_ hCode, he⟩
  intro x hx c hc hcov
  have hc := prepare_components hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov
  · obtain ⟨i, hi, heq⟩ := hcov
    exact (hPre.scratch.slice 0 8 (by decide)).code i hi (by
      simpa only [BitVec.add_zero] using (heq ▸ (show InProgram x.1 from ⟨x.2, hx⟩)))
  · obtain ⟨i, hi, heq⟩ := hcov
    apply (hPre.scratch.slice 8 8 (by decide)).code i hi
    have hbase : stackPtr s + BitVec.ofNat 64 (kind.frame - 16) + 8#64 =
        stackPtr s + BitVec.ofNat 64 (kind.frame - 8) := by
      cases kind <;> simp [EpilogueKind.frame, BitVec.add_assoc]
    rw [hbase, ← heq]
    exact ⟨x.2, hx⟩

private theorem prepare_read_tail {kind : EpilogueKind} {s t : RamState}
    (h : (prepareEffect kind s).Holds s t) {offset : Nat}
    (hlo : kind.frame ≤ offset) (hhi : offset + 8 ≤ kind.frame + 56) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply read_memory_of_agrees h.agrees
  intro i hi c hc hcov
  have hc := prepare_components hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov
  all_goals
    obtain ⟨j, hj, heq⟩ := hcov
    apply RangeApart.offsets (stackPtr s) (a := offset) (len := 8)
      (b := _) (count := 8) ?_ ?_ (.inr ?_) i hi j hj heq
    all_goals cases kind <;> simp only [EpilogueKind.frame] at * <;> omega

private theorem output_run [Bindings] {kind : EpilogueKind} {boundary : ReturnBoundary}
    {s : RamState} (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hPre : OutputPre kind s) (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (outputEffect kind s).Holds s t := by
  have hrun : ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      (outputEffect kind s).Holds s t := by
    cases kind with
    | updateFinalizeInto =>
      have hc : CodeIn (codeRange 0x101b7a NewEntries.UpdateFinalize.Epilogue.outputBytes) s :=
        program_text_slice hCode 0x1b7a 7 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ :=
        NewEntries.UpdateFinalize.Epilogue.output boundary hOutside s hReady hc
          ⟨hPre.rip, by simpa only [epilogueOutput, EpilogueKind.outputOffset,
            BitVec.add_zero,
            NewEntries.UpdateFinalize.Epilogue.epilogueOutput] using hPre.write⟩
      refine ⟨fuel, t, ha, hr, ?_⟩
      simpa only [outputEffect, epilogueOutput, EpilogueKind.outputOffset,
        EpilogueKind.restore, BitVec.add_zero,
        NewEntries.UpdateFinalize.Epilogue.outputEffect,
        NewEntries.UpdateFinalize.Epilogue.epilogueOutput] using he
    | slices =>
      have hc : CodeIn (codeRange 0x1005da slicesOutputBytes) s :=
        program_text_slice hCode 0x5da 7 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := slices_output boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
    | resetSecond =>
      have hc : CodeIn (codeRange 0x100c90 resetSecondOutputBytes) s :=
        program_text_slice hCode 0xc90 8 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := resetSecond_output boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
    | finalizeResetSecond =>
      have hc : CodeIn (codeRange 0x101320 (finalizeResetSecondOutputBytes)) s :=
        program_text_slice hCode 0x1320 8 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := finalizeResetSecond_output boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
    | resetDiscardSecond =>
      have hc : CodeIn (codeRange 0x10181e (resetDiscardSecondOutputBytes)) s :=
        program_text_slice hCode 0x181e 7 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := resetDiscardSecond_output boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
  obtain ⟨fuel, t, ha, hr, he⟩ := hrun
  refine ⟨fuel, t, ha, hr, he.codeIn ?_ hCode, he⟩
  intro x hx c hc hcov
  simp only [outputEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_mem, List.append_nil, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl
  · obtain ⟨i, hi, heq⟩ := hcov
    exact (hPre.write.slice 8 8 (by decide)).code i hi (heq ▸ ⟨x.2, hx⟩)
  · obtain ⟨i, hi, heq⟩ := hcov
    exact hPre.write.code i (by omega) (heq ▸ ⟨x.2, hx⟩)
  · exact hcov

private theorem output_read_apart {kind : EpilogueKind} {s t : RamState}
    (h : (outputEffect kind s).Holds s t) {address : BitVec 64}
    (ha : RangeApart (epilogueOutput kind s) 16 address 8) :
    (Operand.mem address : Operand 64).read t = (Operand.mem address : Operand 64).read s := by
  apply read_memory_of_agrees h.agrees
  intro i hi c hc hcov
  simp only [outputEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_mem, List.append_nil, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl
  · obtain ⟨j, hj, heq⟩ := hcov
    exact MemoryRoutines.rangeApart_slice_left ha 8 8 (by decide) j hj i hi heq.symm
  · obtain ⟨j, hj, heq⟩ := hcov
    exact ha j (by omega) i hi heq.symm
  · exact hcov

private theorem restore_returns [Bindings] (kind : EpilogueKind)
    {s initial : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hPre : RestorePre kind s)
    (hSaved : ∀ i : Fin 6,
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.frame + 8 * i.val)) : Operand 64).read s =
        (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val] : Operand 64).read initial)
    (hReturn : (Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.frame + 48)) : Operand 64).read s =
      boundary.rip)
    (hRsp : stackPtr s + BitVec.ofNat 64 (kind.frame + 56) = boundary.rsp)
    (hLow : boundary.rip.toNat < userAddressLimit) (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Returns boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      CalleeSavedRegistersUnchanged initial t ∧
      AgreesExcept [.reg 3, .reg 12, .reg 13, .reg 14, .reg 15, .reg 5, .reg 4,
        .flags, .rip] s t := by
  have hrun : ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      (restoreEffect kind s).Holds s t := by
    cases kind with
    | updateFinalizeInto =>
      have hc : CodeIn (codeRange 0x101b81 NewEntries.UpdateFinalize.Epilogue.restoreBytes) s :=
        program_text_slice hCode 0x1b81 17 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ :=
        NewEntries.UpdateFinalize.Epilogue.restore boundary hOutside s hReady hc ⟨hPre.rip, hPre.read⟩
      exact ⟨fuel, t, ha, hr, he⟩
    | slices =>
      have hc : CodeIn (codeRange 0x1005e1 (EpilogueKind.restoreBytes .slices)) s :=
        program_text_slice hCode 0x5e1 17 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := slices_restore boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
    | resetSecond =>
      have hc : CodeIn (codeRange 0x100c98 (EpilogueKind.restoreBytes .resetSecond)) s :=
        program_text_slice hCode 0xc98 17 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := resetSecond_restore boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
    | finalizeResetSecond =>
      have hc : CodeIn (codeRange 0x101328 (EpilogueKind.restoreBytes .finalizeResetSecond)) s :=
        program_text_slice hCode 0x1328 17 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := finalizeResetSecond_restore boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
    | resetDiscardSecond =>
      have hc : CodeIn (codeRange 0x101825 (EpilogueKind.restoreBytes .resetDiscardSecond)) s :=
        program_text_slice hCode 0x1825 17 (by decide +kernel)
      obtain ⟨fuel, t, ha, hr, _, he⟩ := resetDiscardSecond_restore boundary hOutside s hReady hc hPre
      exact ⟨fuel, t, ha, hr, he⟩
  obtain ⟨fuel, u, ha, hr, he⟩ := hrun
  have hm : u.external = s.external := he.agrees.external (by
    simp [restoreEffect, Effect.components, Component.Covers])
  have hsp : stackPtr u = stackPtr s + BitVec.ofNat 64 (kind.frame + 48) :=
    he.writes.2.2.2.2.2.2
  have htop : stackTop u = boundary.rip := by
    simpa only [stackTop, hsp, Operand.read, hm] using hReturn
  have hc : CodeIn (codeRange (kind.restore + 17) [0xc3]) u := by
    have hu := hCode.of_external_eq hm
    cases kind with
    | updateFinalizeInto => exact program_text_slice hu 0x1b92 1 (by decide +kernel)
    | slices => exact program_text_slice hu 0x5f2 1 (by decide +kernel)
    | finalizeResetSecond => exact program_text_slice hu 0x1339 1 (by decide +kernel)
    | resetDiscardSecond => exact program_text_slice hu 0x1836 1 (by decide +kernel)
    | resetSecond => exact program_text_slice hu 0xca9 1 (by decide +kernel)
  have hp : RetPre (kind.restore + 17) u := by
    refine ⟨⟨he.rip, ?_⟩, ?_⟩
    · rw [hsp]
      apply MemReadable.of_external_eq _ hm
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using
        MemoryRoutines.memReadable_slice hPre.read 48 8 (by omega)
    · rw [htop]
      exact hLow
  obtain ⟨t, hstep, hready, hret⟩ := ret_effect_step (kind.restore + 17) u hr hc hp
  have hreturns : Returns boundary 1 u t := by
    apply Returns.of_step hstep (hret.rip.trans htop)
    have ht : stackPtr t = stackPtr u + 8 := hret.writes
    rw [hsp, BitVec.add_assoc] at ht
    have hsum : BitVec.ofNat 64 (kind.frame + 48) + 8 =
        BitVec.ofNat 64 (kind.frame + 56) := by cases kind <;> decide +kernel
    exact ht.trans (hsum ▸ hRsp)
  have hag : AgreesExcept [.reg 3, .reg 12, .reg 13, .reg 14, .reg 15, .reg 5, .reg 4,
      .flags, .rip] s t := (he.agrees.trans hret.agrees).mono (by
        simp [restoreEffect, retEffect, Effect.components])
  refine ⟨fuel + 1, t, ha.returns hreturns, hready,
    hCode.of_external_eq (hag.external (by simp [Component.Covers])), ?_, hag⟩
  intro register hreg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
  rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hret.agrees.read (r := 3) (n := 64) (by simp [retEffect, Effect.components])).trans
      (he.writes.1.trans (hSaved 0))
  · exact (hret.agrees.read (r := 5) (n := 64) (by simp [retEffect, Effect.components])).trans
      (he.writes.2.2.2.2.2.1.trans (hSaved 5))
  · exact (hret.agrees.read (r := 12) (n := 64) (by simp [retEffect, Effect.components])).trans
      (he.writes.2.1.trans (hSaved 1))
  · exact (hret.agrees.read (r := 13) (n := 64) (by simp [retEffect, Effect.components])).trans
      (he.writes.2.2.1.trans (hSaved 2))
  · exact (hret.agrees.read (r := 14) (n := 64) (by simp [retEffect, Effect.components])).trans
      (he.writes.2.2.2.1.trans (hSaved 3))
  · exact (hret.agrees.read (r := 15) (n := 64) (by simp [retEffect, Effect.components])).trans
      (he.writes.2.2.2.2.1.trans (hSaved 4))

private theorem mem_covers_contains {base address : BitVec 64} {offset length size : Nat}
    (hlow : base.toNat + size ≤ 2^32) (hoff : offset + length ≤ size)
    (hc : Component.Covers (.mem (base + BitVec.ofNat 64 offset) length) address) :
    (⟨base.toNat, size⟩ : MemoryRegion).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  rw [add_ofNat_add_ofNat, toNat_add_ofNat _ _ (by omega)]
  change base.toNat ≤ base.toNat + (offset + i) ∧
    base.toNat + (offset + i) < base.toNat + size
  omega

private theorem prepare_frame {kind : EpilogueKind} {s t : RamState}
    (h : (prepareEffect kind s).Holds s t) (hp : PreparePre kind s) :
    MemoryWriteFrame s t #v[⟨(stackPtr s).toNat + kind.frame - 16, 16⟩] := by
  apply h.agrees.memoryWriteFrame
  intro c hc address hcov
  have hc := prepare_components hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
  all_goals
    refine ⟨⟨(stackPtr s).toNat + kind.frame - 16, 16⟩, by simp, ?_⟩
    have hlow := hp.read.low
    obtain ⟨i, hi, rfl⟩ := hcov
    rw [add_ofNat_add_ofNat, toNat_add_ofNat _ _ (by
      cases kind <;> simp only [EpilogueKind.frame] at * <;> omega)]
    change (stackPtr s).toNat + kind.frame - 16 ≤ _ ∧
      _ < (stackPtr s).toNat + kind.frame - 16 + 16
    cases kind <;> simp only [EpilogueKind.frame] at * <;> omega

private theorem output_frame {kind : EpilogueKind} {s t : RamState}
    (h : (outputEffect kind s).Holds s t) (hp : OutputPre kind s) :
    MemoryWriteFrame s t #v[⟨(epilogueOutput kind s).toNat, 16⟩] := by
  apply h.agrees.memoryWriteFrame
  intro c hc address hcov
  simp only [outputEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_mem, List.append_nil, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨_, by simp, mem_covers_contains hp.write.readable.low (offset := 8) (by decide) hcov⟩
  · exact ⟨_, by simp,
      mem_covers_contains hp.write.readable.low (offset := 0) (length := 8) (by decide)
      (by simpa only [BitVec.add_zero] using hcov)⟩
  · exact hcov.elim

set_option maxHeartbeats 400000 in
theorem epilogue_correct [Bindings] {kind : EpilogueKind} {initial s : RamState}
    {boundary : ReturnBoundary} {digest : Vector UInt8 16} {output : BitVec 64}
    (h : EpiloguePre kind initial boundary digest output s) :
    ∃ t, EpiloguePost kind initial boundary digest output s t := by
  obtain ⟨n₁, u, ha₁, hr₁, hc₁, he₁⟩ :=
    prepare_run h.ready h.code h.prepare h.boundaryOutside
  have hsp₁ : stackPtr u = stackPtr s := he₁.agrees.read (r := 4) (n := 64) (by
    cases kind <;> simp [prepareEffect, NewEntries.UpdateFinalize.Epilogue.prepareEffect, Effect.components])
  have hout : epilogueOutput kind u = output := by
    unfold epilogueOutput
    rw [(prepare_registers he₁).2.2]
    exact h.outputSlot
  have hp₂ : OutputPre kind u := by
    refine ⟨?_, ?_⟩
    · cases kind <;>
        simpa [prepareEffect, NewEntries.UpdateFinalize.Epilogue.prepareEffect] using he₁.rip
    · rw [hout]
      exact h.outputWritable.of_agrees he₁.agrees
  obtain ⟨n₂, v, ha₂, hr₂, hc₂, he₂⟩ := output_run hr₁ hc₁ hp₂ h.boundaryOutside
  have hsp₂ : stackPtr v = stackPtr s :=
    (he₂.agrees.read (r := 4) (n := 64) (by simp [outputEffect, Effect.components])).trans hsp₁
  have htail (offset : Nat) (hlo : kind.frame ≤ offset)
      (hhi : offset + 8 ≤ kind.frame + 56) :
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read v =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
    apply (output_read_apart he₂ ?_).trans (prepare_read_tail he₁ hlo hhi)
    rw [hout]
    exact MemoryRoutines.rangeApart_slice_right h.outputApart offset 8 hhi
  have hp₃ : RestorePre kind v := by
    refine ⟨he₂.rip, ?_⟩
    rw [hsp₂]
    exact (MemoryRoutines.memReadable_slice h.prepare.read kind.frame 56 (by omega)).of_holds
      he₁ |>.of_holds he₂
  have hsaved : ∀ i : Fin 6,
      (Operand.mem (stackPtr v + BitVec.ofNat 64 (kind.frame + 8 * i.val)) : Operand 64).read v =
        (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val] : Operand 64).read
          initial := by
    intro i
    rw [hsp₂, htail _ (by omega) (by have := i.isLt; omega)]
    exact h.saved i
  have hreturn :
      (Operand.mem (stackPtr v + BitVec.ofNat 64 (kind.frame + 48)) : Operand 64).read v =
        boundary.rip := by
    rw [hsp₂, htail _ (by omega) (by omega)]
    exact h.returnSlot
  have hrsp : stackPtr v + BitVec.ofNat 64 (kind.frame + 56) = boundary.rsp := by
    rw [hsp₂]
    exact h.boundaryRsp
  obtain ⟨n₃, t, hret, hrt, hct, hsav, hag⟩ :=
    restore_returns kind hr₂ hc₂ hp₃ hsaved hreturn hrsp h.boundaryLow h.boundaryOutside
  have hm : t.external = v.external := hag.external (by simp [Component.Covers])
  have hb : Bytes v.external output 16 (fun i ↦ digest[i]!) := by
    apply bytes_of_two_memLoads (source_bytes h.digestBytes)
    · intro i hi
      exact he₂.agrees.grow _ (he₁.agrees.grow _ (h.outputWritable.readable.mem i hi))
    · have hw := he₂.writes.2
      rw [hout] at hw
      exact hw.trans (prepare_registers he₁).1
    · have hw := he₂.writes.1
      rw [hout] at hw
      have hh := hw.trans (prepare_registers he₁).2.1
      have hadd : stackPtr s + BitVec.ofNat 64 kind.source + 8 =
          stackPtr s + BitVec.ofNat 64 (kind.source + 8) := by
        cases kind <;> simp [EpilogueKind.source, BitVec.add_assoc]
      change memLoad v.external (output + 8) 64 =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 (kind.source + 8)) 64 at hh
      rw [hadd]
      exact hh
  have hframe₁ := prepare_frame he₁ h.prepare
  have hframe₂ := output_frame he₂ hp₂
  rw [hout] at hframe₂
  refine ⟨t, ⟨⟨n₁ + (n₂ + n₃), ha₁.returns (ha₂.returns hret)⟩, hrt, hct,
    ?_, hsav, hag.directionFlagClear (by simp)
      (he₂.agrees.directionFlagClear (by simp [outputEffect, Effect.components])
        (he₁.agrees.directionFlagClear (by cases kind <;> simp [prepareEffect, NewEntries.UpdateFinalize.Epilogue.prepareEffect, Effect.components]) h.df)),
    ?_, ?_⟩⟩
  · rw [hm]
    exact hasBytes_of_bytes hb
  · intro address houtside
    rw [hm, hframe₂ address (by
      intro region hregion
      simp only [Vector.mem_mk, Array.mem_singleton] at hregion
      subst region
      exact houtside _ (by simp)), hframe₁ address (by
      intro region hregion
      simp only [Vector.mem_mk, Array.mem_singleton] at hregion
      subst region
      exact houtside _ (by simp))]

  · intro hs
    exact SupportedSSE.of_agreesExcept hag
      (SupportedSSE.of_agreesExcept he₂.agrees (SupportedSSE.of_agreesExcept he₁.agrees hs))

theorem EpiloguePost.memoryFrame_stack [Bindings] {kind : EpilogueKind}
    {initial s t : RamState} {boundary : ReturnBoundary} {digest : Vector UInt8 16}
    {output : BitVec 64} {budget : Nat}
    (h : EpiloguePost kind initial boundary digest output s t)
    (hstack : Stack.Valid initial budget) (hbudget : kind.frame + 48 ≤ budget)
    (hsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (kind.frame + 48)) :
    MemoryWriteFrame s t #v[⟨output.toNat, 16⟩, Stack.region initial budget] := by
  have hbound : budget ≤ (stackPtr initial).toNat := hstack.2.2.1
  have hlt := (stackPtr initial).isLt
  have hnat : (stackPtr s).toNat = (stackPtr initial).toNat - (kind.frame + 48) := by
    have hn : kind.frame + 48 < 2^64 := by omega
    simp only [hsp, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    omega
  have hscratch (address : BitVec 64)
      (ha : (⟨(stackPtr s).toNat + kind.frame - 16, 16⟩ : MemoryRegion).Contains address.toNat) :
      (Stack.region initial budget).Contains address.toNat := by
    change (stackPtr s).toNat + kind.frame - 16 ≤ address.toNat ∧
      address.toNat < (stackPtr s).toNat + kind.frame - 16 + 16 at ha
    change (stackPtr initial).toNat - budget ≤ address.toNat ∧
      address.toNat < (stackPtr initial).toNat - budget +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - budget))
    rw [hnat] at ha
    have hframe : 16 ≤ kind.frame := by cases kind <;> decide
    omega
  intro address hout
  apply h.memoryFrame address
  intro region hregion
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hregion
  rcases hregion with rfl | rfl
  · exact hout _ (by simp)
  · intro hin
    exact hout _ (by simp) (hscratch address hin)

end Md5.Proofs.Streaming
