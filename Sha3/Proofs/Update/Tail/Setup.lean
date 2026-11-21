import Sha3.Proofs.X86.Instructions.Add.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple
import Sha3.Proofs.Update.Tail.Code
import Sha3.Proofs.Wrapper.Setup.Basic
import Sha3.Proofs.Scalar.Address.And
import Sha3.Proofs.X86.Instructions.Test.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple
import Sha3.Proofs.X86.Instructions.Add.Triple
import X86Proofs.Instructions.NopMem.Triple

namespace Sha3.Proofs.Update.Tail.Setup

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program
open Sha3.Proofs.Wrapper (ImageAt)

def tailSetupPC (v : Variant) : BitVec 64 := chunkAddress v + 56

def postChunkPC (v : Variant) : BitVec 64 := chunkAddress v + 51

def finishPC (v : Variant) : BitVec 64 := chunkAddress v + 96

def chunkSetupPC (v : Variant) : BitVec 64 := tailAddress v + 36

def clobbers : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 7, .reg 13, .reg 15, .flags, .rip]

theorem clobbers_nomem : ∀ c ∈ clobbers, ∀ a, ¬ c.Covers a := by
  simp [clobbers, Component.Covers]

theorem frame_trans {s t u : RamState} (h : AgreesExcept clobbers s t)
    (h' : AgreesExcept clobbers t u) : AgreesExcept clobbers s u :=
  (h.trans h').mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)

private theorem advance [Bindings] {boundary : ReturnBoundary} {s model : RamState}
    {p : BitVec 64} {bytes : List UInt8} {pre : RamState → Prop} {effect : RamState → Effect}
    (step : StepEffect pre (codeRange p bytes) effect) (image : ImageAt p bytes)
    (full : ∀ t, ∀ w ∈ (effect t).writes, w.Full)
    (localWrites : ∀ a b, Obs a b → (effect a).writes = (effect b).writes)
    (frame : ∀ c ∈ (effect s).components, c ∈ clobbers)
    (next : 0x100000 ≤ (effect s).rip.toNat ∧ (effect s).rip.toNat ≤ 0x106222)
    (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (hp : pre s) (obs : Obs model s) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ (effect s).Holds s t ∧
      Obs (applyWrites model (effect model).writes) t ∧ AgreesExcept clobbers s t := by
  obtain ⟨t, ht, hr, he⟩ := step.advances ready
    (image.code (fun a b h ↦ (loaded (a, b) h).2)) hp
    (Permutation.permutation_address_ne_boundary sp next.1 next.2)
  have ha := he.agrees.mono frame
  refine ⟨t, ht, hr, CodeIn.of_external_eq (ha.external clobbers_nomem) loaded,
    sp, he, ?_, ha⟩
  rw [localWrites model s obs]
  exact he.obs obs (full s)

macro "next_pc " v:term : tactic => `(tactic|
  cases ($v) <;> first
  | decide +kernel
  | (dsimp only [movR32R32Effect, andR32Imm8Effect, cmpR64Imm8Effect,
      xorR32R32Effect, leaR64Effect, addR64Imm8Effect, addR64R64Effect,
      jmpEffect]; decide +kernel)
  | (simp only [jccEffect, branchEffect]; split <;> decide +kernel))

private theorem test_branch [Bindings] {boundary : ReturnBoundary} (p : BitVec 64)
    (reg : BitVec 5) (rex modrm : UInt8) (disp : BitVec 8)
    (testStep : StepEffect (fun s ↦ s.RIP = p) (codeRange p [rex,0x85,modrm])
      (testR64R64Effect p reg reg))
    (image1 : ImageAt p [rex,0x85,modrm])
    (image2 : ImageAt (p + 3) (0x74 :: immBytes 8 disp))
    (low : (branchTarget (p + 3) 2 (disp.signExtend 64)).toNat < 2^32)
    (next₁ : 0x100000 ≤ (p + 3#64).toNat ∧ (p + 3#64).toNat ≤ 0x106222)
    (next₂ : 0x100000 ≤ (p + 5#64).toNat ∧ (p + 5#64).toNat ≤ 0x106222)
    (next₃ : 0x100000 ≤ (branchTarget (p + 3) 2 (disp.signExtend 64)).toNat ∧
      (branchTarget (p + 3) 2 (disp.signExtend 64)).toNat ≤ 0x106222)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = p) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧
      t.RIP = (if ((Operand.reg reg : Operand 64).read s == 0) then
        branchTarget (p + 3) 2 (disp.signExtend 64) else p + 5) ∧
      Obs s t ∧ AgreesExcept clobbers s t := by
  obtain ⟨s1,a1,r1,l1,b1,e1,o1,f1⟩ := advance testStep image1
    (by intro t; simp [testR64R64Effect]) (by intro a b h; rfl)
    (by simp [clobbers]) next₁ ready loaded sp ip (Obs.refl s)
  have hz : (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      ((Operand.reg reg : Operand 64).read s == 0) := by
    simpa only [testR64R64Effect, Effect.FlagsHold, testFlags, BitVec.and_self,
      StatusFlagsOutcome.Allows, FlagAllows] using e1.flags.2.2.2.1
  obtain ⟨s2,a2,r2,l2,b2,e2,o2,f2⟩ := advance
    (jcc_rel8_effect_step (p + 3) 4 disp) image2
    (by intro t; simp [jccEffect, branchEffect]) (by intro a b h; rfl)
    (by simp [jccEffect, clobbers]) (by
      dsimp only [jccEffect, branchEffect]
      split
      · exact next₃
      · simpa only [BitVec.add_assoc, BitVec.reduceAdd] using next₂) r1 l1 b1 ⟨e1.rip, fun _ ↦ low⟩ o1
  refine ⟨s2,a1.trans a2,r2,l2,b2,?_,o2,frame_trans f1 f2⟩
  simpa only [jccEffect, branchEffect, condHolds, BitVec.reduceToNat, hz,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e2.rip

theorem entry_test [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = tailAddress v) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧
      t.RIP = (if ((Operand.reg 12 : Operand 64).read s == 0) then
        tailAddress v + 25 else tailAddress v + 5) ∧
      Obs s t ∧ AgreesExcept clobbers s t := by
  have target : branchTarget (tailAddress v + 3) 2 (BitVec.signExtend 64 (0x14 : BitVec 8)) =
      tailAddress v + 25 := by simp [branchTarget, BitVec.add_assoc]
  have h := test_branch (tailAddress v) 12 0x4d 0xe4 0x14
    (test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by cases v <;> decide +kernel)
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)
    (by cases v <;> decide +kernel) s ready loaded sp ip
  simpa only [target] using h

theorem postchunk_test [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = postChunkPC v) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧
      t.RIP = (if ((Operand.reg 0 : Operand 64).read s == 0) then
        finishPC v else tailSetupPC v) ∧
      Obs s t ∧ AgreesExcept clobbers s t := by
  have target : branchTarget (postChunkPC v + 3) 2 (BitVec.signExtend 64 (0x28 : BitVec 8)) =
      finishPC v := by cases v <;> decide +kernel
  have next : postChunkPC v + (5 : BitVec 64) = tailSetupPC v := by cases v <;> decide +kernel
  have h := test_branch (postChunkPC v) 0 0x48 0xc0 0x28
    (test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by cases v <;> decide +kernel)
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)
    (by cases v <;> decide +kernel) s ready loaded sp ip
  simpa only [target,next] using h


def jaeDisp (_ : Variant) : BitVec 8 := 15

private theorem dispatch_image (v : Variant) :
    ImageAt (tailAddress v + 5)
      [0x44,0x89,0xe0,0x83,0xe0,3,0x49,0x83,0xfc,4] := by
  unfold ImageAt
  cases v <;> decide +kernel

private theorem mask_low (r : Fin 200) :
    (((BitVec.ofNat 64 r.val).setWidth 32).setWidth 64).setWidth 32 &&& (3 : BitVec 32) =
      BitVec.ofNat 32 (r.val % 4) := by
  revert r
  decide +kernel

private theorem stack_read_frame {s t : RamState} (h : AgreesExcept clobbers s t)
    (hr : MemReadable s ((Operand.reg 4 : Operand 64).read s) 8) :
    MemReadable t ((Operand.reg 4 : Operand 64).read t) 8 := by
  rw [h.read (by simp [clobbers])]
  exact hr.of_external_eq (h.external clobbers_nomem)

private theorem load_cursor [Bindings] {boundary : ReturnBoundary} (p : BitVec 64)
    (image : ImageAt p [0x48,0x8b,0x3c,0x24])
    (next : 0x100000 ≤ (p + (4 : BitVec 64)).toNat ∧ (p + (4 : BitVec 64)).toNat ≤ 0x106222)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = p)
    (hr : MemReadable s ((Operand.reg 4 : Operand 64).read s) 8) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ t.RIP = p + (4 : BitVec 64) ∧
      (Operand.reg 7 : Operand 64).read t =
        (Operand.mem ((Operand.reg 4 : Operand 64).read s) : Operand 64).read s ∧
      AgreesExcept [.reg 7,.rip] s t := by
  obtain ⟨t,ha,hr',hl,hb,he,ho,hf⟩ := advance
    (effect := movR64M64Effect p 7 (.sib 4 none 0 .none))
    (mov_r64_m64_effect_step p 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 .none)
      (by decide) (by decide) (by decide)) image
    (by intro t; simp [movR64M64Effect,Write.Full,Operand.Full])
    (by intro a b h; simp only [movR64M64Effect,AddrMode.addr_obs h,h.read_mem])
    (by simp [clobbers]) next ready loaded sp ⟨ip,by
      change MemReadable s ((Operand.reg 4 : Operand 64).read s + (0 : BitVec 64)) 8
      rw [show (Operand.reg 4 : Operand 64).read s + (0 : BitVec 64) =
        (Operand.reg 4 : Operand 64).read s from BitVec.add_zero _]
      exact hr⟩ (Obs.refl s)
  refine ⟨t,ha,hr',hl,hb,he.rip,?_,he.agrees⟩
  rw [← ho.read_reg]
  x86_norm [movR64M64Effect,AddrMode.addr,AddrMode.offset,BitVec.add_zero]

set_option maxHeartbeats 600000 in
theorem dispatch_compare [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (r : Fin 200) (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = tailAddress v + (5 : BitVec 64))
    (hr : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 r.val)
    (hread : MemReadable s ((Operand.reg 4 : Operand 64).read s) 8) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧
      t.RIP = (if 4 ≤ r.val then chunkSetupPC v else tailAddress v + 21) ∧
      (Operand.reg 0 : Operand 64).read t = BitVec.ofNat 64 (r.val % 4) ∧
      (Operand.reg 7 : Operand 64).read t =
        (Operand.mem ((Operand.reg 4 : Operand 64).read s) : Operand 64).read s ∧
      AgreesExcept [.reg 0,.reg 7,.flags,.rip] s t := by
  have image := dispatch_image v
  obtain ⟨s1,a1,r1,l1,b1,e1,o1,f1⟩ := advance
    (effect := movR32R32Effect (tailAddress v + 5) 3 0 12)
    (mov_r32_r32_rex_effect_step _ 0x44 0xe0 (by unfold RexNoWPrefix; decide) (by decide))
    (by simpa only [BitVec.add_zero] using image.slice (bytes := [0x44,0x89,0xe0]) 0 (by rfl))
    (by intro t; simp [movR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR32R32Effect, h.read_reg])
    (by simp [clobbers]) (by next_pc v) ready loaded sp ip (Obs.refl s)
  obtain ⟨s2,a2,r2,l2,b2,e2,o2,f2⟩ := advance
    (effect := andR32Imm8Effect (tailAddress v + 8) 3 0 3)
    (and_r32_imm8_effect_step _ 0xe0 3 (by decide) (by decide))
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
      image.slice (bytes := 0x83 :: 0xe0 :: immBytes 8 3) 3 (by cases v <;> decide +kernel))
    (by intro t; simp [andR32Imm8Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [andR32Imm8Effect, h.read_reg])
    (by simp [clobbers]) (by next_pc v) r1 l1 b1 (by simpa only [movR32R32Effect,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e1.rip) o1
  obtain ⟨s3,a3,r3,l3,b3,e3,o3,f3⟩ := advance
    (effect := cmpR64Imm8Effect (tailAddress v + 11) 12 4)
    (cmp_r64_imm8_effect_step _ 0x49 0xfc 4 (by unfold RexWPrefix; decide) (by decide) (by decide))
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
      image.slice (bytes := 0x49 :: 0x83 :: 0xfc :: immBytes 8 4) 6 (by cases v <;> decide +kernel))
    (by intro t; simp [cmpR64Imm8Effect]) (by intro a b h; rfl)
    (by simp [clobbers]) (by next_pc v) r2 l2 b2 (by simpa only [andR32Imm8Effect,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using e2.rip) o2
  have hr2 : (Operand.reg 12 : Operand 64).read s2 = BitVec.ofNat 64 r.val := by
    first | rw [← o2.read_reg] | rw [← o2.read_mem]
    x86_norm [movR32R32Effect, andR32Imm8Effect]
    exact hr
  have cf : (StatusFlags.ofRFLAGS s3.RFLAGS).CF = decide (r.val < 4) := by
    have hh := e3.flags.1
    change (StatusFlags.ofRFLAGS s3.RFLAGS).CF =
      decide (((Operand.reg 12 : Operand 64).read s2).toNat < 4) at hh
    rw [hr2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := r.isLt; omega)] at hh
    exact hh
  obtain ⟨sm,am,rm,lm,bm,ipm,curm,fm⟩ := load_cursor (tailAddress v + 15)
    (by unfold ImageAt; cases v <;> decide +kernel) (by next_pc v) s3 r3 l3 b3
    (by simpa only [cmpR64Imm8Effect,BitVec.add_assoc,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using e3.rip)
    (stack_read_frame (frame_trans f1 (frame_trans f2 f3)) hread)
  have cfm : (StatusFlags.ofRFLAGS sm.RFLAGS).CF = decide (r.val < 4) := by
    rw [fm.rflags (by decide) (by decide)]
    exact cf
  obtain ⟨s4,a4,r4,l4,b4,e4,o4,f4⟩ := advance
    (jcc_rel8_effect_step (tailAddress v + 19) 3 (jaeDisp v))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [jccEffect, branchEffect]) (by intro a b h; rfl)
    (by simp [jccEffect, clobbers]) (by next_pc v) rm lm bm
    ⟨by simpa only [BitVec.add_assoc, BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using ipm, fun _ ↦ by cases v <;> decide +kernel⟩ (Obs.refl sm)
  refine ⟨s4,a1.trans (a2.trans (a3.trans (am.trans a4))),r4,l4,b4,?_,?_,?_,?_⟩
  · have target : branchTarget (tailAddress v + 19) 2 ((jaeDisp v).signExtend 64) =
        chunkSetupPC v := by cases v <;> decide +kernel
    simp only [BitVec.ofNat_eq_ofNat] at target
    have hh := e4.rip
    simp only [jccEffect, branchEffect, condHolds, BitVec.reduceToNat, cfm, target,
      Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hh
    simpa only [BitVec.ofNat_eq_ofNat] using hh
  · rw [e4.agrees.read (by simp [jccEffect,branchEffect,Effect.components]), fm.read (by decide), ← o3.read_reg]
    x86_norm [movR32R32Effect, andR32Imm8Effect, cmpR64Imm8Effect, jccEffect, branchEffect]
    have h32 := show (Operand.reg 12 : Operand 32).read s =
      ((Operand.reg 12 : Operand 64).read s).setWidth 32 from rfl
    simp only [BitVec.ofNat_eq_ofNat] at h32 hr
    have hm := mask_low r
    simp only [BitVec.ofNat_eq_ofNat] at hm
    rw [h32, hr, hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · rw [e4.agrees.read (by simp [jccEffect,branchEffect,Effect.components]),curm]
    have ff := frame_trans f1 (frame_trans f2 f3)
    rw [ff.read (r := 4) (by simp [clobbers])]
    simp only [Operand.read,ff.external clobbers_nomem]
  · apply ((e1.agrees.trans e2.agrees).trans (e3.agrees.trans (fm.trans e4.agrees))).mono
    simp [movR32R32Effect, andR32Imm8Effect, cmpR64Imm8Effect, jccEffect,
      branchEffect,Effect.components]


def shortDisp : Variant → BitVec 8
  | .sha224 => 0x62 | .sha256 => 0x60 | .sha384 => 0x53 | .sha512 => 0x53

theorem short_setup [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = tailAddress v + (21 : BitVec 64)) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ t.RIP = tailSetupPC v ∧
      (Operand.reg 2 : Operand 64).read t = 0 ∧ AgreesExcept [.reg 2,.flags,.rip] s t := by
  obtain ⟨s1,a1,r1,l1,b1,e1,o1,f1⟩ := advance
    (effect := xorR32R32Effect (tailAddress v + 21) 2 2 2)
    (xor_r32_r32_effect_step _ 0xd2 (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect,h.read_reg])
    (by simp [clobbers]) (by next_pc v) ready loaded sp ip (Obs.refl s)
  obtain ⟨s2,a2,r2,l2,b2,e2,o2,f2⟩ := advance
    (jmp_rel8_effect_step (tailAddress v + 23) (shortDisp v) (by cases v <;> decide +kernel))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [jmpEffect]) (by intro a b h; rfl)
    (by simp [jmpEffect,Effect.components,clobbers]) (by next_pc v) r1 l1 b1
    (by simpa only [xorR32R32Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e1.rip) o1
  refine ⟨s2,a1.trans a2,r2,l2,b2,?_,?_,?_⟩
  · have hh := e2.rip
    cases v <;> exact hh
  · first | rw [← o2.read_reg] | rw [← o2.read_mem]
    x86_norm [xorR32R32Effect,jmpEffect,branchEffect,BitVec.xor_self]
  · apply (e1.agrees.trans e2.agrees).mono
    simp [jmpEffect,Effect.components,xorR32R32Effect]

def chunkLeaPC (v : Variant) : BitVec 64 :=
  chunkSetupPC v + (if v = .sha384 ∨ v = .sha512 then 6 else 9)

def chunkMask (v : Variant) : BitVec 32 := if v = .sha384 ∨ v = .sha512 then 124 else 252

def chunkMaskBytes (v : Variant) : List UInt8 :=
  if v = .sha384 ∨ v = .sha512 then [0x83,0xe1,0x7c] else [0x81,0xe1,0xfc,0,0,0]

def chunkMaskEffect (v : Variant) (s : RamState) : Effect :=
  let value := (Operand.reg 1 : Operand 32).read s &&& chunkMask v
  {rip := chunkLeaPC v, writes := [⟨(Operand.reg 1 : Operand 64),value.setWidth 64⟩],
   flags := some (andFlags value)}

private theorem chunk_mask_step [Bindings] (v : Variant) :
    StepEffect (fun s ↦ s.RIP = chunkSetupPC v + (3 : BitVec 64))
      (codeRange (chunkSetupPC v + 3) (chunkMaskBytes v)) (chunkMaskEffect v) := by
  cases v with
  | sha384 | sha512 => exact and_r32_imm8_effect_step _ 0xe1 0x7c (by decide) (by decide)
  | sha224 | sha256 => exact and_ecx_fc_effect_step _

private theorem chunk_mask_arithmetic (v : Variant) (r : Fin (v.rate)) :
    (((((BitVec.ofNat 64 r.val).setWidth 32).setWidth 64).setWidth 32) &&& chunkMask v).setWidth 64 =
      BitVec.ofNat 64 (r.val / 4 * 4) := by
  revert r
  cases v <;> decide +kernel


def chunkNopBytes : Variant → List UInt8
  | .sha224 => [0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0]
  | .sha256 => [0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0]
  | .sha384 | .sha512 => []

private theorem chunk_nop [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = chunkLeaPC v + (10 : BitVec 64)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ t.RIP = chunkAddress v ∧ Obs s t ∧
      AgreesExcept [.rip] s t := by
  cases v with
  | sha384 | sha512 => exact ⟨0,s,(advances_zero _ _ _).mpr rfl,ready,loaded,sp,ip,Obs.refl _,AgreesExcept.refl _ _⟩
  | sha224 =>
    obtain ⟨t,ha,hr,hl,hb,he,ho,hf⟩ := advance
      (nop_m_effect_step _ [0x66,0x66,0x66,0x2e]
        (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0))
        (by decide) (by decide) (by decide))
      (by unfold ImageAt; decide +kernel)
      (by intro t; simp [nopEffect]) (by intro a b h; rfl)
      (by simp [nopEffect,Effect.components,clobbers]) (by decide +kernel)
      ready loaded sp ip (Obs.refl s)
    exact ⟨1,t,ha,hr,hl,hb,he.rip,ho,he.agrees⟩
  | sha256 =>
    obtain ⟨t,ha,hr,hl,hb,he,ho,hf⟩ := advance
      (nop_m_effect_step _ [0x66,0x2e]
        (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0))
        (by decide) (by decide) (by decide))
      (by unfold ImageAt; decide +kernel)
      (by intro t; simp [nopEffect]) (by intro a b h; rfl)
      (by simp [nopEffect,Effect.components,clobbers]) (by decide +kernel)
      ready loaded sp ip (Obs.refl s)
    exact ⟨1,t,ha,hr,hl,hb,he.rip,ho,he.agrees⟩

set_option maxHeartbeats 1200000 in
theorem chunk_setup [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (r : Fin (v.rate)) (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = chunkSetupPC v)
    (hr : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 r.val) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ t.RIP = chunkAddress v ∧
      (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 (r.val / 4 * 4) ∧
      (Operand.reg 2 : Operand 64).read t = 0 ∧
      (Operand.reg 6 : Operand 64).read t =
        (Operand.reg 3 : Operand 64).read s + (Operand.reg 13 : Operand 64).read s + 3 ∧
      AgreesExcept [.reg 1,.reg 2,.reg 6,.flags,.rip] s t := by
  obtain ⟨s1,a1,r1,l1,b1,e1,o1,f1⟩ := advance
    (effect := movR32R32Effect (chunkSetupPC v) 3 1 12)
    (mov_r32_r32_rex_effect_step _ 0x44 0xe1 (by unfold RexNoWPrefix; decide) (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [movR32R32Effect,Write.Full,Operand.Full])
    (by intro a b h; simp only [movR32R32Effect,h.read_reg])
    (by simp [clobbers]) (by next_pc v) ready loaded sp ip (Obs.refl s)
  obtain ⟨s2,a2,r2,l2,b2,e2,o2,f2⟩ := advance (chunk_mask_step v)
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [chunkMaskEffect,Write.Full,Operand.Full])
    (by intro a b h; simp only [chunkMaskEffect,h.read_reg])
    (by simp [chunkMaskEffect,Effect.components,clobbers]) (by dsimp only [chunkMaskEffect]; next_pc v) r1 l1 b1 e1.rip o1
  obtain ⟨s3,a3,r3,l3,b3,e3,o3,f3⟩ := advance
    (effect := leaR64Effect (chunkLeaPC v) 6 (.sib 3 (some 13) 0 .none))
    (lea_r64_effect_step _ 0x4a (by unfold RexWPrefix; decide) 6
      (.sib 3 (some 13) 0 .none) (by decide) (by decide) (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [leaR64Effect,Write.Full,Operand.Full])
    (by intro a b h; simp only [leaR64Effect,AddrMode.addr_obs h])
    (by simp [clobbers]) (by next_pc v) r2 l2 b2 e2.rip o2
  obtain ⟨s4,a4,r4,l4,b4,e4,o4,f4⟩ := advance
    (effect := addR64Imm8Effect (chunkLeaPC v + 4) 6 3)
    (add_r64_imm8_effect_step _ 0x48 0xc6 3 (by unfold RexWPrefix; decide) (by decide) (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [addR64Imm8Effect,Write.Full,Operand.Full])
    (by intro a b h; simp only [addR64Imm8Effect,h.read_reg])
    (by simp [clobbers]) (by next_pc v) r3 l3 b3 e3.rip o3
  obtain ⟨s5,a5,r5,l5,b5,e5,o5,f5⟩ := advance
    (effect := xorR32R32Effect (chunkLeaPC v + 8) 2 2 2)
    (xor_r32_r32_effect_step _ 0xd2 (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [xorR32R32Effect,Write.Full,Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect,h.read_reg])
    (by simp [clobbers]) (by next_pc v) r4 l4 b4 (by simpa only [addR64Imm8Effect,
      BitVec.add_assoc,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using e4.rip) o4
  obtain ⟨fuel6,s6,a6,r6,l6,b6,ip6,o6,f6⟩ := chunk_nop v s5 r5 l5 b5
    (by simpa only [xorR32R32Effect,BitVec.add_assoc,BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e5.rip)
  have obs := o5.trans o6
  refine ⟨5 + fuel6,s6,?_,r6,l6,b6,ip6,?_,?_,?_,?_⟩
  · simpa only [← Nat.add_assoc] using (a1.trans (a2.trans (a3.trans (a4.trans a5)))).trans a6
  · rw [← obs.read_reg]
    x86_norm [movR32R32Effect,chunkMaskEffect,leaR64Effect,addR64Imm8Effect,xorR32R32Effect]
    have h32 := show (Operand.reg 12 : Operand 32).read s =
      ((Operand.reg 12 : Operand 64).read s).setWidth 32 from rfl
    have hm := chunk_mask_arithmetic v r
    simp only [BitVec.ofNat_eq_ofNat] at h32 hr hm
    rw [h32,hr]
    exact hm
  · rw [← obs.read_reg]
    x86_norm [movR32R32Effect,chunkMaskEffect,leaR64Effect,addR64Imm8Effect,
      xorR32R32Effect,BitVec.xor_self]
  · rw [← obs.read_reg]
    x86_norm [movR32R32Effect,chunkMaskEffect,leaR64Effect,addR64Imm8Effect,
      xorR32R32Effect,BitVec.shiftLeft_zero,BitVec.add_zero]
  · have hh := (e1.agrees.trans (e2.agrees.trans (e3.agrees.trans (e4.agrees.trans e5.agrees))))
    apply (hh.trans f6).mono
    simp [chunkMaskEffect,Effect.components,movR32R32Effect,leaR64Effect,
      addR64Imm8Effect,xorR32R32Effect]



def zeroDisp : Variant → BitVec 32
  | .sha224 => 0x102 | .sha256 => 0x100 | .sha384 | .sha512 => 0xf3

theorem zero_setup [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = tailAddress v + (25 : BitVec 64))
    (hread : MemReadable s ((Operand.reg 4 : Operand 64).read s) 8) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ t.RIP = cursorWriteAddress v ∧
      (Operand.reg 1 : Operand 64).read t = 0 ∧ (Operand.reg 7 : Operand 64).read t =
        (Operand.mem ((Operand.reg 4 : Operand 64).read s) : Operand 64).read s ∧
      AgreesExcept [.reg 1,.reg 7,.flags,.rip] s t := by
  obtain ⟨s1,a1,r1,l1,b1,e1,o1,f1⟩ := advance
    (effect := xorR32R32Effect (tailAddress v + (25 : BitVec 64)) 2 1 1)
    (xor_r32_r32_effect_step _ 0xc9 (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [xorR32R32Effect,Write.Full,Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect,h.read_reg])
    (by simp [clobbers]) (by next_pc v) ready loaded sp ip (Obs.refl s)
  obtain ⟨sm,am,rm,lm,bm,ipm,curm,fm⟩ := load_cursor (tailAddress v + 27)
    (by unfold ImageAt; cases v <;> decide +kernel) (by next_pc v) s1 r1 l1 b1
    (by simpa only [xorR32R32Effect,BitVec.add_assoc,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using e1.rip)
    (stack_read_frame f1 hread)
  obtain ⟨s2,a2,r2,l2,b2,e2,o2,f2⟩ := advance
    (jmp_rel32_effect_step (tailAddress v + 31) (zeroDisp v) (by cases v <;> decide +kernel))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [jmpEffect]) (by intro a b h; rfl)
    (by simp [jmpEffect,Effect.components,clobbers]) (by next_pc v) rm lm bm
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using ipm) (Obs.refl sm)
  refine ⟨s2,a1.trans (am.trans a2),r2,l2,b2,?_,?_,?_,?_⟩
  · have hh := e2.rip
    cases v <;> exact hh
  · rw [e2.agrees.read (by simp [jmpEffect,Effect.components]),fm.read (by decide),← o1.read_reg]
    x86_norm [xorR32R32Effect,jmpEffect,BitVec.xor_self]
  · rw [e2.agrees.read (by simp [jmpEffect,Effect.components]),curm]
    rw [f1.read (r := 4) (by simp [clobbers])]
    simp only [Operand.read,f1.external clobbers_nomem]
  · apply (e1.agrees.trans (fm.trans e2.agrees)).mono
    simp [Effect.components, xorR32R32Effect, jmpEffect]

set_option maxHeartbeats 800000 in
theorem tail_setup [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = tailSetupPC v) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ t.RIP = byteAddress v ∧ AgreesExcept clobbers s t ∧
      (Operand.reg 0 : Operand 64).read t = (Operand.reg 0 : Operand 64).read s ∧
      (Operand.reg 1 : Operand 64).read t = 0 ∧
      (Operand.reg 15 : Operand 64).read t = (Operand.reg 15 : Operand 64).read s +
        (Operand.reg 2 : Operand 64).read s ∧
      (Operand.reg 3 : Operand 64).read t = (Operand.reg 3 : Operand 64).read s +
        ((Operand.reg 13 : Operand 64).read s + (Operand.reg 2 : Operand 64).read s) ∧
      (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s := by
  obtain ⟨s1,a1,r1,l1,b1,e1,o1,f1⟩ := advance
    (effect := addR64R64Effect (tailSetupPC v) 15 2)
    (add_r64_r64_effect_step _ 0x49 0xd7 (by unfold RexWPrefix; decide) (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [addR64R64Effect,Write.Full,Operand.Full])
    (by intro a b h; simp only [addR64R64Effect,h.read_reg])
    (by simp [clobbers]) (by next_pc v) ready loaded sp ip (Obs.refl s)
  obtain ⟨s2,a2,r2,l2,b2,e2,o2,f2⟩ := advance
    (effect := addR64R64Effect (tailSetupPC v + 3) 13 2)
    (add_r64_r64_effect_step _ 0x49 0xd5 (by unfold RexWPrefix; decide) (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [addR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64R64Effect, h.read_reg])
    (by simp [clobbers]) (by next_pc v) r1 l1 b1 e1.rip o1
  obtain ⟨s3,a3,r3,l3,b3,e3,o3,f3⟩ := advance
    (effect := addR64R64Effect (tailSetupPC v + 6) 3 13)
    (add_r64_r64_effect_step _ 0x4c 0xeb (by unfold RexWPrefix; decide) (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [addR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [addR64R64Effect, h.read_reg])
    (by simp [clobbers]) (by next_pc v) r2 l2 b2
    (by simpa only [addR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e2.rip) o2
  obtain ⟨s4,a4,r4,l4,b4,e4,o4,f4⟩ := advance
    (effect := xorR32R32Effect (tailSetupPC v + 9) 2 1 1)
    (xor_r32_r32_effect_step _ 0xc9 (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [xorR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [xorR32R32Effect, h.read_reg])
    (by simp [clobbers]) (by next_pc v) r3 l3 b3
    (by simpa only [addR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e3.rip) o3
  obtain ⟨s5,a5,r5,l5,b5,e5,o5,f5⟩ := advance
    (nop_m_effect_step (tailSetupPC v + 11) [0x66,0x66,0x66,0x66,0x2e]
      (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0))
      (by decide) (by decide) (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [nopEffect]) (by intro a b h; rfl)
    (by simp [nopEffect,Effect.components,clobbers]) (by cases v <;> decide +kernel)
    r4 l4 b4
    (by simpa only [xorR32R32Effect,BitVec.add_assoc,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using e4.rip) o4
  refine ⟨s5,a1.trans (a2.trans (a3.trans (a4.trans a5))),r5,l5,b5,?_,
    frame_trans f1 (frame_trans f2 (frame_trans f3 (frame_trans f4 f5))),?_,?_,?_,?_,?_⟩
  · have hh := e5.rip
    cases v <;> exact hh
  all_goals
    first | rw [← o5.read_reg] | rw [← o5.read_mem]
    x86_norm [addR64R64Effect,xorR32R32Effect,nopEffect,BitVec.xor_self]

theorem finish [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (r : Fin 200) (s : RamState) (ready : ReadyToStep s)
    (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = finishPC v)
    (hr : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 r.val) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ¬ InProgram boundary.rip ∧ t.RIP = cursorWriteAddress v ∧
      (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 r.val ∧
      AgreesExcept [.reg 1,.rip] s t := by
  obtain ⟨s1,a1,r1,l1,b1,e1,o1,f1⟩ := advance
    (effect := movR32R32Effect (finishPC v) 3 1 12)
    (mov_r32_r32_rex_effect_step _ 0x44 0xe1 (by unfold RexNoWPrefix; decide) (by decide))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [movR32R32Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR32R32Effect, h.read_reg])
    (by simp [clobbers]) (by next_pc v) ready loaded sp ip (Obs.refl s)
  obtain ⟨s2,a2,r2,l2,b2,e2,o2,f2⟩ := advance
    (jmp_rel8_effect_step (finishPC v + 3) 0x7e (by cases v <;> decide +kernel))
    (by unfold ImageAt; cases v <;> decide +kernel)
    (by intro t; simp [jmpEffect]) (by intro a b h; rfl)
    (by simp [jmpEffect, Effect.components, clobbers]) (by next_pc v) r1 l1 b1 e1.rip o1
  refine ⟨s2,a1.trans a2,r2,l2,b2,?_,?_,?_⟩
  · have hh := e2.rip
    cases v <;> exact hh
  · first | rw [← o2.read_reg] | rw [← o2.read_mem]
    x86_norm [movR32R32Effect, jmpEffect]
    change (((Operand.reg 12 : Operand 64).read s).setWidth 32).setWidth 64 = _
    rw [hr]
    have hi := r.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · apply (e1.agrees.trans e2.agrees).mono
    simp [jmpEffect, Effect.components, movR32R32Effect]

theorem dispatch [Bindings] {boundary : ReturnBoundary} (v : Variant)
    (r : Fin (v.rate)) (s : RamState) (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (sp : ¬ InProgram boundary.rip) (ip : s.RIP = tailAddress v)
    (hr : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 r.val)
    (hread : MemReadable s ((Operand.reg 4 : Operand 64).read s) 8) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      AgreesExcept clobbers s t ∧
      (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s ∧
      (Operand.reg 4 : Operand 64).read t = (Operand.reg 4 : Operand 64).read s ∧
      (Operand.reg 3 : Operand 64).read t = (Operand.reg 3 : Operand 64).read s ∧
      (Operand.reg 13 : Operand 64).read t = (Operand.reg 13 : Operand 64).read s ∧
      (Operand.reg 15 : Operand 64).read t = (Operand.reg 15 : Operand 64).read s ∧
      (Operand.reg 7 : Operand 64).read t =
        (Operand.mem ((Operand.reg 4 : Operand 64).read s) : Operand 64).read s ∧
      ((r.val = 0 ∧ t.RIP = cursorWriteAddress v ∧
        (Operand.reg 1 : Operand 64).read t = 0) ∨
       (0 < r.val ∧ r.val < 4 ∧ t.RIP = tailSetupPC v ∧
        (Operand.reg 0 : Operand 64).read t = BitVec.ofNat 64 (r.val % 4) ∧
        (Operand.reg 2 : Operand 64).read t = 0) ∨
       (4 ≤ r.val ∧ t.RIP = chunkAddress v ∧
        (Operand.reg 0 : Operand 64).read t = BitVec.ofNat 64 (r.val % 4) ∧
        (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 (r.val / 4 * 4) ∧
        (Operand.reg 2 : Operand 64).read t = 0 ∧
        (Operand.reg 6 : Operand 64).read t =
          (Operand.reg 3 : Operand 64).read s + (Operand.reg 13 : Operand 64).read s + 3)) := by
  obtain ⟨s1,a1,r1,l1,b1,ip1,o1,f1⟩ := entry_test v s ready loaded sp ip
  have hr1 : (Operand.reg 12 : Operand 64).read s1 = BitVec.ofNat 64 r.val :=
    (o1.read_reg _).symm.trans hr
  have bound : r.val < 200 := by
    have h := r.isLt
    cases v <;> simp only [Variant.rate, Variant.lanes] at h <;> omega
  by_cases hz : r.val = 0
  · have hrs : (Operand.reg 12 : Operand 64).read s = 0 := by simpa [hz] using hr
    have hp : s1.RIP = tailAddress v + (25 : BitVec 64) := by
      rw [hrs] at ip1
      simpa using ip1
    obtain ⟨s2,a2,r2,l2,b2,ip2,hr2,cur2,f2⟩ := zero_setup v s1 r1 l1 b1 hp (stack_read_frame f1 hread)
    have frame := frame_trans f1 (f2.mono (by simp [clobbers]))
    refine ⟨_,s2,a1.trans a2,r2,l2,frame,?_,frame.read (by simp [clobbers]),
      (f2.read (by decide)).trans (o1.read_reg _).symm,
      (f2.read (by decide)).trans (o1.read_reg _).symm,
      (f2.read (by decide)).trans (o1.read_reg _).symm,?_,Or.inl ⟨hz,ip2,hr2⟩⟩
    · exact (f2.read (by decide)).trans (o1.read_reg _).symm
    · rw [cur2,← o1.read_mem]
      first | rw [← o1.read_reg] | rw [← o1.read_mem]
  · have hn : ((Operand.reg 12 : Operand 64).read s == 0) = false := by
      rw [hr]
      apply Bool.eq_false_iff.mpr
      intro he
      have he' : BitVec.ofNat 64 r.val = (0 : BitVec 64) := eq_of_beq he
      have hh := congrArg BitVec.toNat he'
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show r.val < 2^64 by omega)] at hh
      exact hz hh
    have hp : s1.RIP = tailAddress v + (5 : BitVec 64) := by
      simpa only [hn,Bool.false_eq_true,↓reduceIte] using ip1
    obtain ⟨s2,a2,r2,l2,b2,ip2,rax2,cur2,f2⟩ :=
      dispatch_compare v ⟨r.val,bound⟩ s1 r1 l1 b1 hp hr1 (stack_read_frame f1 hread)
    have hr2 : (Operand.reg 12 : Operand 64).read s2 = BitVec.ofNat 64 r.val :=
      (f2.read (by decide)).trans hr1
    have rb2 : (Operand.reg 3 : Operand 64).read s2 = (Operand.reg 3 : Operand 64).read s :=
      (f2.read (by decide)).trans (o1.read_reg _).symm
    have full2 : (Operand.reg 13 : Operand 64).read s2 = (Operand.reg 13 : Operand 64).read s :=
      (f2.read (by decide)).trans (o1.read_reg _).symm
    have ff2 := frame_trans f1 (f2.mono (by simp [clobbers]))
    by_cases hc : 4 ≤ r.val
    · obtain ⟨fuel3,s3,a3,r3,l3,b3,ip3,rcx3,rdx3,rsi3,f3⟩ :=
        chunk_setup v r s2 r2 l2 b2 (by simpa only [hc,↓reduceIte] using ip2) hr2
      have frame := frame_trans ff2 (f3.mono (by simp [clobbers]))
      refine ⟨_,s3,a1.trans (a2.trans a3),r3,l3,frame,?_,frame.read (by simp [clobbers]),
        (f3.read (by decide)).trans rb2,(f3.read (by decide)).trans full2,
        (f3.read (by decide)).trans ((f2.read (by decide)).trans (o1.read_reg _).symm),?_,
        Or.inr (Or.inr ⟨hc,ip3,(f3.read (by decide)).trans rax2,rcx3,rdx3,?_⟩)⟩
      · exact (f3.read (by decide)).trans (hr2.trans hr.symm)
      · rw [f3.read (by decide),cur2,← o1.read_mem]
        first | rw [← o1.read_reg] | rw [← o1.read_mem]
      · simpa only [rb2,full2, BitVec.add_comm] using rsi3
    · obtain ⟨s3,a3,r3,l3,b3,ip3,rdx3,f3⟩ := short_setup v s2 r2 l2 b2
        (by simpa only [hc,↓reduceIte] using ip2)
      have frame := frame_trans ff2 (f3.mono (by simp [clobbers]))
      refine ⟨_,s3,a1.trans (a2.trans a3),r3,l3,frame,?_,frame.read (by simp [clobbers]),
        (f3.read (by decide)).trans rb2,(f3.read (by decide)).trans full2,
        (f3.read (by decide)).trans ((f2.read (by decide)).trans (o1.read_reg _).symm),?_,
        Or.inr (Or.inl ⟨by omega,by omega,ip3,(f3.read (by decide)).trans rax2,rdx3⟩)⟩
      · exact (f3.read (by decide)).trans (hr2.trans hr.symm)
      · rw [f3.read (by decide),cur2,← o1.read_mem]
        first | rw [← o1.read_reg] | rw [← o1.read_mem]

end Sha3.Proofs.Update.Tail.Setup
