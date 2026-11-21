import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Machine.StackRegion
import Hkdf.Proofs.Common.EffectCompose.Advance
import Hkdf.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller.Prepare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Instructions (cmovR64R64Effect cmov_r64_r64_effect_step)

def middleBytes (d : BitVec 32) : List UInt8 :=
  encodeMovM64Imm32 (.sib 4 none 0 (.d32 (d + 24))) 0 ++
  encodeMovM64Imm32 (.sib 4 none 0 (.d32 (d + 16))) 0 ++
  encodeMovM64Imm32 (.sib 4 none 0 (.d32 (d + 8))) 0 ++
  [0x48, 0x85, 0xc9, 0x48, 0x8d, 0xb4, 0x24] ++ immBytes 32 d ++
  [0x48, 0x0f, 0x45, 0xf1] ++
  encodeMovM64Imm32 (.sib 4 none 0 (.d32 d)) 0 ++
  [0xba, 0x20, 0, 0, 0, 0x49, 0x0f, 0x45, 0xd0]

structure MiddlePre (p : BitVec 64) (d : BitVec 32) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : ∀ o ∈ ([0, 8, 16, 24] : List (BitVec 32)),
    MemWritable s (rspOf s + (d + o).signExtend 64) 8
  apart : ∀ o ∈ ([0, 8, 16, 24] : List (BitVec 32)),
    RangeApart (rspOf s + (d + o).signExtend 64) 8 p 72

def middleEffect (p : BitVec 64) (d : BitVec 32) (s : RamState) : Effect :=
  { rip := p + 72
    writes := [
      ⟨(.mem (rspOf s + (d + 24).signExtend 64) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + (d + 16).signExtend 64) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + (d + 8).signExtend 64) : Operand 64), 0⟩,
      ⟨(.reg 6 : Operand 64), if (Operand.reg 1 : Operand 64).read s = 0 then rspOf s + d.signExtend 64 else (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + d.signExtend 64) : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), if (Operand.reg 1 : Operand 64).read s = 0 then 32 else (Operand.reg 8 : Operand 64).read s⟩]
    flags := some (testFlags ((Operand.reg 1 : Operand 64).read s)) }

theorem cmovne_local (p : BitVec 64) (dst src : BitVec 5) :
    Hkdf.Proofs.Common.EffectCompose.Effect.LocalOn [.ZF] (cmovR64R64Effect p 5 dst src) := by
  apply Hkdf.Proofs.Common.EffectCompose.Effect.LocalOn.of_eq
  · intro s t ho hf
    have zf := hf .ZF (by simp)
    change s.RFLAGS.getLsbD 6 = t.RFLAGS.getLsbD 6 at zf
    simp only [cmovR64R64Effect, Hkdf.Proofs.Common.Instructions.cmovR64R64Value,
      condHolds, BitVec.reduceToNat, StatusFlags.ofRFLAGS, ho.read_reg, zf]
  · intro s w hw
    simp only [cmovR64R64Effect, List.mem_singleton] at hw
    subst w
    rfl

attribute [local x86_compose] cmovR64R64Effect Hkdf.Proofs.Common.Instructions.cmovR64R64Value testR64R64Effect testFlags condHolds BitVec.and_self

macro "middle_proof " p:term ", " d:term ", " continuation:term : tactic => `(tactic| (
  dsimp only [middleBytes]
  advance_begin (mov_m64_imm32_effect_step $p 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 ($d+24))) (by constructor <;> simp [AddrMode.Valid]) rfl rfl 0)
  try (case sub => exact codeRange_slice_subset $p (middleBytes $d) 0 12)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable 24 (by simp), (h.apart 24 (by simp)).sub0 12 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_of_components_mem_rip
      (a := rspOf s + (($d+24 : BitVec 32)).signExtend 64) (len := 8) (by simp [movM64Imm32Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, Operand.read_reg64, stackPtr])
    change RangeApart _ 8 $p 72
    exact h.apart 24 (by simp)
  case next => intro s h; x86_norm [BitVec.add_assoc]; exact $continuation 12 (by decide)
  advance_then (mov_m64_imm32_effect_step ($p+12) 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 ($d+16))) (by constructor <;> simp [AddrMode.Valid]) rfl rfl 0)
  try (case sub => exact codeRange_slice_subset $p (middleBytes $d) 12 12)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact (hP.apart 16 (by simp)).sub 12 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_of_components_mem_rip
        (a := rspOf s + (($d+16 : BitVec 32)).signExtend 64) (len := 8) (by x86_norm)
      change RangeApart _ 8 $p 72
      exact hP.apart 16 (by simp)
    · x86_norm [BitVec.add_assoc]; exact $continuation 24 (by decide)

  advance_then (mov_m64_imm32_effect_step ($p+24) 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 ($d+8))) (by constructor <;> simp [AddrMode.Valid]) rfl rfl 0)
  try (case sub => exact codeRange_slice_subset $p (middleBytes $d) 24 12)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact (hP.apart 8 (by simp)).sub 24 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_of_components_mem_rip
        (a := rspOf s + (($d+8 : BitVec 32)).signExtend 64) (len := 8) (by x86_norm)
      change RangeApart _ 8 $p 72
      exact hP.apart 8 (by simp)
    · x86_norm [BitVec.add_assoc]; exact $continuation 36 (by decide)

  advance_then (show StepEffect (fun (s : RamState) => s.RIP = BitVec.add $p 36)
    (codeRange ($p+36) [0x48,0x85,0xc9]) (testR64R64Effect ($p+36) 1 1) from
    test_r64_r64_effect_step ($p+36) 0x48 0xc9 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset $p (middleBytes $d) 36 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm; try rfl), Effect.Avoids.of_noMem (by simp [cmovR64R64Effect, testR64R64Effect, leaR64Effect, movR32Imm32Effect, Effect.components, Component.Covers]) _, ?_⟩
    x86_norm [BitVec.add_assoc]; exact $continuation 39 (by decide)

  advance_then (lea_r64_effect_step ($p+39) 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 $d)) (by constructor <;> simp [AddrMode.Valid]) rfl rfl)
  try (case sub => exact codeRange_slice_subset $p (middleBytes $d) 39 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm; try rfl), Effect.Avoids.of_noMem (by simp [cmovR64R64Effect, testR64R64Effect, leaR64Effect, movR32Imm32Effect, Effect.components, Component.Covers]) _, ?_⟩
    x86_norm [BitVec.add_assoc]; exact $continuation 47 (by decide)

  advance_then_on [.ZF] using (show StepEffect (fun (s : RamState) => s.RIP = BitVec.add $p 47)
    (codeRange ($p+47) [0x48,0x0f,0x45,0xf1]) (cmovR64R64Effect ($p+47) 5 6 1) from
    cmov_r64_r64_effect_step ($p+47) 0x48 0x45 0xf1
      (by simp [RexWPrefix]) (Or.inr rfl) (by decide))
  case loc => exact cmovne_local ($p+47) 6 1
  try (case sub => exact codeRange_slice_subset $p (middleBytes $d) 47 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm; try rfl), Effect.Avoids.of_noMem (by simp [cmovR64R64Effect, testR64R64Effect, leaR64Effect, movR32Imm32Effect, Effect.components, Component.Covers]) _, ?_⟩
    x86_norm [BitVec.add_assoc]; exact $continuation 51 (by decide)

  advance_then (mov_m64_imm32_effect_step ($p+51) 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 $d)) (by constructor <;> simp [AddrMode.Valid]) rfl rfl 0)
  try (case sub => exact codeRange_slice_subset $p (middleBytes $d) 51 12)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact (hP.apart 0 (by simp)).sub 51 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_of_components_mem_rip
        (a := rspOf s + ($d : BitVec 32).signExtend 64) (len := 8) (by x86_norm)
      change RangeApart _ 8 $p 72
      exact hP.apart 0 (by simp)
    · x86_norm [BitVec.add_assoc]; exact $continuation 63 (by decide)

  advance_then (mov_r32_imm32_effect_step ($p+63) 0xba (by decide) 32)
  try (case sub => exact codeRange_slice_subset $p (middleBytes $d) 63 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm; try rfl), Effect.Avoids.of_noMem (by simp [cmovR64R64Effect, testR64R64Effect, leaR64Effect, movR32Imm32Effect, Effect.components, Component.Covers]) _, ?_⟩
    x86_norm [BitVec.add_assoc]; exact $continuation 68 (by decide)

  advance_then_on [.ZF] using (show StepEffect (fun (s : RamState) => s.RIP = BitVec.add $p 68)
    (codeRange ($p+68) [0x49,0x0f,0x45,0xd0]) (cmovR64R64Effect ($p+68) 5 2 8) from
    cmov_r64_r64_effect_step ($p+68) 0x49 0x45 0xd0
      (by simp [RexWPrefix]) (Or.inr rfl) (by decide))
  case loc => exact cmovne_local ($p+68) 2 8
  try (case sub => exact codeRange_slice_subset $p (middleBytes $d) 68 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm; try rfl), Effect.Avoids.of_noMem (by simp [cmovR64R64Effect, testR64R64Effect, leaR64Effect, movR32Imm32Effect, Effect.components, Component.Covers]) _, ?_⟩
    x86_norm [BitVec.add_assoc]; exact $continuation 72 (by decide)

  advance_finish [middleEffect, BitVec.and_self, BitVec.add_assoc, rspOf, ite_not]

))

set_option maxHeartbeats 1800000 in
theorem middle_run [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (d : BitVec 32)
    (displacement : d = 256 ∨ d = 296)
    (next : ∀ i : Nat, i ≤ 72 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (MiddlePre p d) (codeRange p (middleBytes d))
      (Effect.post (middleEffect p d)) := by
  rcases displacement with rfl | rfl
  · middle_proof p, 256, next
  · middle_proof p, 296, next

theorem middle_words {s t : RamState} {p : BitVec 64} {d : BitVec 32}
    (effect : (middleEffect p d s).Holds s t) (displacement : d = 256 ∨ d = 296) :
    ∀ j < 4, memLoad t.external
      (rspOf s + d.signExtend 64 + BitVec.ofNat 64 (8*j)) 64 = 0 := by
  have stores := effect.writes
  simp only [middleEffect, Write.AllHold, Operand.read, rspOf] at stores
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, rspOf,
      Operand.read, BitVec.setWidth_eq] using stores.2.2.2.2.1
  · rcases displacement with rfl | rfl
    all_goals simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
      BitVec.reduceSignExtend, BitVec.add_assoc, rspOf, Operand.read, BitVec.setWidth_eq] using stores.2.2.1
  · rcases displacement with rfl | rfl
    all_goals simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
      BitVec.reduceSignExtend, BitVec.add_assoc, rspOf, Operand.read, BitVec.setWidth_eq] using stores.2.1
  · rcases displacement with rfl | rfl
    all_goals simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
      BitVec.reduceSignExtend, BitVec.add_assoc, rspOf, Operand.read, BitVec.setWidth_eq] using stores.1

theorem middle_zero_bytes {s t : RamState} {p : BitVec 64} {d : BitVec 32}
    (effect : (middleEffect p d s).Holds s t) (displacement : d = 256 ∨ d = 296)
    (read : MemReadable t (rspOf s + d.signExtend 64) 32) :
    (⟨(rspOf s + d.signExtend 64).toNat, 32⟩ : MemoryRegion).HasBytes t.external
      ⟨Array.replicate 32 0⟩ := by
  have bytes : Bytes t.external (rspOf s + d.signExtend 64) 32 (fun _ => 0) := by
    intro i hi
    have chunk := Bytes.of_memLoad (n := 64) (m := t.external)
      (a := rspOf s + d.signExtend 64 + BitVec.ofNat 64 (8*(i/8))) (by
        intro j hj
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact read.mem _ (by omega))
    rw [middle_words effect displacement (i/8) (by omega)] at chunk
    have byte := chunk (i%8) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8)+i%8 = i by omega] at byte
    simpa [storedByte] using byte
  refine ⟨rfl, ?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [ByteArray.size, Array.size_replicate] using i.isLt
  have byte := bytes i.val hi
  change t.external[BitVec.ofNat 64 ((rspOf s + d.signExtend 64).toNat + i.val)]? =
    some ((Array.replicate 32 (0 : UInt8))[i.val])
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact byte.trans (congrArg some (Array.getElem_replicate
    (n := 32) (v := (0 : UInt8)) (i := i.val) (by simpa only [Array.size_replicate] using hi)).symm)

theorem middle_registers {s t : RamState} {p : BitVec 64} {d : BitVec 32}
    (effect : (middleEffect p d s).Holds s t) :
    t.RIP = p + (72 : BitVec 64) ∧ stackPtr t = stackPtr s ∧
      (Operand.reg 6 : Operand 64).read t =
        (if (Operand.reg 1 : Operand 64).read s = 0 then rspOf s + d.signExtend 64
          else (Operand.reg 1 : Operand 64).read s) ∧
      (Operand.reg 2 : Operand 64).read t =
        (if (Operand.reg 1 : Operand 64).read s = 0 then 32 else (Operand.reg 8 : Operand 64).read s) := by
  have stores := effect.writes
  simp only [middleEffect, Write.AllHold] at stores
  refine ⟨effect.rip, effect.agrees.read (n := 64) (r := 4) ?_, stores.2.2.2.1, stores.2.2.2.2.2⟩
  simp [middleEffect, Effect.components, Write.component, Operand.component]

def middleOffset (simple : Bool) : Nat := if simple then 0x5c9c else 0x1445

def saltDisplacement (simple : Bool) : Nat := if simple then 256 else 296

def allocation (simple : Bool) : Nat := if simple then 536 else 520

theorem stack_offset_address (base total offset : BitVec 64) :
    base - total + offset = base - (total - offset) := by
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

theorem middle_pre_of_stack [bindings : Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {reserve : Nat} (simple : Bool)
    (stack : Stack.Valid initial reserve)
    (avoid : (Stack.region initial reserve).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a))
    (running : CallFrame.Running initial boundary #v[Stack.region initial reserve] s)
    (enough : allocation simple ≤ reserve)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 (middleOffset simple))
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (allocation simple)) :
    MiddlePre (Extracted.textAddress + BitVec.ofNat 64 (middleOffset simple))
      (BitVec.ofNat 32 (saltDisplacement simple)) s := by
  refine ⟨rip, ?_, ?_⟩
  · intro o member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals rw [show rspOf s = stackPtr s from Operand.read_reg64 s 4, rsp]
    all_goals cases simple
    all_goals simp only [allocation, saltDisplacement, Bool.false_eq_true, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSignExtend]
    all_goals rw [stack_offset_address]
    all_goals simp only [BitVec.reduceSub]
    · exact CallFrame.stack_writable8 stack avoid running.allocated
        (offset := 224) (by dsimp [allocation] at enough; omega) (by decide)
    · exact CallFrame.stack_writable8 stack avoid running.allocated
        (offset := 280) (by dsimp [allocation] at enough; omega) (by decide)
    · exact CallFrame.stack_writable8 stack avoid running.allocated
        (offset := 216) (by dsimp [allocation] at enough; omega) (by decide)
    · exact CallFrame.stack_writable8 stack avoid running.allocated
        (offset := 272) (by dsimp [allocation] at enough; omega) (by decide)
    · exact CallFrame.stack_writable8 stack avoid running.allocated
        (offset := 208) (by dsimp [allocation] at enough; omega) (by decide)
    · exact CallFrame.stack_writable8 stack avoid running.allocated
        (offset := 264) (by dsimp [allocation] at enough; omega) (by decide)
    · exact CallFrame.stack_writable8 stack avoid running.allocated
        (offset := 200) (by dsimp [allocation] at enough; omega) (by decide)
    · exact CallFrame.stack_writable8 stack avoid running.allocated
        (offset := 256) (by dsimp [allocation] at enough; omega) (by decide)
  · intro o member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals rw [show rspOf s = stackPtr s from Operand.read_reg64 s 4, rsp]
    all_goals cases simple
    all_goals simp only [allocation, saltDisplacement, middleOffset, Bool.false_eq_true,
      ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSignExtend]
    all_goals rw [stack_offset_address]
    all_goals simp only [BitVec.reduceSub]
    · exact CallFrame.stack_codeApart stack (fun a ha inside => avoid a ha (.inl inside))
        (offset := 224) (len := 8) (codeLen := 72) (codeOffset := 0x1445)
        (by dsimp [allocation] at enough; omega) (by decide) (by decide)
    · exact CallFrame.stack_codeApart stack (fun a ha inside => avoid a ha (.inl inside))
        (offset := 280) (len := 8) (codeLen := 72) (codeOffset := 0x5c9c)
        (by dsimp [allocation] at enough; omega) (by decide) (by decide)
    · exact CallFrame.stack_codeApart stack (fun a ha inside => avoid a ha (.inl inside))
        (offset := 216) (len := 8) (codeLen := 72) (codeOffset := 0x1445)
        (by dsimp [allocation] at enough; omega) (by decide) (by decide)
    · exact CallFrame.stack_codeApart stack (fun a ha inside => avoid a ha (.inl inside))
        (offset := 272) (len := 8) (codeLen := 72) (codeOffset := 0x5c9c)
        (by dsimp [allocation] at enough; omega) (by decide) (by decide)
    · exact CallFrame.stack_codeApart stack (fun a ha inside => avoid a ha (.inl inside))
        (offset := 208) (len := 8) (codeLen := 72) (codeOffset := 0x1445)
        (by dsimp [allocation] at enough; omega) (by decide) (by decide)
    · exact CallFrame.stack_codeApart stack (fun a ha inside => avoid a ha (.inl inside))
        (offset := 264) (len := 8) (codeLen := 72) (codeOffset := 0x5c9c)
        (by dsimp [allocation] at enough; omega) (by decide) (by decide)
    · exact CallFrame.stack_codeApart stack (fun a ha inside => avoid a ha (.inl inside))
        (offset := 200) (len := 8) (codeLen := 72) (codeOffset := 0x1445)
        (by dsimp [allocation] at enough; omega) (by decide) (by decide)
    · exact CallFrame.stack_codeApart stack (fun a ha inside => avoid a ha (.inl inside))
        (offset := 256) (len := 8) (codeLen := 72) (codeOffset := 0x5c9c)
        (by dsimp [allocation] at enough; omega) (by decide) (by decide)

theorem middle_writesWithin {initial s : RamState} {reserve : Nat} (simple : Bool)
    (stack : Stack.Valid initial reserve) (enough : allocation simple ≤ reserve)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (allocation simple)) :
    WritesWithin (middleEffect
      (Extracted.textAddress + BitVec.ofNat 64 (middleOffset simple))
      (BitVec.ofNat 32 (saltDisplacement simple)) s).components
      #v[Stack.region initial reserve] := by
  intro c hc a ha
  simp only [middleEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
    Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals refine ⟨Stack.region initial reserve, by simp, ?_⟩
  all_goals rw [show rspOf s = stackPtr s from Operand.read_reg64 s 4, rsp] at ha
  all_goals cases simple
  all_goals simp only [allocation, saltDisplacement, Bool.false_eq_true, ↓reduceIte,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSignExtend] at ha
  all_goals rw [stack_offset_address] at ha
  all_goals simp only [BitVec.reduceSub] at ha
  · exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub stack.2.2.1
      (offset := 200) (by dsimp [allocation] at enough; omega) (by decide) ha
  · exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub stack.2.2.1
      (offset := 256) (by dsimp [allocation] at enough; omega) (by decide) ha
  · exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub stack.2.2.1
      (offset := 208) (by dsimp [allocation] at enough; omega) (by decide) ha
  · exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub stack.2.2.1
      (offset := 264) (by dsimp [allocation] at enough; omega) (by decide) ha
  · exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub stack.2.2.1
      (offset := 216) (by dsimp [allocation] at enough; omega) (by decide) ha
  · exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub stack.2.2.1
      (offset := 272) (by dsimp [allocation] at enough; omega) (by decide) ha
  · exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub stack.2.2.1
      (offset := 224) (by dsimp [allocation] at enough; omega) (by decide) ha
  · exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub stack.2.2.1
      (offset := 280) (by dsimp [allocation] at enough; omega) (by decide) ha

theorem middle_run_stack [bindings : Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {reserve : Nat} (simple : Bool)
    (stack : Stack.Valid initial reserve)
    (avoid : (Stack.region initial reserve).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a))
    (running : CallFrame.Running initial boundary #v[Stack.region initial reserve] s)
    (enough : allocation simple ≤ reserve) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 (middleOffset simple))
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (allocation simple)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CallFrame.Running initial boundary #v[Stack.region initial reserve] t ∧
      (middleEffect (Extracted.textAddress + BitVec.ofNat 64 (middleOffset simple))
        (BitVec.ofNat 32 (saltDisplacement simple)) s).Holds s t := by
  have code := programText_slice (programLoaded_codeIn running.loaded) (middleOffset simple)
    (middleBytes (BitVec.ofNat 32 (saltDisplacement simple)))
    (by cases simple <;> decide) (by cases simple <;> decide +kernel)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := middle_run boundary
    (Extracted.textAddress + BitVec.ofNat 64 (middleOffset simple))
    (BitVec.ofNat 32 (saltDisplacement simple))
    (by cases simple <;> decide) (by
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact boundary_ne_program outside (inProgram_of_textOffset _ (by
        cases simple <;> simp only [middleOffset, ↓reduceIte, Bool.false_eq_true] <;> omega)))
    s (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep running.machine) code
    (middle_pre_of_stack simple stack avoid running enough rip rsp)
  refine ⟨fuel, t, run, ready, running.of_agrees run ready effect.agrees
    (middle_writesWithin simple stack enough rsp) ?_ ?_, effect⟩
  · intro region member a contains inside
    have eq : region = Stack.region initial reserve := by simpa using member
    subst region
    exact avoid a contains (.inl inside)
  · simp [middleEffect, Effect.components, Write.component, Operand.component]

def outputOffset (simple : Bool) : Nat := if simple then 0x5ce4 else 0x148d

def callOffset (simple : Bool) : Nat := if simple then 0x5ce7 else 0x1492

def outputBytes (simple : Bool) : List UInt8 :=
  if simple then [0x48,0x89,0xe7] else [0x48,0x8d,0x7c,0x24,0x78]

def outputEffect (simple : Bool) (s : RamState) : Effect :=
  { rip := Extracted.textAddress + BitVec.ofNat 64 (callOffset simple)
    writes := [⟨(.reg 7 : Operand 64), (if simple then rspOf s else rspOf s + 120)⟩] }

theorem output_effect_step [Bindings] (simple : Bool) :
    StepEffect (fun (s : RamState) => s.RIP =
      Extracted.textAddress + BitVec.ofNat 64 (outputOffset simple))
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 (outputOffset simple))
        (outputBytes simple)) (outputEffect simple) := by
  cases simple
  · exact lea_r64_effect_step 0x10148d 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl
  · exact mov_r64_r64_effect_step 0x105ce4 0x48 0xe7 (by simp [RexWPrefix]) (by decide)

theorem output_run [bindings : Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {n : Nat} {regions : Vector MemoryRegion n}
    (simple : Bool) (running : CallFrame.Running initial boundary regions s)
    (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 (outputOffset simple)) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CallFrame.Running initial boundary regions t ∧
      (outputEffect simple s).Holds s t := by
  obtain ⟨t, run, ready, effect⟩ := (output_effect_step simple).advances
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep running.machine)
    (programText_slice (programLoaded_codeIn running.loaded) (outputOffset simple)
      (outputBytes simple) (by cases simple <;> decide)
      (by cases simple <;> decide +kernel)) rip (by
        change Extracted.textAddress + BitVec.ofNat 64 (callOffset simple) ≠ boundary.rip
        exact boundary_ne_program outside
          (inProgram_of_textOffset _ (by cases simple <;> decide)))
  have memory := effect.agrees.external
    (by simp [outputEffect, Effect.components, Component.Covers])
  obtain ⟨previous, before⟩ := running.execution
  refine ⟨t, run, ready, ?_, effect⟩
  refine ⟨⟨previous+1, before.trans run⟩,
    Hkdf.Proofs.Common.Machine.supportedMachine_of_ready_agrees running.machine ready effect.agrees,
    ?_, ?_, ?_, ?_⟩
  · intro a byte member
    rw [memory]
    exact running.loaded a byte member
  · intro a allocated
    rw [memory]
    exact running.allocated a allocated
  · exact effect.agrees.directionFlagClear
      (by simp [outputEffect, Effect.components, Write.component, Operand.component])
      running.directionFlag
  · intro a apart
    rw [memory]
    exact running.frame a apart

theorem default_readable {initial s t : RamState} {reserve : Nat} (simple : Bool)
    (stack : Stack.Valid initial reserve) (enough : allocation simple ≤ reserve)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (allocation simple))
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome) :
    MemReadable t (rspOf s + (BitVec.ofNat 32 (saltDisplacement simple)).signExtend 64) 32 := by
  rw [show rspOf s = stackPtr s from Operand.read_reg64 s 4, rsp]
  cases simple
  all_goals simp only [allocation, saltDisplacement, Bool.false_eq_true, ↓reduceIte,
    BitVec.reduceSignExtend]
  all_goals rw [stack_offset_address]
  all_goals simp only [BitVec.reduceSub]
  · exact CallFrame.stack_readable stack grow (offset := 224)
      (by dsimp [allocation] at enough; omega) (by decide)
  · exact CallFrame.stack_readable stack grow (offset := 280)
      (by dsimp [allocation] at enough; omega) (by decide)

theorem run [bindings : Bindings] {initial s : RamState}
    {boundary : ReturnBoundary} {reserve : Nat} (simple : Bool)
    (stack : Stack.Valid initial reserve)
    (avoid : (Stack.region initial reserve).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a))
    (running : CallFrame.Running initial boundary #v[Stack.region initial reserve] s)
    (enough : allocation simple ≤ reserve) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 (middleOffset simple))
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (allocation simple)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CallFrame.Running initial boundary #v[Stack.region initial reserve] t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 (callOffset simple) ∧
      stackPtr t = stackPtr s ∧
      (Operand.reg 7 : Operand 64).read t = (if simple then rspOf s else rspOf s + 120) ∧
      (Operand.reg 6 : Operand 64).read t =
        (if (Operand.reg 1 : Operand 64).read s = 0 then
          rspOf s + (BitVec.ofNat 32 (saltDisplacement simple)).signExtend 64
        else (Operand.reg 1 : Operand 64).read s) ∧
      (Operand.reg 2 : Operand 64).read t =
        (if (Operand.reg 1 : Operand 64).read s = 0 then 32 else (Operand.reg 8 : Operand 64).read s) ∧
      (⟨(rspOf s + (BitVec.ofNat 32 (saltDisplacement simple)).signExtend 64).toNat, 32⟩ :
        MemoryRegion).HasBytes t.external ⟨Array.replicate 32 0⟩ ∧
      AgreesExcept ((middleEffect
        (Extracted.textAddress + BitVec.ofNat 64 (middleOffset simple))
        (BitVec.ofNat 32 (saltDisplacement simple)) s).components ++ [.reg 7, .rip]) s t := by
  obtain ⟨fuel, u, runU, _, runningU, effectU⟩ :=
    middle_run_stack simple stack avoid running enough outside rip rsp
  obtain ⟨ripU, rspU, inputU, lengthU⟩ := middle_registers effectU
  have atOutput : u.RIP = Extracted.textAddress + BitVec.ofNat 64 (outputOffset simple) := by
    rw [ripU]
    cases simple <;> decide +kernel
  obtain ⟨t, runT, readyT, runningT, effectT⟩ := output_run simple runningU outside atOutput
  have frameT : AgreesExcept [.reg 7, .rip] u t := by
    apply effectT.agrees.mono
    intro c hc
    simp only [outputEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp
  have rspRead : rspOf u = rspOf s := effectU.agrees.read (n := 64) (r := 4)
    (by simp [middleEffect, Effect.components, Write.component, Operand.component])
  have out : (Operand.reg 7 : Operand 64).read t =
      (if simple then rspOf s else rspOf s + 120) := by
    exact (show (Operand.reg 7 : Operand 64).read t =
      (if simple then rspOf u else rspOf u + 120) from effectT.writes).trans (by rw [rspRead])
  have zero := middle_zero_bytes effectU (by cases simple <;> decide)
    (default_readable simple stack enough rsp runningU.allocated)
  have memoryT := frameT.external (by simp [Component.Covers])
  refine ⟨fuel+1, t, runU.trans runT, readyT, runningT, effectT.rip,
    (frameT.read (n := 64) (r := 4) (by simp)).trans rspU, out,
    (frameT.read (n := 64) (r := 6) (by simp)).trans inputU,
    (frameT.read (n := 64) (r := 2) (by simp)).trans lengthU, ?_, effectU.agrees.trans frameT⟩
  rw [memoryT]
  exact zero

end Hkdf.Proofs.Common.ExtractCaller.Prepare
