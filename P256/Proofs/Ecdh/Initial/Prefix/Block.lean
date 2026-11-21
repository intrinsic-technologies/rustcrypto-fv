import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial.Prefix.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

private theorem memLoad_memStore_rangeApart (mem : Ram) (a b : BitVec 64)
    (v : BitVec 64) (hap : RangeApart a 8 b 8) :
    memLoad (memStore mem a v) b 64 = memLoad mem b 64 := by
  apply memLoad_congr
  intro j hj
  simp only [memByte,PhysicalMemory.read]
  rw [memStore_getElem?_of_ne]
  intro i hi
  exact hap i hi j hj

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x100011
  peerReadable : ∀ k < 8, MemReadable s (s.regValue .rdx + BitVec.ofNat 64 (8*k)) 8
  oneReadable : ∀ k < 4, MemReadable s (0x202580 + BitVec.ofNat 64 (8*k)) 8
  writable : ∀ c ∈ ([8, 248, 256, 264, 272, 280, 288, 296, 304, 312, 320, 328, 336] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 c) 8
  codeApart : ∀ c ∈ ([8, 248, 256, 264, 272, 280, 288, 296, 304, 312, 320, 328, 336] : List Nat), ∀ offset len : Nat, offset + len ≤ 202 →
    RangeApart (rspOf s + BitVec.ofNat 64 c) 8 (0x100011 + BitVec.ofNat 64 offset) len
  peerApart : ∀ c ∈ ([8, 248, 256, 264, 272, 280, 288, 296, 304, 312, 320, 328, 336] : List Nat), ∀ j < 8,
    RangeApart (rspOf s + BitVec.ofNat 64 c) 8 (s.regValue .rdx + BitVec.ofNat 64 (8*j)) 8
  oneApart : ∀ c ∈ ([8, 248, 256, 264, 272, 280, 288, 296, 304, 312, 320, 328, 336] : List Nat), ∀ j < 4,
    RangeApart (rspOf s + BitVec.ofNat 64 c) 8 (0x202580 + BitVec.ofNat 64 (8*j)) 8

theorem Pre.peer_read_store {s : RamState} (h : Pre s)
    (mem : Ram) (c d : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [8, 248, 256, 264, 272, 280, 288, 296, 304, 312, 320, 328, 336]) (hd : d ∈ [0,8,16,24,32,40,48,56]) :
    memLoad (memStore mem ((Operand.reg 4#5 : Operand 64).read s+c) v)
      ((Operand.reg 2#5 : Operand 64).read s+d) 64 =
        memLoad mem ((Operand.reg 2#5 : Operand 64).read s+d) 64 := by
  have hcn : ∃ n ∈ ([8, 248, 256, 264, 272, 280, 288, 296, 304, 312, 320, 328, 336] : List Nat), c = BitVec.ofNat 64 n := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_,by simp,rfl⟩
  obtain ⟨n,hn,rfl⟩ := hcn
  have hd' : d ∈ List.ofFn (fun j : Fin 8 => BitVec.ofNat 64 (8*j.val)) := hd
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hd'
  exact memLoad_memStore_rangeApart mem _ _ v
    (h.peerApart n hn j.val j.isLt)

theorem Pre.one_read_store {s : RamState} (h : Pre s)
    (mem : Ram) (c a : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [8, 248, 256, 264, 272, 280, 288, 296, 304, 312, 320, 328, 336]) (ha : a ∈ [0x202580,0x202588,0x202590,0x202598]) :
    memLoad (memStore mem ((Operand.reg 4#5 : Operand 64).read s+c) v) a 64 = memLoad mem a 64 := by
  have hcn : ∃ n ∈ ([8, 248, 256, 264, 272, 280, 288, 296, 304, 312, 320, 328, 336] : List Nat), c = BitVec.ofNat 64 n := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_,by simp,rfl⟩
  obtain ⟨n,hn,rfl⟩ := hcn
  have ha' : a ∈ List.ofFn (fun j : Fin 4 => 0x202580+BitVec.ofNat 64 (8*j.val)) := ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha'
  exact memLoad_memStore_rangeApart mem _ _ v
    (h.oneApart n hn j.val j.isLt)

def codeBytes : List UInt8 :=
  [0x48, 0x89, 0x74, 0x24, 0x8, 0x48, 0x89, 0xfb, 0x4c, 0x8d, 0xb4, 0x24, 0x18, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x42, 0x38, 0x48, 0x89, 0x84, 0x24, 0x30, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x42, 0x30, 0x48, 0x89, 0x84, 0x24, 0x28, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x42, 0x20, 0x48, 0x8b, 0x4a, 0x28, 0x48, 0x89, 0x8c, 0x24, 0x20, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x18, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x2, 0x48, 0x8b, 0x4a, 0x8, 0x48, 0x89, 0x84, 0x24, 0xf8, 0x0, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0x0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x42, 0x10, 0x48, 0x89, 0x84, 0x24, 0x8, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x42, 0x18, 0x48, 0x89, 0x84, 0x24, 0x10, 0x1, 0x0, 0x0, 0x4c, 0x8d, 0xa4, 0x24, 0x38, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x5, 0xf1, 0x24, 0x10, 0x0, 0x48, 0x89, 0x84, 0x24, 0x38, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x5, 0xea, 0x24, 0x10, 0x0, 0x48, 0x89, 0x84, 0x24, 0x40, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x5, 0xe3, 0x24, 0x10, 0x0, 0x48, 0x89, 0x84, 0x24, 0x48, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x5, 0xdc, 0x24, 0x10, 0x0, 0x48, 0x89, 0x84, 0x24, 0x50, 0x1, 0x0, 0x0, 0x4c, 0x8d, 0xac, 0x24, 0xf8, 0x3, 0x0, 0x0, 0xb9, 0xc, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xef, 0x48, 0xc7, 0xc6, 0x90, 0x24, 0x20, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x1000db
    writes := [⟨(.reg 0 : Operand 64),memLoad s.external 0x202598 64⟩,
      ⟨(.reg 3 : Operand 64),s.regValue .rdi⟩,
      ⟨(.reg 14 : Operand 64),rspOf s+280⟩,
      ⟨(.reg 12 : Operand 64),rspOf s+312⟩,
      ⟨(.reg 13 : Operand 64),rspOf s+1016⟩,
      ⟨(.reg 1 : Operand 64),12⟩,
      ⟨(.reg 7 : Operand 64),rspOf s+1016⟩,
      ⟨(.reg 6 : Operand 64),0x202490⟩,
      ⟨(.mem (rspOf s+8) : Operand 64),s.regValue .rsi⟩,
      ⟨(.mem (rspOf s+248) : Operand 64),memLoad s.external (s.regValue .rdx+0) 64⟩,
      ⟨(.mem (rspOf s+256) : Operand 64),memLoad s.external (s.regValue .rdx+8) 64⟩,
      ⟨(.mem (rspOf s+264) : Operand 64),memLoad s.external (s.regValue .rdx+16) 64⟩,
      ⟨(.mem (rspOf s+272) : Operand 64),memLoad s.external (s.regValue .rdx+24) 64⟩,
      ⟨(.mem (rspOf s+280) : Operand 64),memLoad s.external (s.regValue .rdx+32) 64⟩,
      ⟨(.mem (rspOf s+288) : Operand 64),memLoad s.external (s.regValue .rdx+40) 64⟩,
      ⟨(.mem (rspOf s+296) : Operand 64),memLoad s.external (s.regValue .rdx+48) 64⟩,
      ⟨(.mem (rspOf s+304) : Operand 64),memLoad s.external (s.regValue .rdx+56) 64⟩,
      ⟨(.mem (rspOf s+312) : Operand 64),memLoad s.external (0x202580) 64⟩,
      ⟨(.mem (rspOf s+320) : Operand 64),memLoad s.external (0x202588) 64⟩,
      ⟨(.mem (rspOf s+328) : Operand 64),memLoad s.external (0x202590) 64⟩,
      ⟨(.mem (rspOf s+336) : Operand 64),memLoad s.external (0x202598) 64⟩] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem correct [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 202, (0x100011 : BitVec 64)+BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x100011 codeBytes) (Effect.post effect) := by
  advance_begin (mov_m64_r64_effect_step 0x100011 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip,hP.writable 8 (by simp),hP.codeApart 8 (by simp) 0 5 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.codeApart 8 (by simp) 0 202 (by decide)
  case next => intro _ _; exact outside 5 (by decide)
  advance_then (mov_r64_r64_effect_step 0x100016 0x48 0xfb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 5 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 8 (by decide)
  advance_then (lea_r64_effect_step 0x100019 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 16 (by decide)
  advance_then (mov_r64_m64_effect_step 0x100021 0x48 (by simp [RexWPrefix]) 0 (.base 2 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 16 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.peerReadable 7 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 20 (by decide)
  advance_then (mov_m64_r64_effect_step 0x100025 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 20 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 304 (by simp)
    · x86_norm
      exact hP.codeApart 304 (by simp) 20 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 304 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 28 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10002d 0x48 (by simp [RexWPrefix]) 0 (.base 2 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 28 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.peerReadable 6 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 32 (by decide)
  advance_then (mov_m64_r64_effect_step 0x100031 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 296 (by simp)
    · x86_norm
      exact hP.codeApart 296 (by simp) 32 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 296 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 40 (by decide)
  advance_then (mov_r64_m64_effect_step 0x100039 0x48 (by simp [RexWPrefix]) 0 (.base 2 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 40 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.peerReadable 4 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 44 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10003d 0x48 (by simp [RexWPrefix]) 1 (.base 2 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 44 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.peerReadable 5 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 48 (by decide)
  advance_then (mov_m64_r64_effect_step 0x100041 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 288 (by simp)
    · x86_norm
      exact hP.codeApart 288 (by simp) 48 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 288 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 56 (by decide)
  advance_then (mov_m64_r64_effect_step 0x100049 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 280 (by simp)
    · x86_norm
      exact hP.codeApart 280 (by simp) 56 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 280 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 64 (by decide)
  advance_then (mov_r64_m64_effect_step 0x100051 0x48 (by simp [RexWPrefix]) 0 (.base 2 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 64 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.peerReadable 0 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 67 (by decide)
  advance_then (mov_r64_m64_effect_step 0x100054 0x48 (by simp [RexWPrefix]) 1 (.base 2 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 67 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.peerReadable 1 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 71 (by decide)
  advance_then (mov_m64_r64_effect_step 0x100058 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 71 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 248 (by simp)
    · x86_norm
      exact hP.codeApart 248 (by simp) 71 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 248 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 79 (by decide)
  advance_then (mov_m64_r64_effect_step 0x100060 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 256)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 79 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 256 (by simp)
    · x86_norm
      exact hP.codeApart 256 (by simp) 79 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 256 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 87 (by decide)
  advance_then (mov_r64_m64_effect_step 0x100068 0x48 (by simp [RexWPrefix]) 0 (.base 2 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 87 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.peerReadable 2 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 91 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10006c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 91 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 264 (by simp)
    · x86_norm
      exact hP.codeApart 264 (by simp) 91 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 264 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 99 (by decide)
  advance_then (mov_r64_m64_effect_step 0x100074 0x48 (by simp [RexWPrefix]) 0 (.base 2 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 99 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.peerReadable 3 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 103 (by decide)
  advance_then (mov_m64_r64_effect_step 0x100078 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 272)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 103 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 272 (by simp)
    · x86_norm
      exact hP.codeApart 272 (by simp) 103 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 272 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 111 (by decide)
  advance_then (lea_r64_effect_step 0x100080 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 111 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 119 (by decide)
  advance_then (mov_r64_m64_effect_step 0x100088 0x48 (by simp [RexWPrefix]) 0 (.rip 0x1024f1) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 119 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.oneReadable 0 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 126 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10008f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 126 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 312 (by simp)
    · x86_norm
      exact hP.codeApart 312 (by simp) 126 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 312 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 134 (by decide)
  advance_then (mov_r64_m64_effect_step 0x100097 0x48 (by simp [RexWPrefix]) 0 (.rip 0x1024ea) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 134 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.oneReadable 1 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 141 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10009e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 141 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 320 (by simp)
    · x86_norm
      exact hP.codeApart 320 (by simp) 141 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 320 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 149 (by decide)
  advance_then (mov_r64_m64_effect_step 0x1000a6 0x48 (by simp [RexWPrefix]) 0 (.rip 0x1024e3) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 149 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.oneReadable 2 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 156 (by decide)
  advance_then (mov_m64_r64_effect_step 0x1000ad 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 156 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 328 (by simp)
    · x86_norm
      exact hP.codeApart 328 (by simp) 156 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 328 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 164 (by decide)
  advance_then (mov_r64_m64_effect_step 0x1000b5 0x48 (by simp [RexWPrefix]) 0 (.rip 0x1024dc) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 164 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.oneReadable 3 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 171 (by decide)
  advance_then (mov_m64_r64_effect_step 0x1000bc 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 171 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 336 (by simp)
    · x86_norm
      exact hP.codeApart 336 (by simp) 171 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 336 (by simp) 0 202 (by decide)
    · x86_norm
      exact outside 179 (by decide)
  advance_then (lea_r64_effect_step 0x1000c4 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 1016)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 179 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 187 (by decide)
  advance_then (mov_r32_imm32_effect_step 0x1000cc 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 187 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 192 (by decide)
  advance_then (mov_r64_r64_effect_step 0x1000d1 0x4c 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 192 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 195 (by decide)
  advance_then (mov_r64_imm32_effect_step 0x1000d4 0x48 0xc6 (by simp [RexWPrefix]) rfl rfl 0x202490)
  case sub => exact codeRange_slice_subset 0x100011 codeBytes 195 7
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      exact outside 202 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect,hP.peer_read_store,hP.one_read_store,
      List.mem_cons,List.not_mem_nil,or_false,BitVec.reduceEq,

      operand_write_reg_external,
      operand_write_mem_external]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Ecdh.Initial.Prefix.Block
