import ChaCha20Poly1305.Spec
import ChaCha20Poly1305.Proofs.Common.Poly1305State
import ChaCha20Poly1305.Proofs.Common.WritableRange
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Execution
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Mov.Generated.MImm32C7.Triple
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.Imm32.Triple
import X86Proofs.Program.Execution
import X86Proofs.Program.Agrees
import X86Proofs.Program.Code
import X86Proofs.Step.ReadyToStep

   
                                      

                                                                                              
                                                                             
                                                                                                 
                                                                                               
                                                                                            
  

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e40

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
  Standards.RFC.ChaCha20Poly1305 ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

def entry : BitVec 64 := 0x101e40

def codeLength : Nat := 0x78

structure Pre (key : Vector UInt8 32) (s : RamState) : Prop where
  rip : s.RIP = entry
  state : WritableRange s (rdi.read s) stateBytes
  keyReadable : MemReadable s (rsi.read s) 32
  keyBytes : ∀ i : Fin 32, s.external[rsi.read s + BitVec.ofNat 64 i.val]? = some key[i]
  stateKey : RangeApart (rdi.read s) stateBytes (rsi.read s) 32
  returnSlot : MemReadable s (stackPtr s) 8
  stateReturn : RangeApart (rdi.read s) stateBytes (stackPtr s) 8
  returnLow : (returnBoundary s).rip.toNat < 2 ^ 32
  returnOutside : (returnBoundary s).rip.toNat < entry.toNat ∨
    entry.toNat + codeLength ≤ (returnBoundary s).rip.toNat

def changes (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
    .flags, .rip, .mem (rdi.read s) stateBytes]

structure Result [Bindings] (key : Vector UInt8 32) (s t : RamState) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = stackPtr s + 8
  result : rax.read t = rdi.read s
  agrees : AgreesExcept (changes s) s t
  pad : wordValue (padWords t (rdi.read s)) = padOf key
  rClamped : ClampedLimbs (rLimbs t (rdi.read s))
  rValue : limbValue (rLimbs t (rdi.read s)) = clampedR key
  hZero : ∀ i, hLimbs t (rdi.read s) i = 0

structure HeadPre (s : RamState) : Prop where
  rip : s.RIP = 0x101e40
  state : MemWritable s (rdi.read s) 56
  apart : RangeApart (rdi.read s) 56 0x101e40 0x78

def headBytes : List UInt8 :=
  [0x48, 0x89, 0xf8,
   0xc7, 0x47, 0x34, 0x00, 0x00, 0x00, 0x00,
   0x48, 0xc7, 0x47, 0x2c, 0x00, 0x00, 0x00, 0x00,
   0x48, 0xc7, 0x47, 0x24, 0x00, 0x00, 0x00, 0x00]

theorem slotW {s : RamState} {a : BitVec 64} (h : MemWritable s a 56) (off n : Nat)
    (hn : off + n ≤ 56) : MemWritable s (a + BitVec.ofNat 64 off) n := by
  have hl := h.low
  have ha : (a + BitVec.ofNat 64 off).toNat = a.toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨by omega, fun i hi => ?_, ?_⟩
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h.mem _ (by omega)
  · rw [ha]; exact h.tables.sub (by omega) (by omega)

theorem slotA {a p : BitVec 64} (h : RangeApart a 56 0x101e40 0x78) (off n : Nat)
    (hn : off + n ≤ 56) (m : Nat) (hp : 0x101e40 ≤ p.toNat) (hm : p.toNat + m ≤ 0x101e40 + 0x78) :
    RangeApart (a + BitVec.ofNat 64 off) n p m := by
  intro i hi j hj he
  obtain ⟨k, hk0⟩ : ∃ k, k = p.toNat - 0x101e40 + j := ⟨_, rfl⟩
  have hk : (0x101e40 : BitVec 64) + BitVec.ofNat 64 k = p + BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq
    have hp64 := p.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow,
      Nat.reduceMod]
    generalize p.toNat = q at *
    omega
  apply h (off + i) (by omega) k (by omega)
  rw [hk, BitVec.ofNat_add, ← BitVec.add_assoc, he]

theorem slotA0 {a p : BitVec 64} (h : RangeApart a 56 0x101e40 0x78) (n : Nat)
    (hn : n ≤ 56) (m : Nat) (hp : 0x101e40 ≤ p.toNat) (hm : p.toNat + m ≤ 0x101e40 + 0x78) :
    RangeApart a n p m := by
  have := slotA h 0 n (by omega) m hp hm
  rwa [show a + BitVec.ofNat 64 0 = a from by simp] at this

theorem slotW0 {s : RamState} {a : BitVec 64} (h : MemWritable s a 56) (n : Nat)
    (hn : n ≤ 56) : MemWritable s a n := by
  have := slotW h 0 n (by omega)
  rwa [show a + BitVec.ofNat 64 0 = a from by simp] at this

macro "e40_store_mid" off:num : tactic => `(tactic| (
  intro s s' hP hH hO
  refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_,
    Effect.Local.avoids (by x86_local) (hO true) ?_⟩
  · x86_norm; exact slotW hP.state $off _ (by decide)
  · x86_norm; exact slotA hP.apart $off _ (by decide) _ (by decide) (by decide)
  · apply Effect.avoids_of_components_mem_rip (by rfl)
    x86_norm; exact slotA hP.apart $off _ (by decide) _ (by decide) (by decide)))

macro "e40_bd" h:ident : tactic => `(tactic| (
  intro _ _; simp only [x86_compose]; exact $h _ (by decide) (by decide)))

def headEffect (s : RamState) : Effect where
  rip := 0x101e5a
  writes := [⟨rax, rdi.read s⟩, ⟨(Operand.mem (rdi.read s + 0x34) : Operand 32), 0⟩,
    ⟨(Operand.mem (rdi.read s + 0x2c) : Operand 64), 0⟩,
    ⟨(Operand.mem (rdi.read s + 0x24) : Operand 64), 0⟩]

theorem head_block [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ pc : BitVec 64, 0x101e40 ≤ pc.toNat → pc.toNat < 0x101eb8 → pc ≠ boundary.rip) :
    AdvancesBlock boundary HeadPre (codeRange 0x101e40 headBytes) headEffect := by
  unfold headBytes
  have h0 : StepEffect (fun s => s.RIP = 0x101e40) (codeRange 0x101e40 [0x48, 0x89, 0xf8])
      (movR64R64Effect 0x101e40 0 7) :=
    mov_r64_r64_effect_step 0x101e40 0x48 0xf8 (by unfold RexWPrefix; decide) (by decide)
  routine_run_begin h0
  case boundary => e40_bd hne
  routine_run_then mov_m32_imm32_effect_step 0x101e43 (.base 7 (.d8 0x34)) (by decide) (by decide) (by decide) 0
  case sub => exact codeRange_mem_of_drop (p := 0x101e40) 3 (by decide +kernel)
  case mid => e40_store_mid 0x34
  case boundary => e40_bd hne
  routine_run_then mov_m64_imm32_effect_step 0x101e4a 0x48 (by unfold RexWPrefix; decide) (.base 7 (.d8 0x2c)) (by decide) (by decide) (by decide) 0
  case sub => exact codeRange_mem_of_drop (p := 0x101e40) 10 (by decide +kernel)
  case mid => e40_store_mid 0x2c
  case boundary => e40_bd hne
  routine_run_then mov_m64_imm32_effect_step 0x101e52 0x48 (by unfold RexWPrefix; decide) (.base 7 (.d8 0x24)) (by decide) (by decide) (by decide) 0
  case sub => exact codeRange_mem_of_drop (p := 0x101e40) 18 (by decide +kernel)
  case mid => e40_store_mid 0x24
  case boundary => e40_bd hne
  routine_run_finish [headEffect]

structure TailPre (s : RamState) : Prop where
  rip : s.RIP = 0x101e5a
  key : MemReadable s (rsi.read s) 32
  state : MemWritable s (rax.read s) 56
  apart : RangeApart (rax.read s) 56 0x101e40 0x78

def tailBytes : List UInt8 :=
  [0xb9, 0xff, 0xff, 0xff, 0x03,
   0x23, 0x0e,
   0x8b, 0x56, 0x03,
   0x8b, 0x7e, 0x06,
   0xc1, 0xea, 0x02,
   0x81, 0xe2, 0x03, 0xff, 0xff, 0x03,
   0xc1, 0xef, 0x04,
   0x81, 0xe7, 0xff, 0xc0, 0xff, 0x03,
   0x44, 0x8b, 0x46, 0x09,
   0x41, 0xc1, 0xe8, 0x06,
   0x41, 0x81, 0xe0, 0xff, 0x3f, 0xf0, 0x03,
   0x44, 0x8b, 0x4e, 0x0c,
   0x41, 0xc1, 0xe9, 0x08,
   0x41, 0x81, 0xe1, 0xff, 0xff, 0x0f, 0x00,
   0x4c, 0x8b, 0x56, 0x10,
   0x48, 0x8b, 0x76, 0x18,
   0x4c, 0x89, 0x10,
   0x48, 0x89, 0x70, 0x08,
   0x89, 0x48, 0x10,
   0x89, 0x50, 0x14,
   0x89, 0x78, 0x18,
   0x44, 0x89, 0x40, 0x1c,
   0x44, 0x89, 0x48, 0x20]

macro "e40_load_mid" off:num : tactic => `(tactic| (
  intro s s' hP hH hO
  refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
    Effect.Local.avoids (by x86_local) (hO true) ?_⟩
  · x86_norm
    first
      | exact memReadable_slice hP.key $off _ (by decide)
      | simpa using memReadable_slice hP.key $off _ (by decide)
  · x86_avoid))

macro "e40_store_mid'" off:num : tactic => `(tactic| (
  intro s s' hP hH hO
  refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_,
    Effect.Local.avoids (by x86_local) (hO true) ?_⟩
  · x86_norm
    first
      | exact slotW hP.state $off _ (by decide)
      | simpa using slotW hP.state $off _ (by decide)
  · x86_norm
    first
      | exact slotA hP.apart $off _ (by decide) _ (by decide) (by decide)
      | simpa using slotA hP.apart $off _ (by decide) _ (by decide) (by decide)
  · apply Effect.avoids_of_components_mem_rip (by rfl)
    x86_norm
    first
      | exact slotA hP.apart $off _ (by decide) _ (by decide) (by decide)
      | simpa using slotA hP.apart $off _ (by decide) _ (by decide) (by decide)))

def unknownFlags : Option StatusFlagsOutcome := some ⟨none, none, none, none, none, none⟩

def mem32 (s : RamState) (a : BitVec 64) : BitVec 32 := (Operand.mem a : Operand 32).read s

def b1Effect (s : RamState) : Effect where
  rip := 0x101e61
  writes := [⟨rcx, ((0x3ffffff : BitVec 32) &&& mem32 s (rsi.read s)).setWidth 64⟩]
  flags := unknownFlags

structure KeyPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  key : MemReadable s (rsi.read s) 32

theorem b1_block [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ pc : BitVec 64, 0x101e40 ≤ pc.toNat → pc.toNat < 0x101eb8 → pc ≠ boundary.rip) :
    AdvancesBlock boundary (KeyPre 0x101e5a) (codeRange 0x101e5a [0xb9, 0xff, 0xff, 0xff, 0x03, 0x23, 0x0e]) b1Effect := by
  have h5 : StepEffect (fun s => s.RIP = 0x101e5a) (codeRange 0x101e5a [0xb9, 0xff, 0xff, 0xff, 0x03])
      (movR32Imm32Effect 0x101e5a 5 1 0x3ffffff) :=
    mov_r32_imm32_effect_step 0x101e5a 0xb9 (by decide) 0x3ffffff
  have h6 : StepEffect _ _ (andR32M32Effect 0x101e5f 2 1 (.base 6 .none)) :=
    and_r32_m32_effect_step 0x101e5f 1 (.base 6 .none) (by decide) (by decide) (by decide)
  routine_run_begin h5
  case boundary => e40_bd hne
  routine_run_then h6
  case sub => exact codeRange_mem_of_drop (p := 0x101e5a) 5 (by decide +kernel)
  case mid => e40_load_mid 0
  case boundary => e40_bd hne
  routine_run_finish [b1Effect, unknownFlags, mem32, BitVec.add_zero]

theorem sw3264 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

def mem64 (s : RamState) (a : BitVec 64) : BitVec 64 := (Operand.mem a : Operand 64).read s

def b2Effect (s : RamState) : Effect where
  rip := 0x101e79
  writes := [⟨(Operand.reg 2 : Operand 64), ((mem32 s (rsi.read s + 3) >>> 2) &&& 0x3ffff03).setWidth 64⟩,
    ⟨rdi, ((mem32 s (rsi.read s + 6) >>> 4) &&& 0x3ffc0ff).setWidth 64⟩]
  flags := unknownFlags

theorem b2_block [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ pc : BitVec 64, 0x101e40 ≤ pc.toNat → pc.toNat < 0x101eb8 → pc ≠ boundary.rip) :
    AdvancesBlock boundary (KeyPre 0x101e61) (codeRange 0x101e61
      [0x8b, 0x56, 0x03, 0x8b, 0x7e, 0x06, 0xc1, 0xea, 0x02, 0x81, 0xe2, 0x03, 0xff, 0xff, 0x03,
       0xc1, 0xef, 0x04, 0x81, 0xe7, 0xff, 0xc0, 0xff, 0x03]) b2Effect := by
  have h1 : StepEffect _ _ (movR32M32LowEffect 0x101e61 2 (.base 6 (.d8 3))) :=
    mov_r32_m32_low_effect_step 0x101e61 2 (.base 6 (.d8 3)) (by decide) (by decide) (by decide)
  have h2 : StepEffect _ _ (movR32M32LowEffect 0x101e64 7 (.base 6 (.d8 6))) :=
    mov_r32_m32_low_effect_step 0x101e64 7 (.base 6 (.d8 6)) (by decide) (by decide) (by decide)
  have h3 : StepEffect _ _ (shrR32Effect 0x101e67 3 2 2) :=
    shr_r32_imm8_effect_step 0x101e67 0xea 0x02 (by decide) (by decide)
  have h4 : StepEffect _ _ (andR32Imm32Effect 0x101e6a 6 2 0x3ffff03) :=
    and_r32_imm32_effect_step 0x101e6a 0xe2 0x3ffff03 (by decide) (by decide)
  have h5 : StepEffect _ _ (shrR32Effect 0x101e70 3 7 4) :=
    shr_r32_imm8_effect_step 0x101e70 0xef 0x04 (by decide) (by decide)
  have h6 : StepEffect _ _ (andR32Imm32Effect 0x101e73 6 7 0x3ffc0ff) :=
    and_r32_imm32_effect_step 0x101e73 0xe7 0x3ffc0ff (by decide) (by decide)
  routine_run_begin h1
  case pre =>
    intro s hP
    refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip (by x86_addr_obs) ?_
    x86_norm; exact memReadable_slice hP.key 3 _ (by decide)
  case boundary => e40_bd hne
  routine_run_then h2
  case sub => exact codeRange_mem_of_drop (p := 0x101e61) 3 (by decide +kernel)
  case mid => e40_load_mid 6
  case boundary => e40_bd hne
  routine_run_then h3
  case sub => exact codeRange_mem_of_drop (p := 0x101e61) 6 (by decide +kernel)
  case boundary => e40_bd hne
  routine_run_then h4
  case sub => exact codeRange_mem_of_drop (p := 0x101e61) 9 (by decide +kernel)
  case boundary => e40_bd hne
  routine_run_then h5
  case sub => exact codeRange_mem_of_drop (p := 0x101e61) 15 (by decide +kernel)
  case boundary => e40_bd hne
  routine_run_then h6
  case sub => exact codeRange_mem_of_drop (p := 0x101e61) 18 (by decide +kernel)
  case boundary => e40_bd hne
  routine_run_finish [b2Effect, unknownFlags, mem32, BitVec.add_zero, sw3264]

def b3Effect (s : RamState) : Effect where
  rip := 0x101e88
  writes := [⟨(Operand.reg 8 : Operand 64), ((mem32 s (rsi.read s + 9) >>> 6) &&& 0x3f03fff).setWidth 64⟩]
  flags := unknownFlags

theorem b3_block [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ pc : BitVec 64, 0x101e40 ≤ pc.toNat → pc.toNat < 0x101eb8 → pc ≠ boundary.rip) :
    AdvancesBlock boundary (KeyPre 0x101e79) (codeRange 0x101e79
      [0x44, 0x8b, 0x46, 0x09, 0x41, 0xc1, 0xe8, 0x06, 0x41, 0x81, 0xe0, 0xff, 0x3f, 0xf0, 0x03]) b3Effect := by
  have h1 : StepEffect _ _ (movR32M32Effect 0x101e79 8 (.base 6 (.d8 9))) :=
    mov_r32_m32_effect_step 0x101e79 0x44 (by unfold RexNoWPrefix; decide) 0 (.base 6 (.d8 9)) (by decide) (by decide) (by decide)
  have h2 : StepEffect _ _ (shrR32Effect (0x101e79 + 4) 4 8 6) :=
    shr_r32_imm8_rex_effect_step (0x101e79 + 4) 0x41 0xe8 6 (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  have h3 : StepEffect _ _ (andR32Imm32Effect (0x101e79 + 8) 7 8 0x3f03fff) :=
    and_r32_imm32_rex_effect_step (0x101e79 + 8) 0x41 0xe0 0x3f03fff (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  routine_run_begin h1
  case pre =>
    intro s hP
    refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip (by x86_addr_obs) ?_
    x86_norm; exact memReadable_slice hP.key 9 _ (by decide)
  case boundary => e40_bd hne
  routine_run_then h2
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e79) 4 (by decide +kernel))
  case boundary => e40_bd hne
  routine_run_then h3
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e79) 8 (by decide +kernel))
  case boundary => e40_bd hne
  routine_run_finish [b3Effect, unknownFlags, mem32, BitVec.add_zero, sw3264]

def b4Effect (s : RamState) : Effect where
  rip := 0x101e97
  writes := [⟨(Operand.reg 9 : Operand 64), ((mem32 s (rsi.read s + 12) >>> 8) &&& 0xfffff).setWidth 64⟩]
  flags := unknownFlags

theorem b4_block [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ pc : BitVec 64, 0x101e40 ≤ pc.toNat → pc.toNat < 0x101eb8 → pc ≠ boundary.rip) :
    AdvancesBlock boundary (KeyPre 0x101e88) (codeRange 0x101e88
      [0x44, 0x8b, 0x4e, 0x0c, 0x41, 0xc1, 0xe9, 0x08, 0x41, 0x81, 0xe1, 0xff, 0xff, 0x0f, 0x00]) b4Effect := by
  have h1 : StepEffect _ _ (movR32M32Effect 0x101e88 9 (.base 6 (.d8 12))) :=
    mov_r32_m32_effect_step 0x101e88 0x44 (by unfold RexNoWPrefix; decide) 1 (.base 6 (.d8 12)) (by decide) (by decide) (by decide)
  have h2 : StepEffect _ _ (shrR32Effect (0x101e88 + 4) 4 9 8) :=
    shr_r32_imm8_rex_effect_step (0x101e88 + 4) 0x41 0xe9 8 (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  have h3 : StepEffect _ _ (andR32Imm32Effect (0x101e88 + 8) 7 9 0xfffff) :=
    and_r32_imm32_rex_effect_step (0x101e88 + 8) 0x41 0xe1 0xfffff (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  routine_run_begin h1
  case pre =>
    intro s hP
    refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip (by x86_addr_obs) ?_
    x86_norm; exact memReadable_slice hP.key 12 _ (by decide)
  case boundary => e40_bd hne
  routine_run_then h2
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e88) 4 (by decide +kernel))
  case boundary => e40_bd hne
  routine_run_then h3
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e88) 8 (by decide +kernel))
  case boundary => e40_bd hne
  routine_run_finish [b4Effect, unknownFlags, mem32, BitVec.add_zero, sw3264]

def b5Effect (s : RamState) : Effect where
  rip := 0x101e9f
  writes := [⟨(Operand.reg 10 : Operand 64), mem64 s (rsi.read s + 16)⟩,
    ⟨(Operand.reg 6 : Operand 64), mem64 s (rsi.read s + 24)⟩]

theorem b5_block [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ pc : BitVec 64, 0x101e40 ≤ pc.toNat → pc.toNat < 0x101eb8 → pc ≠ boundary.rip) :
    AdvancesBlock boundary (KeyPre 0x101e97) (codeRange 0x101e97
      [0x4c, 0x8b, 0x56, 0x10, 0x48, 0x8b, 0x76, 0x18]) b5Effect := by
  have h1 : StepEffect _ _ (movR64M64Effect 0x101e97 10 (.base 6 (.d8 16))) :=
    mov_r64_m64_effect_step 0x101e97 0x4c (by unfold RexWPrefix; decide) 2 (.base 6 (.d8 16)) (by decide) (by decide) (by decide)
  have h2 : StepEffect _ _ (movR64M64Effect 0x101e9b 6 (.base 6 (.d8 24))) :=
    mov_r64_m64_effect_step 0x101e9b 0x48 (by unfold RexWPrefix; decide) 6 (.base 6 (.d8 24)) (by decide) (by decide) (by decide)
  routine_run_begin h1
  case pre =>
    intro s hP
    refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip (by x86_addr_obs) ?_
    x86_norm; exact memReadable_slice hP.key 16 _ (by decide)
  case boundary => e40_bd hne
  routine_run_then h2
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e97) 4 (by decide +kernel))
  case mid => e40_load_mid 24
  case boundary => e40_bd hne
  routine_run_finish [b5Effect, mem64, BitVec.add_zero]

structure StoreCPre (s : RamState) : Prop where
  rip : s.RIP = 0x101e9f
  state : MemWritable s (rax.read s) 56
  apart : RangeApart (rax.read s) 56 0x101e40 0x78

def cEffect (s : RamState) : Effect where
  rip := 0x101eb7
  writes := [⟨(Operand.mem (rax.read s) : Operand 64), (Operand.reg 10 : Operand 64).read s⟩,
    ⟨(Operand.mem (rax.read s + 8) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
    ⟨(Operand.mem (rax.read s + 16) : Operand 32), (Operand.reg 1 : Operand 32).read s⟩,
    ⟨(Operand.mem (rax.read s + 20) : Operand 32), (Operand.reg 2 : Operand 32).read s⟩,
    ⟨(Operand.mem (rax.read s + 24) : Operand 32), (Operand.reg 7 : Operand 32).read s⟩,
    ⟨(Operand.mem (rax.read s + 28) : Operand 32), (Operand.reg 8 : Operand 32).read s⟩,
    ⟨(Operand.mem (rax.read s + 32) : Operand 32), (Operand.reg 9 : Operand 32).read s⟩]

set_option maxHeartbeats 2000000 in
theorem c_block [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ pc : BitVec 64, 0x101e40 ≤ pc.toNat → pc.toNat < 0x101eb8 → pc ≠ boundary.rip) :
    AdvancesBlock boundary StoreCPre (codeRange 0x101e9f
      [0x4c, 0x89, 0x10, 0x48, 0x89, 0x70, 0x08, 0x89, 0x48, 0x10, 0x89, 0x50, 0x14,
       0x89, 0x78, 0x18, 0x44, 0x89, 0x40, 0x1c, 0x44, 0x89, 0x48, 0x20]) cEffect := by
  have h1 : StepEffect _ _ (movM64R64Effect 0x101e9f 10 (.base 0 .none)) :=
    mov_m64_r64_effect_step 0x101e9f 0x4c (by unfold RexWPrefix; decide) 2 (.base 0 .none) (by decide) (by decide) (by decide)
  have h2 : StepEffect _ _ (movM64R64Effect 0x101ea2 6 (.base 0 (.d8 8))) :=
    mov_m64_r64_effect_step 0x101ea2 0x48 (by unfold RexWPrefix; decide) 6 (.base 0 (.d8 8)) (by decide) (by decide) (by decide)
  have h3 : StepEffect _ _ (movM32R32LowEffect 0x101ea6 1 (.base 0 (.d8 16))) :=
    mov_m32_r32_low_effect_step 0x101ea6 1 (.base 0 (.d8 16)) (by decide) (by decide) (by decide)
  have h4 : StepEffect _ _ (movM32R32LowEffect 0x101ea9 2 (.base 0 (.d8 20))) :=
    mov_m32_r32_low_effect_step 0x101ea9 2 (.base 0 (.d8 20)) (by decide) (by decide) (by decide)
  have h5 : StepEffect _ _ (movM32R32LowEffect 0x101eac 7 (.base 0 (.d8 24))) :=
    mov_m32_r32_low_effect_step 0x101eac 7 (.base 0 (.d8 24)) (by decide) (by decide) (by decide)
  have h6 : StepEffect _ _ (movM32R32Effect 0x101eaf 8 (.base 0 (.d8 28))) :=
    mov_m32_r32_effect_step 0x101eaf 0x44 (by unfold RexNoWPrefix; decide) 0 (.base 0 (.d8 28)) (by decide) (by decide) (by decide)
  have h7 : StepEffect _ _ (movM32R32Effect 0x101eb3 9 (.base 0 (.d8 32))) :=
    mov_m32_r32_effect_step 0x101eb3 0x44 (by unfold RexNoWPrefix; decide) 1 (.base 0 (.d8 32)) (by decide) (by decide) (by decide)
  routine_run_begin h1
  case pre =>
    intro s hP
    refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip (by x86_addr_obs) ?_ ?_
    · x86_norm; simpa using slotW hP.state 0 _ (by decide)
    · x86_norm; simpa using slotA hP.apart 0 _ (by decide) _ (by decide) (by decide)
  case av =>
    intro s hP
    apply Effect.avoids_of_components_mem_rip (by rfl)
    x86_norm; simpa using slotA hP.apart 0 _ (by decide) _ (by decide) (by decide)
  case boundary => e40_bd hne
  routine_run_then h2
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e9f) 3 (by decide +kernel))
  case mid => e40_store_mid' 8
  case boundary => e40_bd hne
  routine_run_then h3
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e9f) 7 (by decide +kernel))
  case mid => e40_store_mid' 16
  case boundary => e40_bd hne
  routine_run_then h4
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e9f) 10 (by decide +kernel))
  case mid => e40_store_mid' 20
  case boundary => e40_bd hne
  routine_run_then h5
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e9f) 13 (by decide +kernel))
  case mid => e40_store_mid' 24
  case boundary => e40_bd hne
  routine_run_then h6
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e9f) 16 (by decide +kernel))
  case mid => e40_store_mid' 28
  case boundary => e40_bd hne
  routine_run_then h7
  try (case sub => exact codeRange_mem_of_drop (p := 0x101e9f) 20 (by decide +kernel))
  case mid => e40_store_mid' 32
  case boundary => e40_bd hne
  routine_run_finish [cEffect, BitVec.add_zero]

theorem blockStart [Bindings] {boundary : ReturnBoundary} {P pre : RamState → Prop}
    {code code₁ : CodeMap} {e : RamState → Effect}
    (h : AdvancesBlock boundary pre code₁ e) (hSub : ∀ x ∈ code₁, x ∈ code)
    (hPre : ∀ s, P s → pre s) (hAvoid : ∀ s, P s → (e s).Avoids code) :
    AdvancesBlock boundary P code e := by
  intro s hReady hCode hP
  obtain ⟨fuel, t, hAdvance, hReady', _, hEffect⟩ := h s hReady (hCode.mono hSub) (hPre s hP)
  exact ⟨fuel, t, hAdvance, hReady', hEffect.codeIn (hAvoid s hP) hCode, hEffect⟩

def limb0 (s : RamState) : BitVec 32 := 0x3ffffff &&& mem32 s (rsi.read s)
def limb1 (s : RamState) : BitVec 32 := (mem32 s (rsi.read s + 3) >>> 2) &&& 0x3ffff03
def limb2 (s : RamState) : BitVec 32 := (mem32 s (rsi.read s + 6) >>> 4) &&& 0x3ffc0ff
def limb3 (s : RamState) : BitVec 32 := (mem32 s (rsi.read s + 9) >>> 6) &&& 0x3f03fff
def limb4 (s : RamState) : BitVec 32 := (mem32 s (rsi.read s + 12) >>> 8) &&& 0xfffff

def tailEffect (s : RamState) : Effect where
  rip := 0x101eb7
  writes := [⟨rcx, (limb0 s).setWidth 64⟩,
    ⟨(Operand.reg 2 : Operand 64), (limb1 s).setWidth 64⟩,
    ⟨rdi, (limb2 s).setWidth 64⟩,
    ⟨(Operand.reg 8 : Operand 64), (limb3 s).setWidth 64⟩,
    ⟨(Operand.reg 9 : Operand 64), (limb4 s).setWidth 64⟩,
    ⟨(Operand.reg 10 : Operand 64), mem64 s (rsi.read s + 16)⟩,
    ⟨(Operand.reg 6 : Operand 64), mem64 s (rsi.read s + 24)⟩,
    ⟨(Operand.mem (rax.read s) : Operand 64), mem64 s (rsi.read s + 16)⟩,
    ⟨(Operand.mem (rax.read s + 8) : Operand 64), mem64 s (rsi.read s + 24)⟩,
    ⟨(Operand.mem (rax.read s + 16) : Operand 32), limb0 s⟩,
    ⟨(Operand.mem (rax.read s + 20) : Operand 32), limb1 s⟩,
    ⟨(Operand.mem (rax.read s + 24) : Operand 32), limb2 s⟩,
    ⟨(Operand.mem (rax.read s + 28) : Operand 32), limb3 s⟩,
    ⟨(Operand.mem (rax.read s + 32) : Operand 32), limb4 s⟩]
  flags := unknownFlags

theorem b2Effect_local : Effect.Local b2Effect := by effect_local [b2Effect, unknownFlags, mem32]
theorem b3Effect_local : Effect.Local b3Effect := by effect_local [b3Effect, unknownFlags, mem32]
theorem b4Effect_local : Effect.Local b4Effect := by effect_local [b4Effect, unknownFlags, mem32]
theorem b5Effect_local : Effect.Local b5Effect := by effect_local [b5Effect, mem64]
theorem cEffect_local : Effect.Local cEffect := by effect_local [cEffect]

macro "e40_full" : tactic => `(tactic| (
  intro _ _
  simp (config := { decide := true }) only [x86_compose, b1Effect, b2Effect, b3Effect, b4Effect,
    b5Effect, cEffect, unknownFlags, mem32, mem64, List.forall_mem_cons,
    List.forall_mem_nil, List.forall_mem_append, and_true, true_and]))

macro "e40_key_mid" : tactic => `(tactic| (
  intro s t hP hH hO
  refine ⟨⟨hH.rip_of (by x86_norm [b1Effect, b2Effect, b3Effect, b4Effect, unknownFlags]), ?_⟩, ?_⟩
  · refine MemReadable.carry hH (hO true) (addr := fun s => rsi.read s) (by x86_addr_obs) ?_
    x86_norm [b1Effect, b2Effect, b3Effect, b4Effect, unknownFlags]
    exact hP.key
  · apply Effect.Avoids.of_noMem
    simp [b2Effect, b3Effect, b4Effect, b5Effect, unknownFlags, Effect.components,
      Component.Covers]))

set_option maxHeartbeats 2000000 in
theorem tail_block [Bindings] (boundary : ReturnBoundary)
    (hne : ∀ pc : BitVec 64, 0x101e40 ≤ pc.toNat → pc.toNat < 0x101eb8 → pc ≠ boundary.rip) :
    AdvancesBlock boundary TailPre (codeRange 0x101e5a tailBytes) tailEffect := by
  have k1 := blockStart (b1_block boundary hne) (P := TailPre) (code := codeRange 0x101e5a tailBytes)
    (codeRange_mem_of_take (by decide +kernel)) (fun s h => ⟨h.rip, h.key⟩)
    (fun s _ => Effect.Avoids.of_noMem (by
      simp [b1Effect, unknownFlags, Effect.components, Component.Covers]) _)
  have k2 := AdvancesBlock.seq_block k1 (b2_block boundary hne) b2Effect_local
    (codeRange_mem_of_drop (p := 0x101e5a) 7 (by decide +kernel)) (by e40_full) (by e40_key_mid)
  have k3 := AdvancesBlock.seq_block k2 (b3_block boundary hne) b3Effect_local
    (codeRange_mem_of_drop (p := 0x101e5a) 31 (by decide +kernel)) (by e40_full) (by e40_key_mid)
  have k4 := AdvancesBlock.seq_block k3 (b4_block boundary hne) b4Effect_local
    (codeRange_mem_of_drop (p := 0x101e5a) 46 (by decide +kernel)) (by e40_full) (by e40_key_mid)
  have k5 := AdvancesBlock.seq_block k4 (b5_block boundary hne) b5Effect_local
    (codeRange_mem_of_drop (p := 0x101e5a) 61 (by decide +kernel)) (by e40_full) (by e40_key_mid)
  have hlen : tailBytes.length = 93 := by decide
  have k6 := AdvancesBlock.seq_block k5 (c_block boundary hne) cEffect_local
    (codeRange_mem_of_drop (p := 0x101e5a) 69 (by decide +kernel)) (by e40_full) (by
      intro s t hP hH hO
      have hr : rax.read t = rax.read s := by
        have := (hO true).read (Operand.reg 0 : Operand 64) trivial
        x86_norm [b1Effect, b2Effect, b3Effect, b4Effect, b5Effect, unknownFlags, mem32,
          mem64] at this
        exact this.symm
      refine ⟨⟨hH.rip_of (by x86_norm [b1Effect, b2Effect, b3Effect, b4Effect, b5Effect,
        unknownFlags]), ?_, ?_⟩, ?_⟩
      · refine MemWritable.carry hH (hO true) (addr := fun s => rax.read s) (by x86_addr_obs) ?_
        x86_norm [b1Effect, b2Effect, b3Effect, b4Effect, b5Effect, unknownFlags, mem32, mem64]
        exact hP.state
      · rw [hr]; exact hP.apart
      · apply Effect.avoids_codeRange
        intro c hc a len he
        rw [hlen]
        simp only [cEffect, Effect.components, List.map, Write.component_mem, List.mem_append,
          List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;> cases he <;> rw [hr]
        · exact slotA0 hP.apart 8 (by decide) 93 (by decide) (by decide)
        · exact slotA hP.apart 8 8 (by decide) 93 (by decide) (by decide)
        · exact slotA hP.apart 16 4 (by decide) 93 (by decide) (by decide)
        · exact slotA hP.apart 20 4 (by decide) 93 (by decide) (by decide)
        · exact slotA hP.apart 24 4 (by decide) 93 (by decide) (by decide)
        · exact slotA hP.apart 28 4 (by decide) 93 (by decide) (by decide)
        · exact slotA hP.apart 32 4 (by decide) 93 (by decide) (by decide))
  refine AdvancesBlock.block_end ?_ k6
  intro s t _ hH
  apply hH.weaken
  · x86_norm [tailEffect, b1Effect, b2Effect, b3Effect, b4Effect, b5Effect, cEffect,
      unknownFlags, mem32, mem64, limb0, limb1, limb2, limb3, limb4, sw3264]
  · x86_norm [tailEffect, b1Effect, b2Effect, b3Effect, b4Effect, b5Effect, cEffect,
      unknownFlags, mem32, mem64, limb0, limb1, limb2, limb3, limb4, sw3264]
  · intro i; cases i <;> x86_norm [tailEffect, b1Effect, b2Effect, b3Effect, b4Effect,
      b5Effect, cEffect, unknownFlags, mem32, mem64, limb0, limb1, limb2, limb3, limb4, sw3264]
  · x86_norm [tailEffect, b1Effect, b2Effect, b3Effect, b4Effect, b5Effect, cEffect,
      unknownFlags, mem32, mem64, limb0, limb1, limb2, limb3, limb4, sw3264]

theorem memWritable_of_writableRange {s : RamState} {a : BitVec 64} {n : Nat}
    (h : WritableRange s a n) (hn : 0 < n) : MemWritable s a n :=
  ⟨h.readable.low, h.readable.mem, PageTableEntriesApart.of_bytes hn h.readable.low
    (fun i hi => by
      have := h.tables i hi
      rw [inPageTables_iff] at this
      unfold PageTableEntriesApart
      omega)⟩

theorem code_inProgram (j : Nat) (hj : j < 0x78) :
    InProgram (0x101e40 + BitVec.ofNat 64 j) := by
  have hs : 0x1e40 + 0x78 ≤ Extracted.textBytes.size := by decide +kernel
  have := text_address_in_program (0x1e40 + j) (by omega)
  rwa [BitVec.ofNat_add, ← BitVec.add_assoc] at this

theorem state_apart {s : RamState} {a : BitVec 64} (h : WritableRange s a 56) :
    RangeApart a 56 0x101e40 0x78 :=
  fun i hi j hj he => h.code i hi (he ▸ code_inProgram j hj)

theorem codeIn_of_agrees {cs : List Component} {s t : RamState} {a : BitVec 64}
    (h : AgreesExcept cs s t) (hw : ∀ i < 56, ¬ InProgram (a + BitVec.ofNat 64 i))
    (hcs : ∀ c ∈ cs, ∀ x, c.Covers x → ∃ i < 56, x = a + BitVec.ofNat 64 i)
    (hc : CodeIn Extracted.programImage s) : CodeIn Extracted.programImage t :=
  CodeIn.of_agreesExcept h (fun x hx c hc' hcov => by
    obtain ⟨i, hi, he⟩ := hcs c hc' _ hcov
    exact hw i hi (he ▸ inProgram_of_mem hx)) hc

theorem covers_slot {a x : BitVec 64} {off n B : Nat} (h : off + n ≤ B)
    (hx : (Component.mem (a + BitVec.ofNat 64 off) n).Covers x) :
    ∃ i < B, x = a + BitVec.ofNat 64 i := by
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨off + i, by omega, add_ofNat_add_ofNat _ _ _⟩

theorem covers_slot0 {a x : BitVec 64} {n B : Nat} (h : n ≤ B)
    (hx : (Component.mem a n).Covers x) : ∃ i < B, x = a + BitVec.ofNat 64 i := by
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, by omega, rfl⟩

theorem head_covers (s : RamState) : ∀ c ∈ (headEffect s).components, ∀ x, c.Covers x →
    ∃ i < 56, x = rdi.read s + BitVec.ofNat 64 i := by
  intro c hc x hx
  simp only [headEffect, Effect.components, List.map, Write.component_mem, Write.component_reg,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact hx.elim
  · exact covers_slot (off := 52) (n := 4) (by decide) hx
  · exact covers_slot (off := 44) (n := 8) (by decide) hx
  · exact covers_slot (off := 36) (n := 8) (by decide) hx
  · exact hx.elim

theorem tail_covers (s : RamState) : ∀ c ∈ (tailEffect s).components, ∀ x, c.Covers x →
    ∃ i < 36, x = rax.read s + BitVec.ofNat 64 i := by
  intro c hc x hx
  simp only [tailEffect, unknownFlags, Effect.components, List.map, Write.component_mem,
    Write.component_reg, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals first
    | exact hx.elim
    | exact covers_slot0 (n := 8) (by decide) hx
    | exact covers_slot (off := 8) (n := 8) (by decide) hx
    | exact covers_slot (off := 16) (n := 4) (by decide) hx
    | exact covers_slot (off := 20) (n := 4) (by decide) hx
    | exact covers_slot (off := 24) (n := 4) (by decide) hx
    | exact covers_slot (off := 28) (n := 4) (by decide) hx
    | exact covers_slot (off := 32) (n := 4) (by decide) hx

def leNat (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => f 0 + 256 * leNat (fun j => f (j + 1)) k

theorem leNat_lt {f : Nat → Nat} (hf : ∀ j, f j < 256) (k : Nat) : leNat f k < 256 ^ k := by
  induction k generalizing f with
  | zero => simp [leNat]
  | succ k ih =>
    have := ih (f := fun j => f (j + 1)) (fun j => hf _)
    have := hf 0
    simp only [leNat, Nat.pow_succ]
    omega

theorem leNat_split (f : Nat → Nat) (a b : Nat) :
    leNat f (a + b) = leNat f a + 256 ^ a * leNat (fun j => f (a + j)) b := by
  induction a generalizing f with
  | zero => simp [leNat]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [leNat]
    rw [ih (fun j => f (j + 1))]
    simp only [Nat.pow_succ, show ∀ j, a + j + 1 = a + 1 + j from fun j => by omega]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ a)]
    omega

theorem pow256_pos (a : Nat) : 0 < 256 ^ a := Nat.pow_pos (by decide)

theorem leNat_div {f : Nat → Nat} (hf : ∀ j, f j < 256) (a b : Nat) :
    leNat f (a + b) / 256 ^ a % 256 ^ b = leNat (fun j => f (a + j)) b := by
  rw [leNat_split, Nat.add_mul_div_left _ _ (pow256_pos a),
    Nat.div_eq_of_lt (leNat_lt hf a), Nat.zero_add,
    Nat.mod_eq_of_lt (leNat_lt (fun j => hf _) b)]

theorem leNat_byte {f : Nat → Nat} (hf : ∀ j, f j < 256) {i k : Nat} (hi : i < k) :
    leNat f k / 256 ^ i % 256 = f i := by
  obtain ⟨b, rfl⟩ : ∃ b, k = i + (b + 1) := ⟨k - i - 1, by omega⟩
  have h := leNat_div hf i (b + 1)
  rw [← Nat.mod_mod_of_dvd _ (⟨256 ^ b, by rw [Nat.pow_succ, Nat.mul_comm]⟩ :
    256 ∣ 256 ^ (b + 1)), h]
  simp only [leNat, Nat.add_zero]
  have := hf i
  omega

theorem leNat_congr {f g : Nat → Nat} {k : Nat} (h : ∀ j < k, f j = g j) :
    leNat f k = leNat g k := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
    simp only [leNat]
    rw [h 0 (by omega), ih (fun j hj => h (j + 1) (by omega))]

theorem limb0_bits (N : Nat) : (N % 2 ^ 32) &&& 0x3ffffff = clamp N / 2 ^ 0 % 2 ^ 26 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, clamp]
  by_cases hi : i < 26
  · match i, hi with
    | 0, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 1, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 2, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 3, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 4, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 5, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 6, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 7, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 8, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 9, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 10, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 11, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 12, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 13, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 14, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 15, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 16, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 17, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 18, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 19, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 20, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 21, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 22, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 23, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 24, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 25, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | n + 26, h => exact absurd h (by omega)
  · have h1 : Nat.testBit 0x3ffffff i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (by decide : 0x3ffffff < 2 ^ 26) (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, hi]

theorem limb1_bits (N : Nat) : ((N / 2 ^ 24 % 2 ^ 32) >>> 2) &&& 0x3ffff03 = clamp N / 2 ^ 26 % 2 ^ 26 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, clamp]
  by_cases hi : i < 26
  · match i, hi with
    | 0, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 1, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 2, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 3, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 4, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 5, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 6, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 7, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 8, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 9, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 10, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 11, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 12, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 13, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 14, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 15, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 16, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 17, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 18, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 19, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 20, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 21, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 22, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 23, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 24, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 25, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | n + 26, h => exact absurd h (by omega)
  · have h1 : Nat.testBit 0x3ffff03 i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (by decide : 0x3ffff03 < 2 ^ 26) (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, hi]

theorem limb2_bits (N : Nat) : ((N / 2 ^ 48 % 2 ^ 32) >>> 4) &&& 0x3ffc0ff = clamp N / 2 ^ 52 % 2 ^ 26 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, clamp]
  by_cases hi : i < 26
  · match i, hi with
    | 0, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 1, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 2, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 3, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 4, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 5, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 6, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 7, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 8, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 9, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 10, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 11, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 12, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 13, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 14, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 15, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 16, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 17, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 18, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 19, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 20, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 21, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 22, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 23, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 24, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 25, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | n + 26, h => exact absurd h (by omega)
  · have h1 : Nat.testBit 0x3ffc0ff i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (by decide : 0x3ffc0ff < 2 ^ 26) (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, hi]

theorem limb3_bits (N : Nat) : ((N / 2 ^ 72 % 2 ^ 32) >>> 6) &&& 0x3f03fff = clamp N / 2 ^ 78 % 2 ^ 26 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, clamp]
  by_cases hi : i < 26
  · match i, hi with
    | 0, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 1, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 2, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 3, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 4, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 5, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 6, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 7, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 8, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 9, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 10, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 11, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 12, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 13, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 14, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 15, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 16, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 17, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 18, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 19, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 20, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 21, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 22, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 23, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 24, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 25, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | n + 26, h => exact absurd h (by omega)
  · have h1 : Nat.testBit 0x3f03fff i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (by decide : 0x3f03fff < 2 ^ 26) (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, hi]

theorem limb4_bits (N : Nat) : ((N / 2 ^ 96 % 2 ^ 32) >>> 8) &&& 0xfffff = clamp N / 2 ^ 104 % 2 ^ 26 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, clamp]
  by_cases hi : i < 26
  · match i, hi with
    | 0, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 1, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 2, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 3, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 4, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 5, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 6, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 7, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 8, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 9, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 10, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 11, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 12, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 13, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 14, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 15, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 16, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 17, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 18, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 19, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 20, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 21, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 22, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 23, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 24, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | 25, _ => simp (config := { decide := true }) [Nat.testBit, Nat.shiftRight_eq_div_pow]
    | n + 26, h => exact absurd h (by omega)
  · have h1 : Nat.testBit 0xfffff i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (by decide : 0xfffff < 2 ^ 26) (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, hi]

theorem foldr_leNat (l : List UInt8) :
    l.foldr (fun byte number => byte.toNat + 256 * number) 0 =
      leNat (fun j => (l.getD j 0).toNat) l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [leNat, ih]

theorem leBytesToNum_extract (key : Vector UInt8 32) (a n : Nat) (h : a + n ≤ 32) :
    leBytesToNum ⟨key.toArray.extract a (a + n)⟩ =
      leNat (fun j => if hj : a + j < 32 then key[a + j].toNat else 0) n := by
  unfold leBytesToNum
  rw [← Array.foldr_toList, foldr_leNat]
  have hlen : (key.toArray.extract a (a + n)).toList.length = n := by simp; omega
  rw [hlen]
  apply leNat_congr
  intro j hj
  simp [hj, show a + j < 32 by omega]

def kb (key : Vector UInt8 32) (j : Nat) : Nat := if h : j < 32 then key[j].toNat else 0

theorem kb_lt (key : Vector UInt8 32) (j : Nat) : kb key j < 256 := by
  unfold kb
  split
  · exact UInt8.toNat_lt _
  · decide

def rNum (key : Vector UInt8 32) : Nat := leNat (kb key) 16

theorem rNum_eq (key : Vector UInt8 32) : rNum key = leBytesToNum ⟨key.toArray.extract 0 16⟩ := by
  rw [show (16 : Nat) = 0 + 16 from rfl, leBytesToNum_extract key 0 16 (by decide)]
  apply leNat_congr
  intro j _
  simp [kb]

theorem padOf_eq (key : Vector UInt8 32) : padOf key = leNat (fun j => kb key (16 + j)) 16 :=
  leBytesToNum_extract key 16 16 (by decide)

theorem leNat_window {f : Nat → Nat} (hf : ∀ j, f j < 256) (a b c : Nat) :
    leNat f (a + (b + c)) / 256 ^ a % 256 ^ b = leNat (fun j => f (a + j)) b := by
  rw [leNat_split f a (b + c), Nat.add_mul_div_left _ _ (pow256_pos a),
    Nat.div_eq_of_lt (leNat_lt hf a), Nat.zero_add, leNat_split _ b c,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (leNat_lt (fun j => hf _) b)]

theorem memByte_of_get {m : Ram} {a : BitVec 64} {b : UInt8} (h : m[a]? = some b) :
    memByte m a = b := by
  simp [memByte, PhysicalMemory.read, h]

theorem memByte_of_agrees {cs : List Component} {s t : RamState} (h : AgreesExcept cs s t)
    {x : BitVec 64} (hx : ∀ c ∈ cs, ¬ c.Covers x) : memByte t.external x = memByte s.external x := by
  simp [memByte, PhysicalMemory.read, h.byte hx]

theorem memLoad_of_bytes {m : Ram} {a : BitVec 64} {f : Nat → Nat} {k : Nat}
    (hf : ∀ j, f j < 256)
    (hb : ∀ i < k, memByte m (a + BitVec.ofNat 64 i) = UInt8.ofNat (f i)) :
    memLoad m a (8 * k) = BitVec.ofNat (8 * k) (leNat f k) := by
  apply memLoad_eq_of_memByte (by omega)
  intro i hi
  rw [show 8 * k / 8 = k by omega] at hi
  rw [hb i hi]
  have hlt : leNat f k < 2 ^ (8 * k) := by
    have := leNat_lt hf k
    rwa [Nat.pow_mul]
  apply UInt8.toNat_inj.mp
  simp only [storedByte, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow, Nat.pow_mul,
    show (2 : Nat) ^ 8 = 256 by decide]
  have h1 := leNat_byte hf hi
  simp [h1, hf i]

theorem key_word {m : Ram} {r : BitVec 64} {key : Vector UInt8 32}
    (hk : ∀ i < 32, memByte m (r + BitVec.ofNat 64 i) = UInt8.ofNat (kb key i))
    (d : Nat) (hd : d + 4 ≤ 16) :
    (memLoad m (r + BitVec.ofNat 64 d) 32).toNat = rNum key / 2 ^ (8 * d) % 2 ^ 32 := by
  have h := memLoad_of_bytes (m := m) (a := r + BitVec.ofNat 64 d) (k := 4)
    (f := fun j => kb key (d + j)) (fun j => kb_lt key _)
    (fun i hi => by rw [add_ofNat_add_ofNat]; exact hk _ (by omega))
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have := leNat_lt (fun j => kb_lt key (d + j)) 4
    simpa using this)]
  have hw := leNat_window (kb_lt key) d 4 (12 - d)
  rw [show d + (4 + (12 - d)) = 16 by omega] at hw
  rw [rNum, Nat.pow_mul, ← hw]

theorem entry_toNat : entry.toNat = 0x101e40 := by simp [entry]

theorem body [Bindings] (key : Vector UInt8 32) (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ entry.toNat + codeLength ≤ boundary.rip.toNat)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : Pre key s) :
    ∃ fuel sA t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x101eb7 ∧
      (headEffect s).Holds s sA ∧ (tailEffect sA).Holds sA t := by
  have hne : ∀ pc : BitVec 64, 0x101e40 ≤ pc.toNat → pc.toNat < 0x101eb8 →
      pc ≠ boundary.rip := by
    intro pc h1 h2 he
    subst he
    rw [entry_toNat] at hb
    simp only [codeLength] at hb
    omega
  have hst : WritableRange s (rdi.read s) 56 := hp.state
  have hw := memWritable_of_writableRange hst (by decide)
  obtain ⟨n1, sA, hA, hrA, _, hEA⟩ := head_block boundary hne s hr
    (program_text_slice hc 0x1e40 26 (by decide +kernel)) ⟨hp.rip, hw, state_apart hst⟩
  have hcA := codeIn_of_agrees hEA.agrees hst.code (head_covers s) hc
  have hraxA : rax.read sA = rdi.read s := hEA.writes.1
  have hrsiA : rsi.read sA = rsi.read s :=
    hEA.agrees.read (by simp [headEffect, Effect.components])
  have hpre : TailPre sA := by
    refine ⟨hEA.rip, ?_, ?_, ?_⟩
    · rw [hrsiA]; exact MemReadable.of_holds hEA hp.keyReadable
    · rw [hraxA]; exact MemWritable.of_holds hEA hw
    · rw [hraxA]; exact state_apart hst
  obtain ⟨n2, t, hB, hrt, _, hEt⟩ := tail_block boundary hne sA hrA
    (program_text_slice hcA 0x1e5a 93 (by decide +kernel)) hpre
  have hct := codeIn_of_agrees hEt.agrees (hraxA ▸ hst.code) (fun c hc x hx => by
    obtain ⟨i, hi, he⟩ := tail_covers sA c hc x hx
    exact ⟨i, by omega, he⟩) hcA
  exact ⟨n1 + n2, sA, t, hA.trans hB, hrt, hct, hEt.rip, hEA, hEt⟩

theorem read_mem_eq (t : RamState) (a : BitVec 64) (n : Nat) :
    (Operand.mem a : Operand n).read t = memLoad t.external a n := rfl

theorem key_bytes {key : Vector UInt8 32} {s : RamState} (hp : Pre key s) :
    ∀ i < 32, memByte s.external (rsi.read s + BitVec.ofNat 64 i) = UInt8.ofNat (kb key i) := by
  intro i hi
  rw [memByte_of_get (hp.keyBytes ⟨i, hi⟩)]
  simp [kb, hi]

theorem limb_values {key : Vector UInt8 32} {s : RamState}
    (hk : ∀ i < 32, memByte s.external (rsi.read s + BitVec.ofNat 64 i) = UInt8.ofNat (kb key i)) :
    (limb0 s).toNat = clamp (rNum key) / 2 ^ (26 * 0) % 2 ^ 26 ∧
    (limb1 s).toNat = clamp (rNum key) / 2 ^ (26 * 1) % 2 ^ 26 ∧
    (limb2 s).toNat = clamp (rNum key) / 2 ^ (26 * 2) % 2 ^ 26 ∧
    (limb3 s).toNat = clamp (rNum key) / 2 ^ (26 * 3) % 2 ^ 26 ∧
    (limb4 s).toNat = clamp (rNum key) / 2 ^ (26 * 4) % 2 ^ 26 := by
  have w0 := key_word hk 0 (by decide)
  have w3 := key_word hk 3 (by decide)
  have w6 := key_word hk 6 (by decide)
  have w9 := key_word hk 9 (by decide)
  have w12 := key_word hk 12 (by decide)
  rw [show rsi.read s + BitVec.ofNat 64 0 = rsi.read s from by simp] at w0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := limb0_bits (rNum key)
    simp only [limb0, mem32, BitVec.toNat_and] at *
    rw [read_mem_eq, w0, Nat.and_comm]
    simpa using this
  · have := limb1_bits (rNum key)
    simp only [limb1, mem32, BitVec.toNat_and, BitVec.toNat_ushiftRight]
    rw [read_mem_eq]
    rw [show rsi.read s + (3 : BitVec 64) = rsi.read s + BitVec.ofNat 64 3 from rfl, w3]
    simpa using this
  · have := limb2_bits (rNum key)
    simp only [limb2, mem32, BitVec.toNat_and, BitVec.toNat_ushiftRight]
    rw [read_mem_eq]
    rw [show rsi.read s + (6 : BitVec 64) = rsi.read s + BitVec.ofNat 64 6 from rfl, w6]
    simpa using this
  · have := limb3_bits (rNum key)
    simp only [limb3, mem32, BitVec.toNat_and, BitVec.toNat_ushiftRight]
    rw [read_mem_eq]
    rw [show rsi.read s + (9 : BitVec 64) = rsi.read s + BitVec.ofNat 64 9 from rfl, w9]
    simpa using this
  · have := limb4_bits (rNum key)
    simp only [limb4, mem32, BitVec.toNat_and, BitVec.toNat_ushiftRight]
    rw [read_mem_eq]
    rw [show rsi.read s + (12 : BitVec 64) = rsi.read s + BitVec.ofNat 64 12 from rfl, w12]
    simpa using this

theorem ofNat_add_ne {a : BitVec 64} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : i ≠ j) : a + BitVec.ofNat 64 i ≠ a + BitVec.ofNat 64 j := by
  intro he
  have := congrArg BitVec.toNat ((BitVec.add_right_inj a).mp he)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact h this

theorem storedByte_zero (n i : Nat) : storedByte (0 : BitVec n) i = 0 := by
  simp [storedByte]

theorem leNat_zero (k : Nat) : leNat (fun _ => 0) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [leNat, ih]

theorem leNat16 (g : Nat → Nat) :
    leNat g 16 = leNat g 4 + 2 ^ 32 * leNat (fun j => g (4 + j)) 4 +
      2 ^ 64 * leNat (fun j => g (8 + j)) 4 + 2 ^ 96 * leNat (fun j => g (12 + j)) 4 := by
  have h1 := leNat_split g 4 12
  have h2 := leNat_split (fun j => g (4 + j)) 4 8
  have h3 := leNat_split (fun j => g (4 + (4 + j))) 4 4
  have e2 : leNat (fun j => g (4 + (4 + j))) 4 = leNat (fun j => g (8 + j)) 4 :=
    leNat_congr fun j _ => by rw [← Nat.add_assoc]
  have e3 : leNat (fun j => g (4 + (4 + (4 + j)))) 4 = leNat (fun j => g (12 + j)) 4 :=
    leNat_congr fun j _ => by rw [← Nat.add_assoc, ← Nat.add_assoc]
  simp only [Nat.reduceAdd] at h1 h2 h3
  rw [h1, h2, h3, e2, e3]
  simp only [Nat.reducePow]
  omega

theorem byte_of_store {m m' : Ram} {a b : BitVec 64} {n : Nat}
    (h : memLoad m a n = memLoad m' b n) {j : Nat} (hj : j < n / 8) :
    memByte m (a + BitVec.ofNat 64 j) = memByte m' (b + BitVec.ofNat 64 j) := by
  rw [← storedByte_memLoad m a j hj, h, storedByte_memLoad m' b j hj]

theorem byte_of_store_zero {m : Ram} {a : BitVec 64} {n : Nat}
    (h : memLoad m a n = 0) {j : Nat} (hj : j < n / 8) :
    memByte m (a + BitVec.ofNat 64 j) = 0 := by
  rw [← storedByte_memLoad m a j hj, h, storedByte_zero]

theorem finish [Bindings] {key : Vector UInt8 32} {s sA t : RamState} (hp : Pre key s)
    (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t) (hip : t.RIP = 0x101eb7)
    (hA : (headEffect s).Holds s sA) (hT : (tailEffect sA).Holds sA t) :
    ∃ u, Machine.step t = some (.next u) ∧ Result key s u := by
  obtain ⟨a1, a2, a3, a4⟩ := hA.writes
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩ := hT.writes
  have hraxA : rax.read sA = rdi.read s := a1
  have hrsiA : rsi.read sA = rsi.read s :=
    hA.agrees.read (by simp [headEffect, Effect.components])
  have hAT := hA.agrees.trans hT.agrees
  have hcov : ∀ c ∈ (headEffect s).components ++ (tailEffect sA).components, ∀ x, c.Covers x →
      ∃ i < 56, x = rdi.read s + BitVec.ofNat 64 i := by
    intro c hc x hx
    rcases List.mem_append.mp hc with hc | hc
    · exact head_covers s c hc x hx
    · obtain ⟨i, hi, he⟩ := tail_covers sA c hc x hx
      exact ⟨i, by omega, hraxA ▸ he⟩
  have hsp : stackPtr t = stackPtr s :=
    hAT.read (r := 4) (n := 64) (by simp [headEffect, tailEffect, unknownFlags, Effect.components])
  have hslot : ∀ i < 8, t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 i]? := by
    intro i hi
    apply hAT.byte
    intro c hc hx
    obtain ⟨j, hj, he⟩ := hcov c hc _ hx
    exact hp.stateReturn j hj i hi he.symm
  have htop : stackTop t = (returnBoundary s).rip := by
    change memLoad t.external (stackPtr t) 64 = memLoad s.external (stackPtr s) 64
    rw [hsp]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun b : Option UInt8 => b.getD 0) (hslot i hi)
  have hread : MemReadable t (stackPtr t) 8 := by
    rw [hsp]
    exact ⟨hp.returnSlot.low, fun i hi => hAT.grow _ (hp.returnSlot.mem i hi)⟩
  obtain ⟨u, hstep, hready, he⟩ := ret_effect_step 0x101eb7 t hr
    (program_text_slice hc 0x1eb7 1 (by decide +kernel))
    ⟨⟨hip, hread⟩, by rw [htop]; exact hp.returnLow⟩
  have hext : u.external = t.external := he.agrees.external (by simp [Component.Covers])
  have hw32 : ∀ a, word32 u a = memLoad t.external a 32 := fun a => by
    rw [word32, read_mem_eq, hext]
  have hkA : ∀ i < 32, memByte sA.external (rsi.read sA + BitVec.ofNat 64 i) =
      UInt8.ofNat (kb key i) := by
    intro i hi
    rw [hrsiA, memByte_of_agrees hA.agrees (fun c hc hx => by
      obtain ⟨j, hj, he⟩ := head_covers s c hc _ hx
      exact hp.stateKey j hj i hi he.symm)]
    exact key_bytes hp i hi
  have lv := limb_values hkA
  have hl : ∀ (k : Nat) (hk : k < 5) (x : BitVec 32),
      (Operand.mem (rax.read sA + BitVec.ofNat 64 (16 + 4 * k)) : Operand 32).read t = x →
      rLimbs u (rdi.read s) ⟨k, hk⟩ = x := by
    intro k hk x hx
    rw [rLimbs, limbsAt, hw32, ← hx, read_mem_eq, hraxA, rOffset,
      show (0x10 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add_ofNat]
  have hcl : ∀ i : Fin 5, (rLimbs u (rdi.read s) i).toNat =
      clamp (rNum key) / 2 ^ (26 * i.val) % 2 ^ 26 := by
    intro i
    match i with
    | ⟨0, _⟩ => rw [hl 0 _ _ w10]; exact lv.1
    | ⟨1, _⟩ => rw [hl 1 _ _ w11]; exact lv.2.1
    | ⟨2, _⟩ => rw [hl 2 _ _ w12]; exact lv.2.2.1
    | ⟨3, _⟩ => rw [hl 3 _ _ w13]; exact lv.2.2.2.1
    | ⟨4, _⟩ => rw [hl 4 _ _ w14]; exact lv.2.2.2.2
  have hpb : ∀ j < 16, memByte t.external (rdi.read s + BitVec.ofNat 64 j) =
      UInt8.ofNat (kb key (16 + j)) := by
    intro j hj
    by_cases h8 : j < 8
    · rw [← hraxA, byte_of_store (n := 64) w8 (by omega),
        show rsi.read sA + 16 = rsi.read sA + BitVec.ofNat 64 16 from rfl, add_ofNat_add_ofNat]
      exact hkA _ (by omega)
    · obtain ⟨k, rfl⟩ : ∃ k, j = 8 + k := ⟨j - 8, by omega⟩
      rw [show rdi.read s + BitVec.ofNat 64 (8 + k) = rax.read sA + 8 + BitVec.ofNat 64 k from by
          rw [hraxA, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, add_ofNat_add_ofNat],
        byte_of_store (n := 64) w9 (by omega),
        show rsi.read sA + 24 = rsi.read sA + BitVec.ofNat 64 24 from rfl, add_ofNat_add_ofNat,
        show 16 + (8 + k) = 24 + k by omega]
      exact hkA _ (by omega)
  have hpw : ∀ k < 4, (word32 u (rdi.read s + BitVec.ofNat 64 (4 * k))).toNat =
      leNat (fun j => kb key (16 + (4 * k + j))) 4 := by
    intro k hk
    rw [hw32]
    rw [show (32 : Nat) = 8 * 4 from rfl, memLoad_of_bytes (fun j => kb_lt key _)
      (fun i hi => by rw [add_ofNat_add_ofNat]; exact hpb _ (by omega)), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa using leNat_lt (fun j => kb_lt key (16 + (4 * k + j))) 4)]
  have hzb : ∀ j < 20, memByte t.external (rdi.read s + BitVec.ofNat 64 (36 + j)) = 0 := by
    intro j hj
    rw [memByte_of_agrees hT.agrees (fun c hc hx => by
      obtain ⟨i, hi, he⟩ := tail_covers sA c hc _ hx
      rw [hraxA] at he
      exact ofNat_add_ne (by omega) (by omega) (by omega) he)]
    rw [← add_ofNat_add_ofNat]
    by_cases h8 : j < 8
    · exact byte_of_store_zero (n := 64) a4 (by omega)
    · by_cases h16 : j < 16
      · obtain ⟨k, rfl⟩ : ∃ k, j = 8 + k := ⟨j - 8, by omega⟩
        rw [← add_ofNat_add_ofNat, add_ofNat_add_ofNat (rdi.read s) 36 8]
        exact byte_of_store_zero (n := 64) a3 (by omega)
      · obtain ⟨k, rfl⟩ : ∃ k, j = 16 + k := ⟨j - 16, by omega⟩
        rw [← add_ofNat_add_ofNat, add_ofNat_add_ofNat (rdi.read s) 36 16]
        exact byte_of_store_zero (n := 32) a2 (by omega)
  refine ⟨u, hstep, hready, he.rip.trans htop, he.writes.trans (congrArg (· + 8) hsp),
    ?_, ?_, ?_, ⟨rNum key, hcl⟩, ?_, ?_⟩
  · exact (he.agrees.read (r := 0) (n := 64) (by simp)).trans
      ((hT.agrees.read (by simp [tailEffect, unknownFlags, Effect.components])).trans hraxA)
  · apply (hAT.trans he.agrees).widen
    · simp [headEffect, tailEffect, unknownFlags, Effect.components, retEffect, changes,
        Component.isMem]
    · intro x c hc hx
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨i, hi, rfl⟩ := hcov c hc x hx
        exact ⟨.mem (rdi.read s) stateBytes, by simp [changes], i, hi, rfl⟩
      · simp only [retEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> exact hx.elim
  · rw [padOf_eq, leNat16]
    unfold wordValue padWords
    have h0 := hpw 0 (by decide)
    have h1 := hpw 1 (by decide)
    have h2 := hpw 2 (by decide)
    have h3 := hpw 3 (by decide)
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3 ⊢
    rw [show rdi.read s + BitVec.ofNat 64 0 = rdi.read s from by simp] at h0
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.mul_zero, Nat.mul_one,
      Nat.reduceMul]
    rw [show rdi.read s + BitVec.ofNat 64 0 = rdi.read s from by simp]
    rw [h0, h1, h2, show (4 * ((3 : Fin 4) : Nat)) = 12 from rfl, h3]
  · rw [limbValue_clamped (rNum key) hcl, rNum_eq]
    rfl
  · intro i
    rw [hLimbs, limbsAt, hw32, hOffset, show (0x24 : BitVec 64) = BitVec.ofNat 64 36 from rfl,
      add_ofNat_add_ofNat, show (32 : Nat) = 8 * 4 from rfl,
      memLoad_of_bytes (f := fun _ => 0) (fun _ => by decide) (fun j hj => by
        rw [add_ofNat_add_ofNat, show 36 + 4 * i.val + j = 36 + (4 * i.val + j) by omega,
          hzb _ (by omega)]
        rfl), leNat_zero]
    rfl

theorem returns [Bindings] (key : Vector UInt8 32) (s : RamState) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hp : Pre key s) :
    ∃ fuel t, Returns (returnBoundary s) fuel s t ∧ Result key s t := by
  obtain ⟨fuel, sA, t, hrun, hrt, hct, hip, hA, hT⟩ :=
    body key (returnBoundary s) hp.returnOutside s hr hc hp
  obtain ⟨u, hstep, hres⟩ := finish hp hrt hct hip hA hT
  exact ⟨fuel + 1, u, hrun.returns (Returns.of_step hstep hres.rip hres.rsp), hres⟩

theorem advances [Bindings] (key : Vector UInt8 32) (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < entry.toNat ∨ entry.toNat + codeLength ≤ boundary.rip.toNat)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : Pre key s) (hne : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ Result key s t := by
  obtain ⟨fuel, sA, t, hrun, hrt, hct, hip, hA, hT⟩ := body key boundary hb s hr hc hp
  obtain ⟨u, hstep, hres⟩ := finish hp hrt hct hip hA hT
  exact ⟨fuel + 1, u, hrun.trans (Advances.of_step hstep (.inl (by rw [hres.rip]; exact hne))),
    hres⟩

end ChaCha20Poly1305.Proofs.Poly1305.Callee101e40
