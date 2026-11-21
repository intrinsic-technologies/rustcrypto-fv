import P256.Proofs.HMAC.Finalize.CopyWords

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding.Block

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Common
open P256.Proofs.Common.Instructions

structure StorePre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : ∀ i ∈ ([64,128] : List (BitVec 64)), MemWritable s (rspOf s + i) 8
  codeApart : ∀ i ∈ ([64,128] : List (BitVec 64)), RangeApart (rspOf s + i) 8 p 13

def storeBytes (r : BitVec 3) : List UInt8 :=
  [0x4c,0x89,(AddrMode.sib 4 none 0 (.d32 128)).modrm r,0x24,128,0,0,0,
    0x4c,0x89,(AddrMode.sib 4 none 0 (.d8 64)).modrm r,0x24,64]

def storeEffect (p : BitVec 64) (r : BitVec 3) (s : RamState) : Effect :=
  { rip := p + 13
    writes := [⟨(.mem (rspOf s + 128) : Operand 64),
      (.reg (gprNumber 0 1 r) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 64) : Operand 64),
      (.reg (gprNumber 0 1 r) : Operand 64).read s⟩] }

theorem store_run [Bindings] (p : BitVec 64) (r : BitVec 3) (boundary : ReturnBoundary)
    (next : ∀ i : Nat, i ≤ 13 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (StorePre p) (codeRange p (storeBytes r))
      (Effect.post (storeEffect p r)) := by
  advance_begin (mov_m64_r64_effect_step p 0x4c (by simp [RexWPrefix]) r
    (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case pre =>
    intro s hp
    refine ⟨hp.rip, hp.writable 128 (by simp), ?_⟩
    intro i hi j hj
    exact hp.codeApart 128 (by simp) i hi j (by change j < 8 at hj; omega)
  case av =>
    intro s hp
    apply Effect.avoids_codeRange
    x86_norm
    exact hp.codeApart 128 (by simp)
  case sub =>
    rw [show (AddrMode.sib 4 none 0 (.d32 128)).tail = [36,128,0,0,0] by decide +kernel]
    simpa [storeBytes] using codeRange_slice_subset p (storeBytes r) 0 8
  case next => exact fun _ _ => next 8 (by decide)
  advance_then (mov_m64_r64_effect_step (p + 8) 0x4c (by simp [RexWPrefix]) r
    (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset p (storeBytes r) 8 5
  case mid =>
    intro s t hp hh ho
    refine ⟨X86Proofs.StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hp.writable 64 (by simp)
    · x86_norm
      intro i hi j hj
      have h := hp.codeApart 64 (by simp) i hi (8+j) (by change j < 5 at hj; omega)
      simpa only [rspOf, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.codeApart 64 (by simp)
    · x86_norm
      exact next 13 (by decide)
  advance_finish [storeEffect]

def setupBytes (r : UInt8) : List UInt8 :=
  [0x48,0x8d,0x74,0x24,8,0xba,1,0,0,0,0x4c,0x89,r]

def setupEffect (p : BitVec 64) (r : UInt8) (s : RamState) : Effect :=
  { rip := p + 13
    writes := [⟨(.reg 6 : Operand 64), rspOf s + 8⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), (.reg (gprNumber 0 1 (modrmReg r)) : Operand 64).read s⟩] }

theorem setup_run [Bindings] (p : BitVec 64) (r : UInt8)
    (encoding : r = 0xff ∨ r = 0xf7) (boundary : ReturnBoundary)
    (next : ∀ i : Nat, i ≤ 13 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p (setupBytes r))
      (Effect.post (setupEffect p r)) := by
  rcases encoding with rfl | rfl
  all_goals
    advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    case next => exact fun _ _ => next 5 (by decide)
    advance_then (mov_r32_imm32_effect_step (p + 5) 0xba (by decide) 1)
    try (case sub => exact codeRange_slice_subset p _ 5 5)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · x86_norm; exact next 10 (by decide)
  · advance_then (mov_r64_r64_effect_step (p + 10) 0x4c 0xff (by simp [RexWPrefix]) rfl)
    try (case sub => exact codeRange_slice_subset p _ 10 3)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · x86_norm; exact next 13 (by decide)
    advance_finish [setupEffect]
  · advance_then (mov_r64_r64_effect_step (p + 10) 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
    try (case sub => exact codeRange_slice_subset p _ 10 3)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · x86_norm; exact next 13 (by decide)
    advance_finish [setupEffect]



structure Pre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : ∀ i ∈ ([72,80,88,96,104,112,120] : List (BitVec 64)),
    MemReadable s (rspOf s + i) 8
  writable : ∀ i ∈ ([8,16,24,32,40,48,56,64,128] : List (BitVec 64)),
    MemWritable s (rspOf s + i) 8
  codeApart : ∀ i ∈ ([8,16,24,32,40,48,56,64,128] : List (BitVec 64)),
    RangeApart (rspOf s + i) 8 p 96

def bytes (r : BitVec 3) (q : UInt8) := storeBytes r ++ CopyWords.bytes ++ setupBytes q

def effect (p : BitVec 64) (r : BitVec 3) (q : UInt8) (s : RamState) : Effect :=
  { rip := p + 96
    writes := [
      ⟨(.mem (rspOf s + 128) : Operand 64), (.reg (gprNumber 0 1 r) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 64) : Operand 64), (.reg (gprNumber 0 1 r) : Operand 64).read s⟩,
      ⟨(.reg 0 : Operand 64), (.mem (rspOf s + 72) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (rspOf s + 80) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 8) : Operand 64), (.mem (rspOf s + 72) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), (.mem (rspOf s + 80) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), (.mem (rspOf s + 88) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 32) : Operand 64), (.mem (rspOf s + 96) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 40) : Operand 64), (.mem (rspOf s + 104) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 48) : Operand 64), (.mem (rspOf s + 112) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 56) : Operand 64), (.mem (rspOf s + 120) : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 8⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), (.reg (gprNumber 0 1 (modrmReg q)) : Operand 64).read s⟩] }

theorem copy_local (p : BitVec 64) : Effect.Local (CopyWords.effect p) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [CopyWords.effect, rspOf, h.read_reg, h.read_mem]
  · intro s
    simp [CopyWords.effect, Write.Full, Operand.Full]

theorem setup_local (p : BitVec 64) (q : UInt8) : Effect.Local (setupEffect p q) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [setupEffect, rspOf, h.read_reg]
  · intro s
    simp [setupEffect, Write.Full, Operand.Full]

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (p : BitVec 64) (r : BitVec 3) (q : UInt8)
    (encoding : q = 0xff ∨ q = 0xf7) (boundary : ReturnBoundary)
    (next : ∀ i : Nat, i ≤ 96 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (Pre p) (codeRange p (bytes r q)) (Effect.post (effect p r q)) := by
  intro s ready loaded hp
  obtain ⟨na, a, ra, readyA, _, ha⟩ := store_run p r boundary (fun i hi => next i (by omega))
    s ready (loaded.mono (by
      intro x hx
      exact codeRange_slice_subset p (bytes r q) 0 13 x (by simpa [bytes, storeBytes] using hx)))
    ⟨hp.rip, fun i hi => hp.writable i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> simp), fun i hi a ha b hb =>
      hp.codeApart i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> simp) a ha b (by omega)⟩
  have spA : rspOf a = rspOf s := ha.agrees.read (n := 64) (r := 4) (by simp [storeEffect, Effect.components])
  have loadedA : CodeIn (codeRange p (bytes r q)) a := ha.codeIn (by
    apply Effect.avoids_codeRange
    x86_norm [storeEffect]
    exact ⟨hp.codeApart 128 (by simp), hp.codeApart 64 (by simp)⟩) loaded
  obtain ⟨nb, b, rb, readyB, _, hb⟩ := CopyWords.run (p+13) boundary (by
    intro i hi
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using next (13+i) (by omega))
    a readyA (loadedA.mono (codeRange_slice_subset p (bytes r q) 13 70))
    ⟨ha.rip, fun i hi => by rw [spA]; exact (hp.readable i hi).of_holds ha,
      fun i hi => by rw [spA]; exact (hp.writable i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)).of_holds ha,
      fun i hi j hj k hk => by
        rw [spA]
        have h := hp.codeApart i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) j hj (13+k) (by omega)
        simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using h⟩
  have hab := ha.seq (copy_local (p+13)) (by simp [storeEffect, Write.Full, Operand.Full]) hb
  have spB : rspOf b = rspOf s :=
    (hb.agrees.read (n := 64) (r := 4) (by simp [CopyWords.effect, Effect.components])).trans spA
  have loadedB : CodeIn (codeRange p (bytes r q)) b := hb.codeIn (by
    apply Effect.avoids_codeRange
    x86_norm [CopyWords.effect]
    change rspOf a = rspOf s at spA
    simp only [rspOf, BitVec.ofNat_eq_ofNat] at spA
    rw [spA]
    exact ⟨hp.codeApart 8 (by simp), hp.codeApart 16 (by simp),
      hp.codeApart 24 (by simp), hp.codeApart 32 (by simp), hp.codeApart 40 (by simp),
      hp.codeApart 48 (by simp), hp.codeApart 56 (by simp)⟩) loadedA
  obtain ⟨nc, c, rc, readyC, _, hc⟩ := setup_run (p+83) q encoding boundary (by
    intro i hi
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using next (83+i) (by omega))
    b readyB (loadedB.mono (codeRange_slice_subset p (bytes r q) 83 13))
    (by simpa only [CopyWords.effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hb.rip)
  refine ⟨na+nb+nc, c, (ra.trans rb).trans rc, readyC, ?_, ?_⟩
  · exact hc.codeIn (Effect.Avoids.of_noMem (by simp [setupEffect, Effect.components, Component.Covers]) _) loadedB
  · have h := hab.seq (setup_local (p+83) q) (by
      x86_norm [storeEffect, CopyWords.effect]) hc
    rcases encoding with rfl | rfl
    all_goals
      apply h.weaken
      · x86_norm [effect, storeEffect, CopyWords.effect, setupEffect]
      · x86_norm [effect, storeEffect, CopyWords.effect, setupEffect]
      · intro i; cases i <;> x86_norm [effect, storeEffect, CopyWords.effect, setupEffect]
      · x86_norm [effect, storeEffect, CopyWords.effect, setupEffect]

end P256.Proofs.HMAC.Finalize.Padding.Block
