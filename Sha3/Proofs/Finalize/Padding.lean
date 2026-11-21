import Sha3.Proofs.Finalize.Layout
import Sha3.Proofs.Finalize.Padding.Bytes
import Sha3.Proofs.Finalize.Padding.Lanes
import Sha3.Proofs.Memory
import Sha3.Proofs.Image
import Sha3.Proofs.Run
import Sha3.Proofs.Stores.ByteXor
import Sha3.Proofs.X86.Instructions.MovzxLoad.Triple
import Sha3.Proofs.Scalar.Move.Triple
import Sha3.Proofs.Scalar.Shift.Step
import Sha3.Proofs.Scalar.Address.Lea
import Sha3.Proofs.X86.Instructions.And.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple
import Sha3.Proofs.Stores.ByteMov

namespace Sha3.Proofs.Finalize.Padding

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program
open Variant (rate)

def finalMode : Variant → AddrMode
  | .sha224 => .base 7 (.d32 143)
  | .sha256 => .base 7 (.d32 135)
  | .sha384 => .base 7 (.d8 103)
  | .sha512 => .base 7 (.d8 71)

def finish (v : Variant) (reset : Bool := false)
    (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  Finalize.callAddress v reset keccak fullState

def metadataMode : AddrMode := .base 7 (.d32 200)

def laneMode : AddrMode := .sib 7 (some 0) 0 .none

def finalBytes (v : Variant) : List UInt8 :=
  0x80 :: (finalMode v).modrm 6 :: ((finalMode v).tail ++ [0x80])

def clobbers (ptr : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 14, .flags, .rip, .mem ptr 201]

structure Context [Bindings] (boundary : ReturnBoundary) (sp ptr : BitVec 64)
    (s : RamState) : Prop where
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  stack : (Operand.reg 4 : Operand 64).read s = sp
  state : (Operand.reg 7 : Operand 64).read s = ptr
  readable : MemReadable s ptr 201
  avoids : ∀ i < 201, ¬ (InProgram (ptr + BitVec.ofNat 64 i) ∨
    InPageTables (ptr + BitVec.ofNat 64 i))
  boundary : sp ≠ boundary.rsp

theorem Context.of_frame [Bindings] {boundary : ReturnBoundary} {sp ptr : BitVec 64}
    {s t : RamState} (h : Context boundary sp ptr s)
    (ha : AgreesExcept (clobbers ptr) s t) (hr : ReadyToStep t) : Context boundary sp ptr t := by
  refine ⟨hr, ?_, (ha.read (by simp (config := { decide := true }) [clobbers])).trans h.stack,
    (ha.read (by simp (config := { decide := true }) [clobbers])).trans h.state,
    ⟨h.readable.low, fun i hi ↦ ha.grow _ (h.readable.mem i hi)⟩, h.avoids, h.boundary⟩
  intro address byte hbyte
  rw [ha.byte]
  · exact h.loaded address byte hbyte
  · intro c hc hcover
    simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    exact h.avoids i hi (.inl ⟨byte, hbyte⟩)

theorem clobbers_trans {ptr : BitVec 64} {s t u : RamState}
    (h : AgreesExcept (clobbers ptr) s t) (h' : AgreesExcept (clobbers ptr) t u) :
    AgreesExcept (clobbers ptr) s u :=
  (h.trans h').mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)

theorem memory_frame {ptr : BitVec 64} {s t : RamState} {offset count : Nat}
    {cs : List Component} (h : AgreesExcept cs s t) (hsize : offset + count ≤ 201)
    (hcs : ∀ c ∈ cs, c = .mem (ptr + BitVec.ofNat 64 offset) count ∨
      (c ∈ clobbers ptr ∧ c.isMem = false)) : AgreesExcept (clobbers ptr) s t := by
  apply h.widen
  · intro c hc hn
    rcases hcs c hc with rfl | ⟨hm, _⟩
    · simp [Component.isMem] at hn
    · exact hm
  · intro x c hc hcover
    rcases hcs c hc with rfl | ⟨_, hn⟩
    · obtain ⟨i, hi, rfl⟩ := hcover
      refine ⟨.mem ptr 201, by simp (config := { decide := true }) [clobbers],
        offset + i, by omega, ?_⟩
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    · cases c <;> simp_all [Component.isMem, Component.Covers]

theorem step_advance [Bindings] {boundary : ReturnBoundary} {sp ptr p : BitVec 64}
    {s : RamState} {bytes : List UInt8} {pre : RamState → Prop} {effect : RamState → Effect}
    (h : Context boundary sp ptr s) (step : StepEffect pre (codeRange p bytes) effect)
    (image : ∀ byte ∈ codeRange p bytes, byte.1.toNat < userAddressLimit ∧
      Extracted.programSections.fetchByte byte.1 = some byte.2)
    (frame : ∀ t, (effect s).Holds s t → AgreesExcept (clobbers ptr) s t)
    (hp : pre s) :
    ∃ t, Advances boundary 1 s t ∧ Context boundary sp ptr t ∧
      (effect s).Holds s t ∧ AgreesExcept (clobbers ptr) s t := by
  have code : CodeIn (codeRange p bytes) s :=
    fun byte hb ↦ ⟨(image byte hb).1, programLoaded_fetchByte h.loaded (image byte hb).2⟩
  obtain ⟨t, ht, hr, he⟩ := step s h.ready code hp
  have ha := frame t he
  have hc := h.of_frame ha hr
  refine ⟨t, Advances.of_step ht (.inr ?_), hc, he, ha⟩
  change (Operand.reg 4 : Operand 64).read t ≠ _
  rw [hc.stack]
  exact h.boundary

theorem scalar_image (v : Variant) (reset : Bool := false)
    (keccak : Bool := false) (fullState : Bool := false)
    (hfull : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    (∀ byte ∈ codeRange (Finalize.entryAddress v reset keccak fullState + (7 : BitVec 64))
      [0x0f, 0xb6, 0x87, 0xc8, 0, 0, 0],
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2) ∧
    (∀ byte ∈ codeRange (Finalize.entryAddress v reset keccak fullState + (14 : BitVec 64))
      [0x8d, 0x0c, 0xc5, 0, 0, 0, 0],
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2) ∧
    (∀ byte ∈ codeRange (Finalize.entryAddress v reset keccak fullState + (21 : BitVec 64))
      [0xba, Variant.suffix keccak, 0, 0, 0],
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2) ∧
    (∀ byte ∈ codeRange (Finalize.entryAddress v reset keccak fullState + (26 : BitVec 64)) [0x48, 0xd3, 0xe2],
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2) ∧
    (∀ byte ∈ codeRange (Finalize.entryAddress v reset keccak fullState + (29 : BitVec 64)) [0x83, 0xe0, 0xf8],
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2) := by
  cases fullState <;> cases v <;> cases reset <;> cases keccak <;>
    try (obtain ⟨hv, hk⟩ := hfull rfl; contradiction)
  all_goals decide +kernel

theorem read_reg_width (s : RamState) (r : BitVec 5) (n : Nat) :
    (Operand.reg r : Operand n).read s = ((Operand.reg r : Operand 64).read s).setWidth n := by
  change (s.GPR[gprIndex r] : BitVec 64).setWidth n =
    ((s.GPR[gprIndex r] : BitVec 64).setWidth 64).setWidth n
  exact (BitVec.setWidth_setWidth (by omega)).symm

theorem scalar_arithmetic (r : Fin 200) :
    (((BitVec.ofNat 64 r.val).setWidth 8).setWidth 64 = BitVec.ofNat 64 r.val) ∧
    (shiftCount 64 ((((BitVec.ofNat 64 r.val * 8).setWidth 32).setWidth 64).setWidth 8) =
      8 * (r.val % 8)) ∧
    ((((BitVec.ofNat 64 r.val).setWidth 32) &&& (0xfffffff8 : BitVec 32)).setWidth 64 =
      BitVec.ofNat 64 (r.val / 8 * 8)) := by
  revert r
  decide +kernel

theorem scalar_steps [Bindings] {boundary : ReturnBoundary} {v : Variant} {reset : Bool}
    {keccak fullState : Bool}
    {sp ptr : BitVec 64}
    {s : RamState} (h : Context boundary sp ptr s) (r : Fin 200)
    (hr : (Operand.mem (ptr + (200 : BitVec 64)) : Operand 8).read s = BitVec.ofNat 8 r.val)
    (hip : s.RIP = Finalize.entryAddress v reset keccak fullState + (7 : BitVec 64))
    (hfull : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    ∃ t, Advances boundary 5 s t ∧ Context boundary sp ptr t ∧
      t.RIP = Finalize.entryAddress v reset keccak fullState + (32 : BitVec 64) ∧
      AgreesExcept (clobbers ptr) s t ∧
      t.external = s.external ∧
      (Operand.reg 0 : Operand 64).read t = BitVec.ofNat 64 (r.val / 8 * 8) ∧
      (Operand.reg 2 : Operand 64).read t = (Variant.suffix keccak).toBitVec.setWidth 64 <<< (8 * (r.val % 8)) := by
  obtain ⟨himage1, himage2, himage3, himage4, himage5⟩ := scalar_image v reset keccak fullState hfull
  have hmetadata (next : BitVec 64) : metadataMode.addr s next = ptr + (200 : BitVec 64) := by
    change (Operand.reg 7 : Operand 64).read s + (200 : BitVec 64) = _
    rw [h.state]
  obtain ⟨t1, hstep1, hc1, he1, ha1⟩ := step_advance h
    (movzx_r32_m8_effect_step (Finalize.entryAddress v reset keccak fullState + (7 : BitVec 64)) 0 metadataMode
      (by unfold metadataMode AddrMode.Valid; decide) (by decide) (by decide)) himage1
    (fun _ he ↦ he.agrees.mono (by simp (config := { decide := true }) [clobbers])) ⟨hip, by
      rw [hmetadata]
      exact readable_slice h.readable 200 1 (by decide)⟩
  have hr1 : (Operand.reg 0 : Operand 64).read t1 = BitVec.ofNat 64 r.val := by
    have hw := he1.writes
    change (Operand.reg 0 : Operand 64).read t1 =
      ((Operand.mem (metadataMode.addr s
        (Finalize.entryAddress v reset keccak fullState + 7 + 7)) : Operand 8).read s).setWidth 64 at hw
    rw [hmetadata, hr] at hw
    have hext : (BitVec.ofNat 8 r.val).setWidth 64 = BitVec.ofNat 64 r.val := by
      have hrlt := r.isLt
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    rw [hext] at hw
    exact hw
  have hip1 : t1.RIP = Finalize.entryAddress v reset keccak fullState + (14 : BitVec 64) := by
    have hip1 := he1.rip
    change t1.RIP = Finalize.entryAddress v reset keccak fullState + (7 : BitVec 64) + (7 : BitVec 64) at hip1
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using hip1
  obtain ⟨t2, hstep2, hc2, he2, ha2⟩ := step_advance hc1
    (lea_ecx_rax8_effect_step (Finalize.entryAddress v reset keccak fullState + (14 : BitVec 64))) himage2
    (fun _ he ↦ he.agrees.mono (by simp [leaEcxRax8Effect, Effect.components, clobbers])) hip1
  have hr2 : (Operand.reg 1 : Operand 64).read t2 =
      ((BitVec.ofNat 64 r.val * 8).setWidth 32).setWidth 64 := by
    have hw := he2.writes
    change (Operand.reg 1 : Operand 64).read t2 =
      (((Operand.reg 0 : Operand 64).read t1 * 8).setWidth 32).setWidth 64 at hw
    rwa [hr1] at hw
  have hip2 : t2.RIP = Finalize.entryAddress v reset keccak fullState + (21 : BitVec 64) := by
    simpa only [leaEcxRax8Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using he2.rip
  obtain ⟨t3, hstep3, hc3, he3, ha3⟩ := step_advance hc2
    (mov_r32_imm32_effect_step (Finalize.entryAddress v reset keccak fullState + (21 : BitVec 64))
      0xba (by decide) ((Variant.suffix keccak).toBitVec.setWidth 32)) (by
      cases keccak <;> cases fullState <;> exact himage3)
    (fun _ he ↦ he.agrees.mono (by
      change ∀ c ∈ [Component.reg 2, .rip], c ∈ clobbers ptr
      simp [clobbers])) hip2
  have hr3 : (Operand.reg 2 : Operand 64).read t3 = (Variant.suffix keccak).toBitVec.setWidth 64 := by
    have hw : (Operand.reg 2 : Operand 64).read t3 =
        ((Variant.suffix keccak).toBitVec.setWidth 32).setWidth 64 := he3.writes
    simpa only [BitVec.setWidth_setWidth (by decide : ¬(32 < 8 ∧ 32 < 64))] using hw
  have hc3value : (Operand.reg 1 : Operand 64).read t3 =
      ((BitVec.ofNat 64 r.val * 8).setWidth 32).setWidth 64 :=
    (he3.agrees.read (by
      change Component.reg 1 ∉ [Component.reg 2, .rip]
      decide)).trans hr2
  have hip3 : t3.RIP = Finalize.entryAddress v reset keccak fullState + (26 : BitVec 64) := by
    simpa only [movR32Imm32Effect, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
      using he3.rip
  obtain ⟨t4, hstep4, hc4, he4, ha4⟩ := step_advance hc3
    (shl_rdx_cl_effect_step (Finalize.entryAddress v reset keccak fullState + (26 : BitVec 64))) himage4
    (fun _ he ↦ he.agrees.mono (by simp [shlR64ClEffect_components, clobbers])) hip3
  have hr4 : (Operand.reg 2 : Operand 64).read t4 =
      (Variant.suffix keccak).toBitVec.setWidth 64 <<< (8 * (r.val % 8)) := by
    have hw := he4.writes
    change (Operand.reg 2 : Operand 64).read t4 =
      (Operand.reg 2 : Operand 64).read t3 <<<
        shiftCount 64 ((Operand.reg 1 : Operand 8).read t3) at hw
    rwa [hr3, read_reg_width t3 1 8, hc3value, (scalar_arithmetic r).2.1] at hw
  have hip4 : t4.RIP = Finalize.entryAddress v reset keccak fullState + (29 : BitVec 64) := by
    simpa only [shlR64ClEffect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using he4.rip
  have ha4value : (Operand.reg 0 : Operand 64).read t4 = BitVec.ofNat 64 r.val := by
    rw [he4.agrees.read (by simp [shlR64ClEffect_components]),
      he3.agrees.read (by
        change Component.reg 0 ∉ [Component.reg 2, .rip]
        decide),
      he2.agrees.read (by simp [leaEcxRax8Effect, Effect.components])]
    exact hr1
  obtain ⟨t5, hstep5, hc5, he5, ha5⟩ := step_advance hc4
    (and_r32_imm8_effect_step (Finalize.entryAddress v reset keccak fullState + (29 : BitVec 64))
      0xe0 0xf8 (by decide) (by decide)) himage5
    (fun _ he ↦ he.agrees.mono (by simp (config := { decide := true }) [clobbers])) hip4
  refine ⟨t5, hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans hstep5))), hc5,
    ?_, clobbers_trans ha1 (clobbers_trans ha2 (clobbers_trans ha3 (clobbers_trans ha4 ha5))),
    ?_, ?_, (he5.agrees.read (by
      change Component.reg 2 ∉ [.reg 0, .flags, .rip]; decide)).trans hr4⟩
  · simpa only [andR32Imm8Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using he5.rip
  · rw [he5.agrees.external (by simp [Component.Covers]),
      he4.agrees.external (by simp [shlR64ClEffect_components, Component.Covers]),
      he3.agrees.external (by simp [Component.Covers]),
      he2.agrees.external (by simp [leaEcxRax8Effect, Effect.components, Component.Covers]),
      he1.agrees.external (by simp [movzxR32M8Effect_components, Component.Covers])]
  · have hw := he5.writes
    change (Operand.reg 0 : Operand 64).read t5 =
      (((Operand.reg 0 : Operand 32).read t4) &&& (0xfffffff8 : BitVec 32)).setWidth 64 at hw
    rwa [read_reg_width t4 0 32, ha4value, (scalar_arithmetic r).2.2] at hw

theorem lane_address (s : RamState) (next : BitVec 64) :
    laneMode.addr s next = (Operand.reg 7 : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s := by
  simp [laneMode, AddrMode.addr, AddrMode.reg64, Disp.value]

theorem final_spec (v : Variant) :
    (finalMode v).Valid ∧ (finalMode v).rexX = 0 ∧ (finalMode v).rexB = 0 ∧
    0 < rate v ∧ rate v ≤ 144 ∧
    ∀ s next, (finalMode v).addr s next =
      (Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 (rate v - 1) := by
  cases v <;> simp (config := { decide := true })
    [finalMode, rate, Variant.lanes, AddrMode.addr, AddrMode.reg64, Disp.value]

theorem memory_image (v : Variant) (reset : Bool := false)
    (keccak : Bool := false) (fullState : Bool := false)
    (hfull : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    (∀ byte ∈ codeRange (Finalize.entryAddress v reset keccak fullState + (32 : BitVec 64))
      [0x48, 0x31, 0x14, 0x07],
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2) ∧
    (∀ byte ∈ codeRange (Finalize.entryAddress v reset keccak fullState + (36 : BitVec 64)) [0x49, 0x89, 0xf6],
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2) ∧
    (∀ byte ∈ codeRange (Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64)) (finalBytes v),
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2) := by
  cases fullState <;> cases v <;> cases reset <;> cases keccak <;>
    try (obtain ⟨hv, hk⟩ := hfull rfl; contradiction)
  all_goals decide +kernel

theorem lane_effect [Bindings] (p : BitVec 64) :
    StepEffect (StorePreReadable p (storeAddrAt p laneMode 4) 8)
      (codeRange p [0x48, 0x31, 0x14, 0x07])
      (xorMREffect p 4 64 2 laneMode) :=
  xor_m64_r64_effect_step_of_readable p 0x48 (by unfold RexWPrefix; decide) 2 laneMode
    (by unfold laneMode AddrMode.Valid; decide) (by decide) (by decide)

theorem final_effect [Bindings] (v : Variant) (reset : Bool := false)
    (keccak : Bool := false) (fullState : Bool := false) :
    StepEffect (StorePreReadable (Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64))
      (storeAddrAt (Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64))
        (finalMode v) (3 + (finalMode v).tail.length)) 1)
      (codeRange (Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64)) (finalBytes v))
      (xorM8Imm8Effect (Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64))
        (3 + (finalMode v).tail.length)
        (finalMode v) 0x80) :=
  xor_m8_imm8_effect_step_of_readable _ _ (final_spec v).1
    (final_spec v).2.1 (final_spec v).2.2.1 0x80

theorem Context.store_pre [Bindings] {boundary : ReturnBoundary} {sp ptr p : BitVec 64}
    {s : RamState} {address : RamState → BitVec 64} {offset count : Nat}
    (h : Context boundary sp ptr s) (hip : s.RIP = p)
    (haddr : address s = ptr + BitVec.ofNat 64 offset) (hsize : offset + count ≤ 201) :
    StorePreReadable p address count s := by
  refine ⟨⟨hip, ?_⟩, ?_⟩
  · rw [haddr]
    exact readable_slice h.readable offset count hsize
  · intro i hi
    rw [haddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact fun ht ↦ h.avoids (offset + i) (by omega) (.inr ht)

theorem lane_advance [Bindings] {boundary : ReturnBoundary} {v : Variant} {reset : Bool}
    {keccak fullState : Bool}
    {sp ptr : BitVec 64}
    {s : RamState} {bytes : Nat → UInt8} (h : Context boundary sp ptr s) (r : Fin 200)
    (hip : s.RIP = Finalize.entryAddress v reset keccak fullState + (32 : BitVec 64))
    (hax : (Operand.reg 0 : Operand 64).read s = BitVec.ofNat 64 (r.val / 8 * 8))
    (hdx : (Operand.reg 2 : Operand 64).read s = (Variant.suffix keccak).toBitVec.setWidth 64 <<< (8 * (r.val % 8)))
    (hb : Bytes s.external ptr 200 bytes)
    (hfull : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    ∃ t, Advances boundary 1 s t ∧ Context boundary sp ptr t ∧
      t.RIP = Finalize.entryAddress v reset keccak fullState + (36 : BitVec 64) ∧
      AgreesExcept (clobbers ptr) s t ∧
      Bytes t.external ptr 200 (fun i ↦ bytes i ^^^ (if i = r.val then Variant.suffix keccak else 0)) := by
  have haddr : storeAddrAt (Finalize.entryAddress v reset keccak fullState + (32 : BitVec 64)) laneMode 4 s =
      ptr + BitVec.ofNat 64 (r.val / 8 * 8) := by
    rw [storeAddrAt, lane_address, h.state, hax]
  simp only [storeAddrAt] at haddr
  have hspan : r.val / 8 * 8 + 8 ≤ 200 := by have := r.isLt; omega
  have hpre := h.store_pre
    (address := storeAddrAt (Finalize.entryAddress v reset keccak fullState + (32 : BitVec 64)) laneMode 4)
    hip haddr (Nat.le_trans hspan (by decide))
  obtain ⟨t, ht, hc, he, ha⟩ := step_advance h
    (lane_effect (Finalize.entryAddress v reset keccak fullState + (32 : BitVec 64))) (memory_image v reset keccak fullState hfull).1
    (fun _ he ↦ memory_frame he.agrees (Nat.le_trans hspan (by decide)) (by
      simpa only [xorMREffect_components, haddr, Nat.reduceDiv] using
        (show ∀ c ∈ [.mem (ptr + BitVec.ofNat 64 (r.val / 8 * 8)) 8, .flags, .rip],
          c = .mem (ptr + BitVec.ofNat 64 (r.val / 8 * 8)) 8 ∨
            c ∈ clobbers ptr ∧ c.isMem = false by simp [clobbers, Component.isMem]))) hpre
  refine ⟨t, ht, hc, ?_, ha, ?_⟩
  · simpa only [xorMREffect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
      using he.rip
  · have hext := single_store_external (by decide : 64 ≤ 128) hpre.1.2.mem he
    change t.external = memStore s.external
      (storeAddrAt (Finalize.entryAddress v reset keccak fullState + (32 : BitVec 64)) laneMode 4 s)
      ((Operand.mem (storeAddrAt (Finalize.entryAddress v reset keccak fullState + (32 : BitVec 64))
        laneMode 4 s) : Operand 64).read s ^^^
        (Operand.reg 2 : Operand 64).read s) at hext
    rw [storeAddrAt, haddr, hdx] at hext
    rw [hext]
    exact xor_padding_lane hb (by decide) r.isLt hspan (Variant.suffix keccak)

theorem final_advance [Bindings] {boundary : ReturnBoundary} {v : Variant} {reset : Bool}
    {keccak fullState : Bool}
    {sp ptr : BitVec 64}
    {s : RamState} {bytes : Nat → UInt8} (h : Context boundary sp ptr s)
    (hip : s.RIP = Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64))
    (hb : Bytes s.external ptr 200 bytes)
    (hfull : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    ∃ t, Advances boundary 1 s t ∧ Context boundary sp ptr t ∧ t.RIP = finish v reset keccak fullState ∧
      AgreesExcept (clobbers ptr) s t ∧
      (Operand.reg 14 : Operand 64).read t = (Operand.reg 14 : Operand 64).read s ∧
      Bytes t.external ptr 200 (fun i ↦ bytes i ^^^ (if i + 1 = rate v then 0x80 else 0)) := by
  have haddr : storeAddrAt (Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64)) (finalMode v)
      (3 + (finalMode v).tail.length) s = ptr + BitVec.ofNat 64 (rate v - 1) := by
    rw [storeAddrAt, (final_spec v).2.2.2.2.2, h.state]
  simp only [storeAddrAt] at haddr
  have hratepos := (final_spec v).2.2.2.1
  have hrate := (final_spec v).2.2.2.2.1
  have hspan : rate v - 1 + 1 ≤ 201 := by omega
  have hpre := h.store_pre
    (address := storeAddrAt (Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64))
    (finalMode v) (3 + (finalMode v).tail.length)) hip haddr hspan
  obtain ⟨t, ht, hc, he, ha⟩ := step_advance h (final_effect v reset keccak fullState)
    (memory_image v reset keccak fullState hfull).2.2
    (fun _ he ↦ memory_frame he.agrees hspan (by
      simpa only [xorM8Imm8Effect_components, haddr] using
        (show ∀ c ∈ [.mem (ptr + BitVec.ofNat 64 (rate v - 1)) 1, .flags, .rip],
          c = .mem (ptr + BitVec.ofNat 64 (rate v - 1)) 1 ∨
            c ∈ clobbers ptr ∧ c.isMem = false by simp [clobbers, Component.isMem]))) hpre
  refine ⟨t, ht, hc, ?_, ha, he.agrees.read (by simp), ?_⟩
  · have hfinish : Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64) +
        BitVec.ofNat 64 (3 + (finalMode v).tail.length) = finish v reset keccak fullState := by
      cases fullState <;> cases v <;> cases reset <;> cases keccak <;>
        try (obtain ⟨hv, hk⟩ := hfull rfl; contradiction)
      all_goals decide +kernel
    exact he.rip.trans hfinish
  · have hext := single_store_external (by decide : 8 ≤ 128) hpre.1.2.mem he
    change t.external = memStore s.external
      (storeAddrAt (Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64))
        (finalMode v) (3 + (finalMode v).tail.length) s)
      ((Operand.mem (storeAddrAt (Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64)) (finalMode v)
        (3 + (finalMode v).tail.length) s) : Operand 8).read s ^^^ 0x80) at hext
    rw [storeAddrAt, haddr] at hext
    rw [hext]
    exact xor_padding_final hb (by decide) hratepos (by omega)

theorem output_advance [Bindings] {boundary : ReturnBoundary} {v : Variant} {reset : Bool}
    {keccak fullState : Bool}
    {sp ptr : BitVec 64} {s : RamState} (h : Context boundary sp ptr s)
    (hip : s.RIP = Finalize.entryAddress v reset keccak fullState + (36 : BitVec 64))
    (hfull : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    ∃ t, Advances boundary 1 s t ∧ Context boundary sp ptr t ∧
      t.RIP = Finalize.entryAddress v reset keccak fullState + (39 : BitVec 64) ∧
      AgreesExcept (clobbers ptr) s t ∧ t.external = s.external ∧
      (Operand.reg 14 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s := by
  obtain ⟨t, ht, hc, he, ha⟩ := step_advance h
    (mov_r64_r64_effect_step (Finalize.entryAddress v reset keccak fullState + (36 : BitVec 64)) 0x49 0xf6
      (by unfold RexWPrefix; decide) (by decide)) (memory_image v reset keccak fullState hfull).2.1
    (fun _ he ↦ he.agrees.mono (by simp (config := { decide := true }) [clobbers])) hip
  exact ⟨t, ht, hc, by simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
    BitVec.ofNat_eq_ofNat] using he.rip, ha, he.agrees.external (by simp [Component.Covers]),
    he.writes⟩

theorem steps [Bindings] {boundary : ReturnBoundary} {v : Variant} {reset : Bool}
    {keccak fullState : Bool}
    {sp ptr : BitVec 64}
    {s : RamState} {bytes : Nat → UInt8} (h : Context boundary sp ptr s) (r : Fin 200)
    (hr : (Operand.mem (ptr + (200 : BitVec 64)) : Operand 8).read s = BitVec.ofNat 8 r.val)
    (hip : s.RIP = Finalize.entryAddress v reset keccak fullState + (7 : BitVec 64))
    (hb : Bytes s.external ptr 200 bytes)
    (hfull : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    ∃ t, Advances boundary 8 s t ∧ Context boundary sp ptr t ∧ t.RIP = finish v reset keccak fullState ∧
      AgreesExcept (clobbers ptr) s t ∧
      (Operand.reg 14 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s ∧
      Bytes t.external ptr 200 (fun i ↦
        (bytes i ^^^ (if i = r.val then Variant.suffix keccak else 0)) ^^^
          (if i + 1 = rate v then 0x80 else 0)) := by
  obtain ⟨t1, hs1, hc1, hi1, ha1, hm1, hax1, hdx1⟩ := scalar_steps h r hr hip hfull
  have hb1 : Bytes t1.external ptr 200 bytes := hm1 ▸ hb
  obtain ⟨t2, hs2, hc2, hi2, ha2, hb2⟩ := lane_advance hc1 r hi1 hax1 hdx1 hb1 hfull
  obtain ⟨t3, hs3, hc3, hi3, ha3, hm3, ho3⟩ := output_advance hc2 hi2 hfull
  have hb3 := hm3.symm ▸ hb2
  obtain ⟨t4, hs4, hc4, hi4, ha4, ho4, hb4⟩ := final_advance hc3 hi3 hb3 hfull
  refine ⟨t4, (hs1.trans hs2).trans (hs3.trans hs4), hc4, hi4,
    clobbers_trans ha1 (clobbers_trans ha2 (clobbers_trans ha3 ha4)), ?_, hb4⟩
  have hfirst := (clobbers_trans ha1 ha2).read (n := 64) (r := 6)
    (by simp (config := { decide := true }) [clobbers])
  exact ho4.trans (ho3.trans hfirst)

end Sha3.Proofs.Finalize.Padding
