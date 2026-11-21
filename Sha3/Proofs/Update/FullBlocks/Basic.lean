import Sha3.Proofs.Run
import Sha3.Proofs.Image
import Sha3.Proofs.Memory
import Sha3.Proofs.Variant
import Sha3.Proofs.LaneMemory
import Sha3.Proofs.Permutation.LoadStore.Rmw
import X86Proofs.Program.Compose
namespace Sha3.Proofs.Update.FullBlocks

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program
open Keccak Permutation

def start : Variant → BitVec 64
  | .sha224 => 0x1009c0 | .sha256 => 0x1006b0
  | .sha384 => 0x1003d0 | .sha512 => 0x100120

def inputMode (i : Nat) : AddrMode :=
  .base 14 (if i = 0 then .none else if i < 16 then .d8 (.ofNat 8 (8 * i)) else .d32 (.ofNat 32 (8 * i)))

def stateMode (i : Nat) : AddrMode :=
  .base 15 (if i = 0 then .none else if i < 16 then .d8 (.ofNat 8 (8 * i))
    else .d32 (.ofNat 32 (8 * i)))

def pairOffset (i : Nat) : Nat := 8 * i - 2 + 6 * (i - 16)

def loadPC (v : Variant) (i : Nat) : BitVec 64 := start v + .ofNat 64 (pairOffset i)

def xorPC (v : Variant) (i : Nat) : BitVec 64 :=
  loadPC v i + .ofNat 64 (3 + (inputMode i).tail.length)

def loadBytes (i : Nat) : List UInt8 :=
  0x49 :: 0x8b :: (inputMode i).modrm 0 :: (inputMode i).tail

def xorBytes (i : Nat) : List UInt8 :=
  0x49 :: 0x31 :: (stateMode i).modrm 0 :: (stateMode i).tail

theorem laneBound (v : Variant) : v.lanes ≤ 18 := by cases v <;> decide

theorem inputMode_spec (i : Fin 18) :
    (inputMode i).Valid ∧ (inputMode i).rexX = 0 ∧ (inputMode i).rexB = 1 ∧
    ∀ s next, (inputMode i).addr s next =
      (Operand.reg 14 : Operand 64).read s + .ofNat 64 (8 * i.val) := by
  finite_cases i <;> simp (config := { decide := true }) [inputMode, AddrMode.addr, AddrMode.reg64, Disp.value]

theorem stateMode_spec (i : Fin 18) :
    (stateMode i).Valid ∧ (stateMode i).rexX = 0 ∧ (stateMode i).rexB = 1 ∧
    ∀ s next, (stateMode i).addr s next =
      (Operand.reg 15 : Operand 64).read s + .ofNat 64 (8 * i.val) := by
  finite_cases i <;> simp (config := { decide := true }) [stateMode, AddrMode.addr, AddrMode.reg64, Disp.value]

theorem pair_next (v : Variant) (i : Fin 18) :
    xorPC v i + .ofNat 64 (3 + (stateMode i).tail.length) = loadPC v (i + 1) := by
  cases v <;> revert i <;> decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem pair_image (v : Variant) (i : Fin 18) (hi : i.val < v.lanes) :
    (∀ byte ∈ codeRange (loadPC v i) (loadBytes i),
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2) ∧
    (∀ byte ∈ codeRange (xorPC v i) (xorBytes i),
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2) := by
  revert i
  cases v <;> decide +kernel

theorem pair_inProgram (v : Variant) (i : Fin 18) (hi : i.val < v.lanes) :
    InProgram (xorPC v i) ∧ InProgram (loadPC v (i.val + 1)) := by
  constructor
  · refine ⟨0x49, ?_⟩
    apply imageSections_mem_toCodeMap_of_fetchByte
    revert i
    cases v <;> decide +kernel
  · refine ⟨if i.val + 1 < v.lanes then 0x49 else 0x48, ?_⟩
    apply imageSections_mem_toCodeMap_of_fetchByte
    revert i
    cases v <;> decide +kernel

def clobbers (pointer : BitVec 64) : List Component :=
  [.reg 0, .flags, .rip, .mem pointer 200]

structure Context [Bindings] (boundary : ReturnBoundary) (v : Variant)
    (sp state input : BitVec 64) (s : RamState) : Prop where
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  stack : (Operand.reg 4 : Operand 64).read s = sp
  hasher : (Operand.reg 15 : Operand 64).read s = state
  source : (Operand.reg 14 : Operand 64).read s = input
  inputRead : MemReadable s input (8 * v.lanes)
  stateRead : MemReadable s state 200
  apart : RangeApart state 200 input (8 * v.lanes)
  avoids : ∀ i < 200, ¬ (InProgram (state + .ofNat 64 i) ∨
    InPageTables (state + .ofNat 64 i))
  boundary : ¬ InProgram boundary.rip

theorem Context.of_frame [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {sp state input : BitVec 64} {s t : RamState} (h : Context boundary v sp state input s)
    (ha : AgreesExcept (clobbers state) s t) (hr : ReadyToStep t) :
    Context boundary v sp state input t := by
  refine ⟨hr, ?_, (ha.read (by simp [clobbers])).trans h.stack,
    (ha.read (by simp [clobbers])).trans h.hasher,
    (ha.read (by simp [clobbers])).trans h.source,
    ⟨h.inputRead.low, fun i hi ↦ ha.grow _ (h.inputRead.mem i hi)⟩,
    ⟨h.stateRead.low, fun i hi ↦ ha.grow _ (h.stateRead.mem i hi)⟩,
    h.apart, h.avoids, h.boundary⟩
  intro address byte hbyte
  rw [ha.byte]
  · exact h.loaded address byte hbyte
  · intro c hc hcover
    simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact hcover
    · exact hcover
    · exact hcover
    · obtain ⟨i, hi, rfl⟩ := hcover
      exact h.avoids i hi (.inl ⟨byte, hbyte⟩)

theorem clobbers_trans {pointer : BitVec 64} {s t u : RamState}
    (h : AgreesExcept (clobbers pointer) s t) (h' : AgreesExcept (clobbers pointer) t u) :
    AgreesExcept (clobbers pointer) s u :=
  (h.trans h').mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)

theorem load_effect [Bindings] (v : Variant) (i : Fin 18) :
    StepEffect (LoadPre (loadPC v i)
      (fun s ↦ (Operand.reg 14 : Operand 64).read s + .ofNat 64 (8 * i.val)) 8)
      (codeRange (loadPC v i) (loadBytes i))
      (movR64M64Effect (loadPC v i) 0 (inputMode i)) := by
  have h := mov_r64_m64_effect_step (loadPC v i) 0x49
    (by unfold RexWPrefix; decide +kernel) 0 (inputMode i) (inputMode_spec i).1
    (inputMode_spec i).2.1.symm (inputMode_spec i).2.2.1.symm
  simpa only [loadBytes, (inputMode_spec i).2.2.2,
    show gprNumber 0 (rexR (0x49 : UInt8).toBitVec) 0 = 0 by decide +kernel] using h

theorem xor_effect [Bindings] (v : Variant) (i : Fin 18) :
    StepEffect (StorePreReadable (xorPC v i)
      (fun s ↦ (Operand.reg 15 : Operand 64).read s + .ofNat 64 (8 * i.val)) 8)
      (codeRange (xorPC v i) (xorBytes i))
      (xorMREffect (xorPC v i) (3 + (stateMode i).tail.length) 64 0 (stateMode i)) := by
  have h := xor_m64_r64_effect_step_of_readable (xorPC v i) 0x49
    (by unfold RexWPrefix; decide +kernel) 0 (stateMode i) (stateMode_spec i).1
    (stateMode_spec i).2.1.symm (stateMode_spec i).2.2.1.symm
  simpa only [xorBytes, (stateMode_spec i).2.2.2,
    show gprNumber 0 (rexR (0x49 : UInt8).toBitVec) 0 = 0 by decide +kernel] using h

set_option maxHeartbeats 400000 in
theorem pair_advance [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {sp state input : BitVec 64} {s : RamState} (h : Context boundary v sp state input s)
    (i : Fin 18) (hi : i.val < v.lanes) (hip : s.RIP = loadPC v i) :
    ∃ t, Advances boundary 2 s t ∧ Context boundary v sp state input t ∧
      t.RIP = loadPC v (i.val + 1) ∧ AgreesExcept (clobbers state) s t ∧
      memoryLanes state t = setLane (memoryLanes state s) ⟨i.val, by omega⟩
        (memoryLanes state s ⟨i.val, by omega⟩ ^^^
          memLoad s.external (input + .ofNat 64 (8 * i.val)) 64) := by
  have loadCode : CodeIn (codeRange (loadPC v i) (loadBytes i)) s := by
    intro byte hb
    obtain ⟨hlow, hfetch⟩ := (pair_image v i hi).1 byte hb
    exact ⟨hlow, programLoaded_fetchByte h.loaded hfetch⟩
  have loadPre : LoadPre (loadPC v i)
      (fun s ↦ (Operand.reg 14 : Operand 64).read s + .ofNat 64 (8 * i.val)) 8 s := by
    refine ⟨hip, ?_⟩
    rw [h.source]
    exact readable_slice h.inputRead (8 * i.val) 8 (by omega)
  obtain ⟨u, step1, ready1, effect1⟩ := load_effect v i s h.ready loadCode loadPre
  have frame1 : AgreesExcept (clobbers state) s u :=
    effect1.agrees.mono (by simp [clobbers, movR64M64Effect_components])
  have context1 := h.of_frame frame1 ready1
  have ext1 : u.external = s.external := effect1.agrees.external (by
    simp [movR64M64Effect_components, Component.Covers])
  have rax1 : (Operand.reg 0 : Operand 64).read u =
      memLoad s.external (input + .ofNat 64 (8 * i.val)) 64 := by
    have hw := effect1.writes
    change (Operand.reg 0 : Operand 64).read u =
      memLoad s.external ((inputMode i).addr s
        (loadPC v i + .ofNat 64 (3 + (inputMode i).tail.length))) 64 at hw
    rw [(inputMode_spec i).2.2.2, h.source] at hw
    exact hw
  have xorCode : CodeIn (codeRange (xorPC v i) (xorBytes i)) u := by
    intro byte hb
    obtain ⟨hlow, hfetch⟩ := (pair_image v i hi).2 byte hb
    exact ⟨hlow, programLoaded_fetchByte context1.loaded hfetch⟩
  have xorPre : StorePreReadable (xorPC v i)
      (fun s ↦ (Operand.reg 15 : Operand 64).read s + .ofNat 64 (8 * i.val)) 8 u := by
    refine ⟨⟨effect1.rip, ?_⟩, ?_⟩
    · rw [context1.hasher]
      exact readable_slice context1.stateRead (8 * i.val) 8 (by omega)
    · intro j hj
      dsimp only
      rw [context1.hasher, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact fun ht ↦ h.avoids (8 * i.val + j) (by omega) (.inr ht)
  obtain ⟨t, step2, ready2, effect2⟩ := xor_effect v i u ready1 xorCode xorPre
  have address : (stateMode i).addr u
      (xorPC v i + .ofNat 64 (3 + (stateMode i).tail.length)) =
      state + .ofNat 64 (8 * i.val) := by
    rw [(stateMode_spec i).2.2.2, context1.hasher]
  have frame2 : AgreesExcept (clobbers state) u t := by
    apply effect2.agrees.widen
    · intro c hc hm
      simp only [xorMREffect_components, address, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | rfl | rfl
      · contradiction
      · simp [clobbers]
      · simp [clobbers]
    · intro x c hc hcover
      simp only [xorMREffect_components, address, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcover
        refine ⟨.mem state 200, by simp [clobbers], 8 * i.val + j, by omega, ?_⟩
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      · exact hcover.elim
      · exact hcover.elim
  have context2 := context1.of_frame frame2 ready2
  have advance1 : Advances boundary 1 s u := Advances.of_step step1
    (.inl (by
      intro he
      have hp : InProgram u.RIP := effect1.rip ▸ (pair_inProgram v i hi).1
      exact h.boundary (he ▸ hp)))
  have advance2 : Advances boundary 1 u t := Advances.of_step step2
    (.inl (by
      intro he
      have hp : InProgram t.RIP :=
        (effect2.rip.trans (pair_next v i)) ▸ (pair_inProgram v i hi).2
      exact h.boundary (he ▸ hp)))
  refine ⟨t, advance1.trans advance2, context2,
    effect2.rip.trans (pair_next v i), clobbers_trans frame1 frame2, ?_⟩
  have obs := effect2.obs (Obs.refl u) (by
    simp [xorMREffect, Write.Full, Operand.Full])
  rw [← LaneMemory.memoryLanes_eq_of_memByte_eq state obs.mem]
  simp only [xorMREffect, address, applyWrites_cons, applyWrites_nil, Write.apply_mk]
  rw [LaneMemory.memoryLanes_write_lane (lane := ⟨i.val, by omega⟩), rax1]
  have hlanes : memoryLanes state u = memoryLanes state s := by
    unfold memoryLanes
    simp only [Operand.read, ext1]
  rw [hlanes]
  simp only [memoryLanes, Operand.read, ext1]

theorem input_load_frame [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {sp state input : BitVec 64} {s t : RamState} (h : Context boundary v sp state input s)
    (ha : AgreesExcept (clobbers state) s t) (i : Nat) (hi : i < v.lanes) :
    memLoad t.external (input + .ofNat 64 (8 * i)) 64 =
      memLoad s.external (input + .ofNat 64 (8 * i)) 64 := by
  apply memLoad_congr
  intro j hj
  apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
  apply ha.byte
  intro c hc hcover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact hcover
  · exact hcover
  · exact hcover
  · obtain ⟨k, hk, he⟩ := hcover
    apply h.apart k hk (8 * i + j) (by omega)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using he.symm

def xorPrefix (a : Lanes) (s : RamState) (input : BitVec 64) (count : Nat) : Lanes :=
  fun lane ↦ a lane ^^^ (if lane.val < count then
    memLoad s.external (input + .ofNat 64 (8 * lane.val)) 64 else 0)

theorem xorPrefix_zero (a : Lanes) (s : RamState) (input : BitVec 64) :
    xorPrefix a s input 0 = a := by
  funext lane
  simp [xorPrefix]

theorem xorPrefix_succ (a : Lanes) (s : RamState) (input : BitVec 64) (i : Fin 25) :
    setLane (xorPrefix a s input i.val) i
      (xorPrefix a s input i.val i ^^^
        memLoad s.external (input + .ofNat 64 (8 * i.val)) 64) =
      xorPrefix a s input (i.val + 1) := by
  funext lane
  by_cases he : lane = i
  · subst lane
    simp [setLane, xorPrefix]
  · have hv : lane.val ≠ i.val := fun hv ↦ he (Fin.ext hv)
    have hl : lane.val < i.val + 1 ↔ lane.val < i.val := by omega
    simp only [setLane, he, ↓reduceIte, xorPrefix, hl]

theorem prefix_advance [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {sp state input : BitVec 64} {s : RamState} (h : Context boundary v sp state input s)
    (hip : s.RIP = start v) (n : Nat) (hn : n ≤ v.lanes) :
    ∃ t, Advances boundary (2 * n) s t ∧ Context boundary v sp state input t ∧
      t.RIP = loadPC v n ∧ AgreesExcept (clobbers state) s t ∧
      memoryLanes state t = xorPrefix (memoryLanes state s) s input n := by
  induction n with
  | zero =>
    refine ⟨s, (advances_zero boundary s s).mpr rfl, h, ?_, .refl _ _, ?_⟩
    · simpa [loadPC, pairOffset] using hip
    · exact (xorPrefix_zero _ _ _).symm
  | succ n ih =>
    obtain ⟨u, hu, cu, ipu, fu, lu⟩ := ih (by omega)
    have hn18 : n < 18 := Nat.lt_of_lt_of_le (by omega) (laneBound v)
    obtain ⟨t, ht, ct, ipt, ft, lt⟩ := pair_advance cu ⟨n, hn18⟩ (by change n < v.lanes; omega) ipu
    refine ⟨t, ?_, ct, ipt, clobbers_trans fu ft, ?_⟩
    · simpa only [Nat.mul_succ] using hu.trans ht
    · rw [lt, lu, input_load_frame h fu n (by omega)]
      exact xorPrefix_succ _ _ _ ⟨n, by omega⟩

theorem blockLanes_outside (bytes : ByteArray) (offset rate : Nat) (lane : Fin 25)
    (h : rate ≤ 8 * lane.val) : Absorption.blockLanes bytes offset rate lane = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [Absorption.blockLanes, getLsbD_packLane _ ⟨z, hz⟩]
  have hj : ¬ (8 * lane.val + z / 8 < rate ∧ offset + (8 * lane.val + z / 8) < bytes.size) := by
    omega
  simp [hj]

theorem body_advance [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {sp state input : BitVec 64} {s : RamState} (h : Context boundary v sp state input s)
    (hip : s.RIP = start v) :
    ∃ t, Advances boundary (2 * v.lanes) s t ∧ Context boundary v sp state input t ∧
      t.RIP = loadPC v v.lanes ∧ AgreesExcept (clobbers state) s t ∧
      memoryLanes state t = xorPrefix (memoryLanes state s) s input v.lanes :=
  prefix_advance h hip v.lanes (Nat.le_refl _)

theorem body_advance_bytes [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {sp state pointer : BitVec 64} {s : RamState} {bytes : ByteArray} {offset : Nat}
    (h : Context boundary v sp state (pointer + .ofNat 64 offset) s)
    (hip : s.RIP = start v) (hbytes : BytesAt s pointer bytes.data.toList)
    (hsize : offset + 8 * v.lanes ≤ bytes.size) :
    ∃ t, Advances boundary (2 * v.lanes) s t ∧
      Context boundary v sp state (pointer + .ofNat 64 offset) t ∧
      t.RIP = loadPC v v.lanes ∧ AgreesExcept (clobbers state) s t ∧
      memoryLanes state t = fun lane ↦ memoryLanes state s lane ^^^
        Absorption.blockLanes bytes offset (8 * v.lanes) lane := by
  obtain ⟨t, ht, ct, ipt, ft, lt⟩ := body_advance h hip
  refine ⟨t, ht, ct, ipt, ft, lt.trans ?_⟩
  funext lane
  simp only [xorPrefix]
  by_cases hi : lane.val < v.lanes
  · simp only [hi, ↓reduceIte, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [LaneMemory.memLoad_blockLanes_of_bytesAt hbytes offset (8 * v.lanes) lane
      (by omega) (by omega)]
  · rw [blockLanes_outside bytes offset (8 * v.lanes) lane (by omega)]
    simp only [hi, ↓reduceIte]

end Sha3.Proofs.Update.FullBlocks
