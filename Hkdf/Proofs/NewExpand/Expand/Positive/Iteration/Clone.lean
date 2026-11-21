import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.EffectCompose
import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.ContextClone

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def destination (s : RamState) : BitVec 64 := rspOf s + 272

def components (s : RamState) : List Component :=
  [.reg 1, .reg 2, .reg 6, .reg 7, .mem (destination s) 144, .rip]

private def reg (r : BitVec 5) (s : RamState) := (Operand.reg r : Operand 64).read s

private theorem register_number (r : BitVec 3) :
    gprNumber 0 (rexR (0x48 : UInt8).toBitVec) r = r.setWidth 5 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth]
  change (0 + r.toNat) % 32 = r.toNat % 32
  rw [Nat.zero_add]

private def update (regs : BitVec 5 → BitVec 64) (r : BitVec 5) (v : BitVec 64) :
    BitVec 5 → BitVec 64 := fun i => if i = r then v else regs i

private theorem same_offsets (base : BitVec 64) (i j : Nat) :
    base + BitVec.ofNat 64 i + BitVec.ofNat 64 j = base + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem agrees_outside {s t : RamState} {a : BitVec 64} {size : Nat}
    (h : AgreesExcept (components s) s t) (apart : RangeApart a size (destination s) 144) :
    (Component.mem a size).Agrees s t := by
  intro i hi
  apply h.byte
  intro c hc covers
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covers.elim
  obtain ⟨j, hj, eq⟩ := covers
  exact apart i hi j hj eq

private theorem memLoad_agrees {s t : RamState} {a : BitVec 64}
    (h : AgreesExcept (components s) s t) (apart : RangeApart a 8 (destination s) 144) :
    memLoad t.external a 64 = memLoad s.external a 64 :=
  agrees_memLoad (agrees_outside h apart)

private theorem advance_store_agreement {s t u : RamState} {word : Nat} (bound : word < 18)
    (h : AgreesExcept (components s) s t)
    (step : AgreesExcept [.mem (destination s + BitVec.ofNat 64 (8 * word)) 8, .rip] t u) :
    AgreesExcept (components s) s u := by
  refine ⟨?_, ?_, step.rest.trans h.rest, fun a ha => step.grow a (h.grow a ha)⟩
  · intro c hc hn
    apply (h.agree c hc hn).trans (step.agree c ?_ hn)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · intro eq
      subst c
      exact Bool.noConfusion hn
    · intro eq
      subst c
      exact hc (by simp [components])
  · intro a ha
    refine (step.memory a ?_).trans (h.memory a ha)
    intro c hc cov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := cov
      exact ha (.mem (destination s) 144) (by simp [components]) ⟨8 * word + i, by omega, same_offsets _ _ _⟩
    · exact cov

private theorem advance_register_agreement {s t u : RamState} {r : BitVec 5}
    (h : AgreesExcept (components s) s t) (member : Component.reg r ∈ components s)
    (step : AgreesExcept [.reg r, .rip] t u) :
    AgreesExcept (components s) s u := by
  refine ⟨?_, fun a ha => (step.memory a ?_).trans (h.memory a ha),
    step.rest.trans h.rest, fun a ha => step.grow a (h.grow a ha)⟩
  · intro c hc hn
    apply (h.agree c hc hn).trans (step.agree c ?_ hn)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun eq => hc (eq ▸ member), fun eq => hc (eq ▸ by simp [components])⟩
  · intro c hc cov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact cov

def bytes : List UInt8 :=
  [0x48,0x8b,0xbc,0x24,0xa0,0x01,0x00,0x00,0x48,0x8b,0x4f,0x20,0x48,0x8d,0xb4,0x24,
   0x50,0x01,0x00,0x00,0x48,0x89,0x4e,0x48,0x48,0x8b,0x4f,0x18,0x48,0x89,0x4e,0x40,
   0x48,0x8b,0x4f,0x10,0x48,0x89,0x4e,0x38,0x48,0x8b,0x0f,0x48,0x8b,0x57,0x08,0x48,
   0x89,0x56,0x30,0x48,0x89,0x4e,0x28,0x48,0x8b,0x94,0x24,0xa8,0x01,0x00,0x00,0x48,
   0x8b,0x4a,0x20,0x48,0x89,0x4e,0x20,0x48,0x8b,0x4a,0x18,0x48,0x89,0x4e,0x18,0x48,
   0x8b,0x4a,0x10,0x48,0x89,0x4e,0x10,0x48,0x8b,0x0a,0x48,0x8b,0x52,0x08,0x48,0x89,
   0x56,0x08,0x48,0x89,0x0e,0x48,0x8b,0x94,0x24,0xf0,0x00,0x00,0x00,0x48,0x8b,0x4a,
   0x38,0x48,0x89,0x8c,0x24,0x48,0x01,0x00,0x00,0x48,0x8b,0x4a,0x30,0x48,0x89,0x8c,
   0x24,0x40,0x01,0x00,0x00,0x48,0x8b,0x4a,0x28,0x48,0x89,0x8c,0x24,0x38,0x01,0x00,
   0x00,0x48,0x8b,0x4a,0x20,0x48,0x89,0x8c,0x24,0x30,0x01,0x00,0x00,0x48,0x8b,0x4a,
   0x18,0x48,0x89,0x8c,0x24,0x28,0x01,0x00,0x00,0x48,0x8b,0x4a,0x10,0x48,0x89,0x8c,
   0x24,0x20,0x01,0x00,0x00,0x48,0x8b,0x0a,0x48,0x8b,0x52,0x08,0x48,0x89,0x94,0x24,
   0x18,0x01,0x00,0x00,0x48,0x89,0x8c,0x24,0x10,0x01,0x00,0x00]

theorem bytes_length : bytes.length = 204 := by decide +kernel

private abbrev start : BitVec 64 := 0x10f5a0
private abbrev code : CodeMap := codeRange start bytes

structure Pre (s : RamState) (src : BitVec 64) : Prop where
  rip : s.RIP = start
  source : MemReadable s src 144
  sourceApart : RangeApart src 144 (destination s) 144
  stackRead : ∀ offset ∈ ([416, 424, 240] : List (BitVec 64)),
    MemReadable s (rspOf s + offset) 8
  contextPtr : slot s 240 = src
  innerPtr : slot s 424 = src + 64
  outerPtr : slot s 416 = src + 104
  writable : ∀ word < 18, MemWritable s (destination s + BitVec.ofNat 64 (8 * word)) 8
  codeApart : ∀ word < 18, RangeApart (destination s + BitVec.ofNat 64 (8 * word)) 8
    start bytes.length

private structure Prefix [Bindings] (boundary : ReturnBoundary) (s t : RamState)
    (src : BitVec 64) (pc : BitVec 64) (fuel : Nat) (regs : BitVec 5 → BitVec 64)
    (copiedFrom : Nat) : Prop where
  run : Advances boundary fuel s t
  ready : ReadyToStep t
  rip : t.RIP = pc
  codeIn : CodeIn code t
  agrees : AgreesExcept (components s) s t
  registers : ∀ r, reg r t = regs r
  words : ∀ word, copiedFrom ≤ word → word < 18 → ∀ i < 8,
    t.external[destination s + BitVec.ofNat 64 (8 * word) + BitVec.ofNat 64 i]? =
      s.external[src + BitVec.ofNat 64 (8 * word) + BitVec.ofNat 64 i]?

private theorem Prefix.registerStep [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {src pc next : BitVec 64} {fuel : Nat} {regs : BitVec 5 → BitVec 64}
    {copiedFrom : Nat} {r : BitVec 5} {v : BitVec 64} {P : RamState → Prop}
    {insn : CodeMap} {E : RamState → Effect}
    (prefixState : Prefix boundary s t src pc fuel regs copiedFrom)
    (step : StepEffect P insn E) (subset : ∀ x ∈ insn, x ∈ code) (pre : P t)
    (rip : (E t).rip = next) (continues : next ≠ boundary.rip)
    (writes : (E t).writes = [⟨(.reg r : Operand 64), v⟩])
    (noFlags : (E t).flags = none) (member : Component.reg r ∈ components s) :
    ∃ u, Prefix boundary s u src next (fuel + 1) (update regs r v) copiedFrom := by
  obtain ⟨u, run, ready, effect⟩ := step.advances prefixState.ready (prefixState.codeIn.mono subset)
    pre (rip ▸ continues)
  have agreement : AgreesExcept [.reg r, .rip] t u := by
    simpa only [Effect.components, writes, noFlags, List.map_cons, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component] using effect.agrees
  refine ⟨u, prefixState.run.trans run, ready, effect.rip.trans rip,
    agreement.codeIn (by simp [Component.Covers]) prefixState.codeIn,
    advance_register_agreement prefixState.agrees member agreement, ?_, ?_⟩
  · intro i
    by_cases eq : i = r
    · subst i
      have h := effect.writes
      rw [writes] at h
      exact (show reg r u = v from h).trans (by simp [update])
    · exact (agreement.read (by simp [eq])).trans
        ((prefixState.registers i).trans (by simp [update, eq]))
  · intro word low high i hi
    rw [agreement.byte (by simp [Component.Covers])]
    exact prefixState.words word low high i hi

private theorem Prefix.load [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {src pc next addr : BitVec 64} {fuel : Nat} {regs : BitVec 5 → BitVec 64} {copiedFrom : Nat}
    {dst : BitVec 3} {am : AddrMode}
    (prefixState : Prefix boundary s t src pc fuel regs copiedFrom)
    (valid : am.Valid) (rexXeq : rexX (0x48 : UInt8).toBitVec = am.rexX)
    (rexBeq : rexB (0x48 : UInt8).toBitVec = am.rexB)
    (subset : ∀ x ∈ codeRange pc (0x48 :: 0x8b :: am.modrm dst :: am.tail), x ∈ code)
    (rip : pc + BitVec.ofNat 64 (movLoadLen am) = next) (continues : next ≠ boundary.rip)
    (address : am.addr t next = addr) (read : MemReadable s addr 8)
    (apart : RangeApart addr 8 (destination s) 144)
    (member : Component.reg (dst.setWidth 5) ∈ components s) :
    ∃ u, Prefix boundary s u src next (fuel + 1)
      (update regs (dst.setWidth 5) (memLoad s.external addr 64)) copiedFrom := by
  apply prefixState.registerStep
    (mov_r64_m64_effect_step pc 0x48 (by simp [RexWPrefix]) dst am valid rexXeq rexBeq) subset
  · refine ⟨prefixState.rip, ?_⟩
    rw [rip, address]
    exact ⟨read.low, fun i hi => prefixState.agrees.grow _ (read.mem i hi)⟩
  · exact rip
  · exact continues
  · simp only [movR64M64Effect, rip, address, Operand.read, memLoad_agrees prefixState.agrees apart,
      register_number]
  · rfl
  · simpa only [register_number] using member

private theorem Prefix.store [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {src pc next : BitVec 64} {fuel word offset : Nat}
    {regs : BitVec 5 → BitVec 64} {copiedFrom : Nat} {r : BitVec 3} {am : AddrMode}
    (prefixState : Prefix boundary s t src pc fuel regs copiedFrom) (pre : Pre s src)
    (valid : am.Valid) (rexXeq : rexX (0x48 : UInt8).toBitVec = am.rexX)
    (rexBeq : rexB (0x48 : UInt8).toBitVec = am.rexB)
    (subset : ∀ x ∈ codeRange pc (0x48 :: 0x89 :: am.modrm r :: am.tail), x ∈ code)
    (displacement : pc = start + BitVec.ofNat 64 offset)
    (fits : offset + (3 + am.tail.length) ≤ bytes.length)
    (rip : pc + BitVec.ofNat 64 (3 + am.tail.length) = next) (continues : next ≠ boundary.rip)
    (address : am.addr t next = destination s + BitVec.ofNat 64 (8 * word))
    (bound : word < 18) (previous : word + 1 = copiedFrom)
    (value : regs (r.setWidth 5) = memLoad s.external (src + BitVec.ofNat 64 (8 * word)) 64) :
    ∃ u, Prefix boundary s u src next (fuel + 1) regs word := by
  let addr := destination s + BitVec.ofNat 64 (8 * word)
  have actual : storeAddrAt pc am (3 + am.tail.length) t = addr := by
    simp only [storeAddrAt, rip, address, addr]
  have bytesApart := pre.codeApart word bound
  have writable := pre.writable word bound
  obtain ⟨u, run, ready, effect⟩ := (mov_m64_r64_effect_step pc 0x48 (by simp [RexWPrefix]) r am
    valid rexXeq rexBeq).advances prefixState.ready (prefixState.codeIn.mono subset)
    (by
      refine ⟨prefixState.rip, ?_, ?_⟩
      · rw [actual]
        exact ⟨writable.low, fun i hi => prefixState.agrees.grow _ (writable.mem i hi), writable.tables⟩
      · rw [actual, displacement]
        exact bytesApart.sub offset (3 + am.tail.length) fits)
    (rip ▸ continues)
  have agreement : AgreesExcept [.mem addr 8, .rip] t u := by
    simpa only [movM64R64Effect_components, actual] using effect.agrees
  have codeIn : CodeIn code u := effect.codeIn
    (Effect.avoids_of_components_mem_rip (by rw [movM64R64Effect_components, actual]) bytesApart)
    prefixState.codeIn
  refine ⟨u, prefixState.run.trans run, ready, effect.rip.trans rip, codeIn,
    advance_store_agreement bound prefixState.agrees agreement, ?_, ?_⟩
  · intro i
    exact (agreement.read (by simp)).trans (prefixState.registers i)
  · intro w low high i hi
    by_cases eq : w = word
    · subst w
      have val : reg (gprNumber 0 (rexR (0x48 : UInt8).toBitVec) r) t =
          memLoad s.external (src + BitVec.ofNat 64 (8 * word)) 64 := by
        rw [register_number, prefixState.registers, value]
      have same := effect.writes
      change memLoad u.external (storeAddrAt pc am (3 + am.tail.length) t) 64 =
        reg (gprNumber 0 (rexR (0x48 : UInt8).toBitVec) r) t at same
      rw [actual, val] at same
      have out := Bytes.of_memLoad (m := u.external) (a := addr) (n := 64) (fun j hj => agreement.grow _ (prefixState.agrees.grow _ (writable.mem j hj)))
      have input := Bytes.of_memLoad (m := s.external) (n := 64) (a := src + BitVec.ofNat 64 (8 * word))
        (fun j hj => by
          rw [same_offsets]
          exact pre.source.mem (8 * word + j) (by omega))
      have h := out i hi
      rw [same] at h
      exact h.trans (input i hi).symm
    · have apart : RangeApart (destination s + BitVec.ofNat 64 (8 * w)) 8 addr 8 :=
        RangeApart.offsets _ (by omega) (by omega) (by omega)
      rw [agreement.byte (by
        intro c hc cover
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · obtain ⟨j, hj, yes⟩ := cover
          exact apart i hi j hj yes
        · exact cover)]
      exact prefixState.words w (by omega) high i hi

private theorem source_readable_word {s : RamState} {src : BitVec 64} {word : Nat}
    (source : MemReadable s src 144) (bound : word < 18) :
    MemReadable s (src + BitVec.ofNat 64 (8 * word)) 8 := by
  refine ⟨?_, ?_⟩
  · rw [toNat_add_ofNat _ _ (by have := source.low; omega)]
    have := source.low
    omega
  · intro i hi
    rw [same_offsets]
    exact source.mem _ (by omega)

private theorem Prefix.loadSource [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {src pc next : BitVec 64} {fuel word : Nat} {regs : BitVec 5 → BitVec 64}
    {copiedFrom : Nat} {dst : BitVec 3} {am : AddrMode}
    (prefixState : Prefix boundary s t src pc fuel regs copiedFrom) (pre : Pre s src)
    (valid : am.Valid) (rexXeq : rexX (0x48 : UInt8).toBitVec = am.rexX)
    (rexBeq : rexB (0x48 : UInt8).toBitVec = am.rexB)
    (subset : ∀ x ∈ codeRange pc (0x48 :: 0x8b :: am.modrm dst :: am.tail), x ∈ code)
    (rip : pc + BitVec.ofNat 64 (movLoadLen am) = next) (continues : next ≠ boundary.rip)
    (address : am.addr t next = src + BitVec.ofNat 64 (8 * word)) (bound : word < 18)
    (member : Component.reg (dst.setWidth 5) ∈ components s) :
    ∃ u, Prefix boundary s u src next (fuel + 1)
      (update regs (dst.setWidth 5) (memLoad s.external (src + BitVec.ofNat 64 (8 * word)) 64))
      copiedFrom := by
  apply prefixState.load valid rexXeq rexBeq subset rip continues address
    (source_readable_word pre.source bound) ?_ member
  intro i hi j hj
  rw [same_offsets]
  exact pre.sourceApart (8 * word + i) (by omega) j hj

private theorem Prefix.loadStack [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {src pc next v : BitVec 64} {fuel offset : Nat} {regs : BitVec 5 → BitVec 64}
    {copiedFrom : Nat} {dst : BitVec 3} {am : AddrMode}
    (prefixState : Prefix boundary s t src pc fuel regs copiedFrom) (pre : Pre s src)
    (valid : am.Valid) (rexXeq : rexX (0x48 : UInt8).toBitVec = am.rexX)
    (rexBeq : rexB (0x48 : UInt8).toBitVec = am.rexB)
    (subset : ∀ x ∈ codeRange pc (0x48 :: 0x8b :: am.modrm dst :: am.tail), x ∈ code)
    (rip : pc + BitVec.ofNat 64 (movLoadLen am) = next) (continues : next ≠ boundary.rip)
    (address : am.addr t next = rspOf s + BitVec.ofNat 64 offset)
    (stackOffset : offset ∈ [416, 424, 240])
    (value : slot s (BitVec.ofNat 64 offset) = v)
    (member : Component.reg (dst.setWidth 5) ∈ components s) :
    ∃ u, Prefix boundary s u src next (fuel + 1) (update regs (dst.setWidth 5) v) copiedFrom := by
  change memLoad s.external (rspOf s + BitVec.ofNat 64 offset) 64 = v at value
  rw [← value]
  apply prefixState.load valid rexXeq rexBeq subset rip continues address ?_ ?_ member
  · exact pre.stackRead _ (List.mem_map_of_mem (f := BitVec.ofNat 64) stackOffset)
  · simp only [destination]
    apply RangeApart.offsets (a := offset) (b := 272) (rspOf s) ?_ (by decide) ?_
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at stackOffset
      rcases stackOffset with rfl | rfl | rfl <;> decide

private theorem Prefix.lea [Bindings] {boundary : ReturnBoundary} {s t : RamState}
    {src : BitVec 64} {fuel : Nat} {regs : BitVec 5 → BitVec 64} {copiedFrom : Nat}
    (prefixState : Prefix boundary s t src 0x10f5ac fuel regs copiedFrom)
    (continues : (0x10f5b4 : BitVec 64) ≠ boundary.rip)
    (stack : regs 4 = rspOf s) :
    ∃ u, Prefix boundary s u src 0x10f5b4 (fuel + 1)
      (update regs 6 (rspOf s + 336)) copiedFrom := by
  refine prefixState.registerStep
    (lea_r64_effect_step 0x10f5ac 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d32 336)) (by decide) rfl rfl)
    (codeRange_slice_subset start bytes 12 8) prefixState.rip rfl continues ?_ rfl
    (by simp [components])
  change ([⟨(.reg 6 : Operand 64), reg 4 t + 336⟩] : List Write) = _
  rw [prefixState.registers, stack]

local macro "clone_address " prefixState:ident " [" base:num ", " disp:num "]" : tactic => `(tactic| (
  change reg $base _ + $disp = _
  rw [Prefix.registers $prefixState]
  try simp (config := { decide := true }) only [update, ite_true, ite_false, destination,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  try rfl))

set_option maxRecDepth 2048 in
private theorem code_in {s : RamState} (loaded : ProgramLoaded s) : CodeIn code s :=
  programText_slice (programLoaded_codeIn loaded) 0xf5a0 bytes
    (by decide) (by decide +kernel)

set_option maxHeartbeats 700000 in
theorem clone_context [Bindings] {s : RamState} {boundary : ReturnBoundary} {src : BitVec 64}
    (pre : Pre s src) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 40 s t ∧ ReadyToStep t ∧ t.RIP = 0x10f66c ∧
      AgreesExcept (components s) s t ∧
      (∀ i < 144, t.external[destination s + BitVec.ofNat 64 i]? =
        s.external[src + BitVec.ofNat 64 i]?) := by
  have atStart : Prefix boundary s s src start 0 (fun r => reg r s) 18 :=
    ⟨(advances_zero boundary s s).2 rfl, ready, pre.rip, code_in loaded,
      AgreesExcept.refl _ _, fun _ => rfl, by intro word hlo hhi; omega⟩
  have continueAt (offset : Nat) (bound : offset < 115149) :
      (0x100000 : BitVec 64) + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset offset bound)
  obtain ⟨_, step1⟩ := atStart.loadStack pre (am := (.sib 4 none 0 (.d32 416))) (dst := 7)
    (offset := 416) (by decide) rfl rfl (codeRange_slice_subset start bytes 0 8)
    rfl (continueAt 0xf5a8 (by decide)) (by clone_address atStart [4, 416]) (by decide) pre.outerPtr
    (by simp [components])
  obtain ⟨_, step2⟩ := step1.loadSource pre (am := (.base 7 (.d8 32))) (dst := 1)
    (word := 17) (by decide) rfl rfl (codeRange_slice_subset start bytes 8 4)
    rfl (continueAt 0xf5ac (by decide)) (by clone_address step1 [7, 32]) (by decide) (by simp [components])
  obtain ⟨_, step3⟩ := step2.lea (continueAt 0xf5b4 (by decide)) (by rfl)
  obtain ⟨_, step4⟩ := step3.store pre (am := (.base 6 (.d8 72))) (r := 1)
    (word := 17) (offset := 20) (by decide) rfl rfl (codeRange_slice_subset start bytes 20 4)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf5b8 (by decide)) (by clone_address step3 [6, 72]) (by decide) rfl (by rfl)
  obtain ⟨_, step5⟩ := step4.loadSource pre (am := (.base 7 (.d8 24))) (dst := 1)
    (word := 16) (by decide) rfl rfl (codeRange_slice_subset start bytes 24 4)
    rfl (continueAt 0xf5bc (by decide)) (by clone_address step4 [7, 24]) (by decide) (by simp [components])
  obtain ⟨_, step6⟩ := step5.store pre (am := (.base 6 (.d8 64))) (r := 1)
    (word := 16) (offset := 28) (by decide) rfl rfl (codeRange_slice_subset start bytes 28 4)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf5c0 (by decide)) (by clone_address step5 [6, 64]) (by decide) rfl (by rfl)
  obtain ⟨_, step7⟩ := step6.loadSource pre (am := (.base 7 (.d8 16))) (dst := 1)
    (word := 15) (by decide) rfl rfl (codeRange_slice_subset start bytes 32 4)
    rfl (continueAt 0xf5c4 (by decide)) (by clone_address step6 [7, 16]) (by decide) (by simp [components])
  obtain ⟨_, step8⟩ := step7.store pre (am := (.base 6 (.d8 56))) (r := 1)
    (word := 15) (offset := 36) (by decide) rfl rfl (codeRange_slice_subset start bytes 36 4)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf5c8 (by decide)) (by clone_address step7 [6, 56]) (by decide) rfl (by rfl)
  obtain ⟨_, step9⟩ := step8.loadSource pre (am := (.base 7 .none)) (dst := 1)
    (word := 13) (by decide) rfl rfl (codeRange_slice_subset start bytes 40 3)
    rfl (continueAt 0xf5cb (by decide)) (by clone_address step8 [7, 0]) (by decide) (by simp [components])
  obtain ⟨_, step10⟩ := step9.loadSource pre (am := (.base 7 (.d8 8))) (dst := 2)
    (word := 14) (by decide) rfl rfl (codeRange_slice_subset start bytes 43 4)
    rfl (continueAt 0xf5cf (by decide)) (by clone_address step9 [7, 8]) (by decide) (by simp [components])
  obtain ⟨_, step11⟩ := step10.store pre (am := (.base 6 (.d8 48))) (r := 2)
    (word := 14) (offset := 47) (by decide) rfl rfl (codeRange_slice_subset start bytes 47 4)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf5d3 (by decide)) (by clone_address step10 [6, 48]) (by decide) rfl (by rfl)
  obtain ⟨_, step12⟩ := step11.store pre (am := (.base 6 (.d8 40))) (r := 1)
    (word := 13) (offset := 51) (by decide) rfl rfl (codeRange_slice_subset start bytes 51 4)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf5d7 (by decide)) (by clone_address step11 [6, 40]) (by decide) rfl (by rfl)
  obtain ⟨_, step13⟩ := step12.loadStack pre (am := (.sib 4 none 0 (.d32 424))) (dst := 2)
    (offset := 424) (by decide) rfl rfl (codeRange_slice_subset start bytes 55 8)
    rfl (continueAt 0xf5df (by decide)) (by clone_address step12 [4, 424]) (by decide) pre.innerPtr
    (by simp [components])
  obtain ⟨_, step14⟩ := step13.loadSource pre (am := (.base 2 (.d8 32))) (dst := 1)
    (word := 12) (by decide) rfl rfl (codeRange_slice_subset start bytes 63 4)
    rfl (continueAt 0xf5e3 (by decide)) (by clone_address step13 [2, 32]) (by decide) (by simp [components])
  obtain ⟨_, step15⟩ := step14.store pre (am := (.base 6 (.d8 32))) (r := 1)
    (word := 12) (offset := 67) (by decide) rfl rfl (codeRange_slice_subset start bytes 67 4)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf5e7 (by decide)) (by clone_address step14 [6, 32]) (by decide) rfl (by rfl)
  obtain ⟨_, step16⟩ := step15.loadSource pre (am := (.base 2 (.d8 24))) (dst := 1)
    (word := 11) (by decide) rfl rfl (codeRange_slice_subset start bytes 71 4)
    rfl (continueAt 0xf5eb (by decide)) (by clone_address step15 [2, 24]) (by decide) (by simp [components])
  obtain ⟨_, step17⟩ := step16.store pre (am := (.base 6 (.d8 24))) (r := 1)
    (word := 11) (offset := 75) (by decide) rfl rfl (codeRange_slice_subset start bytes 75 4)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf5ef (by decide)) (by clone_address step16 [6, 24]) (by decide) rfl (by rfl)
  obtain ⟨_, step18⟩ := step17.loadSource pre (am := (.base 2 (.d8 16))) (dst := 1)
    (word := 10) (by decide) rfl rfl (codeRange_slice_subset start bytes 79 4)
    rfl (continueAt 0xf5f3 (by decide)) (by clone_address step17 [2, 16]) (by decide) (by simp [components])
  obtain ⟨_, step19⟩ := step18.store pre (am := (.base 6 (.d8 16))) (r := 1)
    (word := 10) (offset := 83) (by decide) rfl rfl (codeRange_slice_subset start bytes 83 4)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf5f7 (by decide)) (by clone_address step18 [6, 16]) (by decide) rfl (by rfl)
  obtain ⟨_, step20⟩ := step19.loadSource pre (am := (.base 2 .none)) (dst := 1)
    (word := 8) (by decide) rfl rfl (codeRange_slice_subset start bytes 87 3)
    rfl (continueAt 0xf5fa (by decide)) (by clone_address step19 [2, 0]) (by decide) (by simp [components])
  obtain ⟨_, step21⟩ := step20.loadSource pre (am := (.base 2 (.d8 8))) (dst := 2)
    (word := 9) (by decide) rfl rfl (codeRange_slice_subset start bytes 90 4)
    rfl (continueAt 0xf5fe (by decide)) (by clone_address step20 [2, 8]) (by decide) (by simp [components])
  obtain ⟨_, step22⟩ := step21.store pre (am := (.base 6 (.d8 8))) (r := 2)
    (word := 9) (offset := 94) (by decide) rfl rfl (codeRange_slice_subset start bytes 94 4)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf602 (by decide)) (by clone_address step21 [6, 8]) (by decide) rfl (by rfl)
  obtain ⟨_, step23⟩ := step22.store pre (am := (.base 6 .none)) (r := 1)
    (word := 8) (offset := 98) (by decide) rfl rfl (codeRange_slice_subset start bytes 98 3)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf605 (by decide)) (by clone_address step22 [6, 0]) (by decide) rfl (by rfl)
  obtain ⟨_, step24⟩ := step23.loadStack pre (am := (.sib 4 none 0 (.d32 240))) (dst := 2)
    (offset := 240) (by decide) rfl rfl (codeRange_slice_subset start bytes 101 8)
    rfl (continueAt 0xf60d (by decide)) (by clone_address step23 [4, 240]) (by decide) pre.contextPtr
    (by simp [components])
  obtain ⟨_, step25⟩ := step24.loadSource pre (am := (.base 2 (.d8 56))) (dst := 1)
    (word := 7) (by decide) rfl rfl (codeRange_slice_subset start bytes 109 4)
    rfl (continueAt 0xf611 (by decide)) (by clone_address step24 [2, 56]) (by decide) (by simp [components])
  obtain ⟨_, step26⟩ := step25.store pre (am := (.sib 4 none 0 (.d32 328))) (r := 1)
    (word := 7) (offset := 113) (by decide) rfl rfl (codeRange_slice_subset start bytes 113 8)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf619 (by decide)) (by clone_address step25 [4, 328]) (by decide) rfl (by rfl)
  obtain ⟨_, step27⟩ := step26.loadSource pre (am := (.base 2 (.d8 48))) (dst := 1)
    (word := 6) (by decide) rfl rfl (codeRange_slice_subset start bytes 121 4)
    rfl (continueAt 0xf61d (by decide)) (by clone_address step26 [2, 48]) (by decide) (by simp [components])
  obtain ⟨_, step28⟩ := step27.store pre (am := (.sib 4 none 0 (.d32 320))) (r := 1)
    (word := 6) (offset := 125) (by decide) rfl rfl (codeRange_slice_subset start bytes 125 8)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf625 (by decide)) (by clone_address step27 [4, 320]) (by decide) rfl (by rfl)
  obtain ⟨_, step29⟩ := step28.loadSource pre (am := (.base 2 (.d8 40))) (dst := 1)
    (word := 5) (by decide) rfl rfl (codeRange_slice_subset start bytes 133 4)
    rfl (continueAt 0xf629 (by decide)) (by clone_address step28 [2, 40]) (by decide) (by simp [components])
  obtain ⟨_, step30⟩ := step29.store pre (am := (.sib 4 none 0 (.d32 312))) (r := 1)
    (word := 5) (offset := 137) (by decide) rfl rfl (codeRange_slice_subset start bytes 137 8)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf631 (by decide)) (by clone_address step29 [4, 312]) (by decide) rfl (by rfl)
  obtain ⟨_, step31⟩ := step30.loadSource pre (am := (.base 2 (.d8 32))) (dst := 1)
    (word := 4) (by decide) rfl rfl (codeRange_slice_subset start bytes 145 4)
    rfl (continueAt 0xf635 (by decide)) (by clone_address step30 [2, 32]) (by decide) (by simp [components])
  obtain ⟨_, step32⟩ := step31.store pre (am := (.sib 4 none 0 (.d32 304))) (r := 1)
    (word := 4) (offset := 149) (by decide) rfl rfl (codeRange_slice_subset start bytes 149 8)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf63d (by decide)) (by clone_address step31 [4, 304]) (by decide) rfl (by rfl)
  obtain ⟨_, step33⟩ := step32.loadSource pre (am := (.base 2 (.d8 24))) (dst := 1)
    (word := 3) (by decide) rfl rfl (codeRange_slice_subset start bytes 157 4)
    rfl (continueAt 0xf641 (by decide)) (by clone_address step32 [2, 24]) (by decide) (by simp [components])
  obtain ⟨_, step34⟩ := step33.store pre (am := (.sib 4 none 0 (.d32 296))) (r := 1)
    (word := 3) (offset := 161) (by decide) rfl rfl (codeRange_slice_subset start bytes 161 8)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf649 (by decide)) (by clone_address step33 [4, 296]) (by decide) rfl (by rfl)
  obtain ⟨_, step35⟩ := step34.loadSource pre (am := (.base 2 (.d8 16))) (dst := 1)
    (word := 2) (by decide) rfl rfl (codeRange_slice_subset start bytes 169 4)
    rfl (continueAt 0xf64d (by decide)) (by clone_address step34 [2, 16]) (by decide) (by simp [components])
  obtain ⟨_, step36⟩ := step35.store pre (am := (.sib 4 none 0 (.d32 288))) (r := 1)
    (word := 2) (offset := 173) (by decide) rfl rfl (codeRange_slice_subset start bytes 173 8)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf655 (by decide)) (by clone_address step35 [4, 288]) (by decide) rfl (by rfl)
  obtain ⟨_, step37⟩ := step36.loadSource pre (am := (.base 2 .none)) (dst := 1)
    (word := 0) (by decide) rfl rfl (codeRange_slice_subset start bytes 181 3)
    rfl (continueAt 0xf658 (by decide)) (by clone_address step36 [2, 0]) (by decide) (by simp [components])
  obtain ⟨_, step38⟩ := step37.loadSource pre (am := (.base 2 (.d8 8))) (dst := 2)
    (word := 1) (by decide) rfl rfl (codeRange_slice_subset start bytes 184 4)
    rfl (continueAt 0xf65c (by decide)) (by clone_address step37 [2, 8]) (by decide) (by simp [components])
  obtain ⟨_, step39⟩ := step38.store pre (am := (.sib 4 none 0 (.d32 280))) (r := 2)
    (word := 1) (offset := 188) (by decide) rfl rfl (codeRange_slice_subset start bytes 188 8)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf664 (by decide)) (by clone_address step38 [4, 280]) (by decide) rfl (by rfl)
  obtain ⟨_, step40⟩ := step39.store pre (am := (.sib 4 none 0 (.d32 272))) (r := 1)
    (word := 0) (offset := 196) (by decide) rfl rfl (codeRange_slice_subset start bytes 196 8)
    rfl (by rw [bytes_length]; decide) rfl (continueAt 0xf66c (by decide)) (by clone_address step39 [4, 272]) (by decide) rfl (by rfl)
  refine ⟨_, step40.run, step40.ready, step40.rip, step40.agrees, ?_⟩
  intro i hi
  have same := step40.words (i / 8) (by omega) (by omega) (i % 8) (by omega)
  rw [same_offsets, same_offsets, show 8 * (i / 8) + i % 8 = i by omega] at same
  exact same

theorem clone_hmac [Bindings] {s : RamState} {boundary : ReturnBoundary} {src : BitVec 64}
    {key message : ByteArray}
    (pre : Pre s src) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (hmac : HmacAt s src key message) :
    ∃ t, Advances boundary 40 s t ∧ ReadyToStep t ∧ t.RIP = 0x10f66c ∧
      AgreesExcept (components s) s t ∧ HmacAt t (destination t) key message := by
  obtain ⟨t, run, readyT, rip, frame, bytes⟩ := clone_context pre ready loaded outside
  have sp : rspOf t = rspOf s := frame.read (r := 4) (n := 64) (by simp [components])
  have target : destination t = destination s := congrArg (· + 272) sp
  exact ⟨t, run, readyT, rip, frame, target ▸ hmac.of_copy bytes⟩

end Hkdf.Proofs.NewExpand.Expand.ContextClone
