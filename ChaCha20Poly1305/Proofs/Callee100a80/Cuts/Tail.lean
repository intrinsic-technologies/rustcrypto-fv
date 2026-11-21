import ChaCha20Poly1305.Spec
import ChaCha20Poly1305.Proofs.ChaCha20.Refinement
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Execution
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Rounds
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Xor.Generated.R8M8.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.NopMem.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple

namespace ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Tail

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 ChaCha20Poly1305.Proofs.ChaCha20

def reg32 (t : RamState) (r : BitVec 5) : BitVec 32 := (Operand.reg r : Operand 32).read t

def reg64 (t : RamState) (r : BitVec 5) : BitVec 64 := (Operand.reg r : Operand 64).read t

def slot (sp : BitVec 64) (off : Nat) : BitVec 64 := sp + BitVec.ofNat 64 off

def slot32 (t : RamState) (sp : BitVec 64) (off : Nat) : BitVec 32 :=
  memLoad t.external (slot sp off) 32

def slot64 (t : RamState) (sp : BitVec 64) (off : Nat) : BitVec 64 :=
  memLoad t.external (slot sp off) 64

def codeLo : Nat := 0x1010cc

def codeHi : Nat := 0x1014aa

def frameBytes : Nat := 0x170

def stateBytes : Nat := 0x80

def base (size : Nat) : Nat := 64 * (size / 64)

def tail (size : Nat) : Nat := size % 64

def quad (size : Nat) : Nat := tail size - tail size % 4

def NotCode (a : BitVec 64) (n : Nat) : Prop := ∀ i < n, ¬ InProgram (a + BitVec.ofNat 64 i)

def outTail (output : BitVec 64) (size : Nat) : BitVec 64 := output + BitVec.ofNat 64 (base size)

def inTail (input : BitVec 64) (size : Nat) : BitVec 64 := input + BitVec.ofNat 64 (base size)

def stream (x : Vector UInt32 16) : Vector UInt8 64 := serialize (runRounds x)

structure Space (sp st input output : BitVec 64) (size : Nat) (t : RamState) : Prop where
  rsp : stackPtr t = sp
  stack : MemWritable t sp frameBytes
  stackCode : NotCode sp frameBytes
  state : MemWritable t st stateBytes
  stateCode : NotCode st stateBytes
  stateStack : RangeApart st stateBytes sp frameBytes
  out : tail size ≠ 0 → MemWritable t (outTail output size) (tail size)
  outCode : NotCode (outTail output size) (tail size)
  outStack : RangeApart (outTail output size) (tail size) sp frameBytes
  outState : RangeApart (outTail output size) (tail size) st stateBytes
  inLow : input.toNat + size ≤ 2 ^ 32
  outLow : output.toNat + size ≤ 2 ^ 32
  inStack : RangeApart (inTail input size) (tail size) sp frameBytes
  inState : RangeApart (inTail input size) (tail size) st stateBytes
  alias : input = output ∨ RangeApart (inTail input size) (tail size) (outTail output size) (tail size)

structure Slots (sp st input output : BitVec 64) (size : Nat) (t : RamState) : Prop where
  state : slot64 t sp 0x48 = st
  output : slot64 t sp 0x88 = output
  input : slot64 t sp 0x90 = input
  head : slot64 t sp 0x98 = 0
  tail : slot64 t sp 0xa0 = BitVec.ofNat 64 (tail size)
  length : slot64 t sp 0xa8 = BitVec.ofNat 64 size

def changes (sp st output : BitVec 64) (size : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip,
    .mem sp frameBytes, .mem (st + 0x30) 4, .mem (st + 0x40) 0x40,
    .mem (outTail output size) (tail size)]

def Rest (input : BitVec 64) (size : Nat) (msg : Nat → UInt8) (start : Nat) (t : RamState) :
    Prop :=
  ∀ i, start ≤ i → i < size → t.external[input + BitVec.ofNat 64 i]? = some (msg i)

def Wrote (output : BitVec 64) (size : Nat) (msg : Nat → UInt8) (ks : Vector UInt8 64)
    (upto : Nat) (t : RamState) : Prop :=
  ∀ i, base size ≤ i → i < upto →
    t.external[output + BitVec.ofNat 64 i]? = some (msg i ^^^ ks[i - base size]!)

def BytesAt (addr : BitVec 64) (bytes : Vector UInt8 64) (t : RamState) : Prop :=
  ∀ i : Fin 64, t.external[addr + BitVec.ofNat 64 i.val]? = some bytes[i]

structure TailCut (sp st input output : BitVec 64) (size : Nat) (msg : Nat → UInt8)
    (x : Vector UInt32 16) (t : RamState) : Prop where
  rip : t.RIP = 0x1010cc
  space : Space sp st input output size t
  slots : Slots sp st input output size t
  state : reg64 t 7 = st
  length : reg64 t 11 = BitVec.ofNat 64 size
  tail : reg64 t 15 = BitVec.ofNat 64 (tail size)
  words : BytesAt st (serialize x) t
  rest : Rest input size msg (base size) t

structure Working (sp : BitVec 64) (x : Vector UInt32 16) (t : RamState) : Prop where
  w0 : slot32 t sp 0x8 = x[0].toBitVec
  w1 : reg32 t 13 = x[1].toBitVec
  w2 : reg32 t 0 = x[2].toBitVec
  w3 : reg32 t 7 = x[3].toBitVec
  w4 : reg32 t 9 = x[4].toBitVec
  w5 : reg32 t 5 = x[5].toBitVec
  w6 : reg32 t 15 = x[6].toBitVec
  w7 : reg32 t 6 = x[7].toBitVec
  w8 : slot32 t sp 0x4 = x[8].toBitVec
  w9 : reg32 t 10 = x[9].toBitVec
  w10 : reg32 t 14 = x[10].toBitVec
  w11 : reg32 t 12 = x[11].toBitVec
  w12 : reg32 t 1 = x[12].toBitVec
  w13 : reg32 t 2 = x[13].toBitVec
  w14 : reg32 t 8 = x[14].toBitVec
  w15 : reg32 t 11 = x[15].toBitVec

structure Initial (sp : BitVec 64) (x : Vector UInt32 16) (t : RamState) : Prop where
  w0 : slot32 t sp 0x38 = x[0].toBitVec
  w1 : slot32 t sp 0x60 = x[1].toBitVec
  w2 : slot32 t sp 0x68 = x[2].toBitVec
  w3 : slot32 t sp 0xc = x[3].toBitVec
  w4 : slot32 t sp 0x50 = x[4].toBitVec
  w5 : slot32 t sp 0x70 = x[5].toBitVec
  w6 : slot32 t sp 0x3c = x[6].toBitVec
  w7 : slot32 t sp 0x10 = x[7].toBitVec
  w8 : slot32 t sp 0x18 = x[8].toBitVec
  w9 : slot32 t sp 0x1c = x[9].toBitVec
  w10 : slot32 t sp 0x20 = x[10].toBitVec
  w11 : slot32 t sp 0x24 = x[11].toBitVec
  w12 : slot32 t sp 0x34 = x[12].toBitVec
  w13 : slot32 t sp 0x28 = x[13].toBitVec
  w14 : slot32 t sp 0x2c = x[14].toBitVec
  w15 : slot32 t sp 0x30 = x[15].toBitVec

structure Rounds (sp st input output : BitVec 64) (size : Nat) (msg : Nat → UInt8)
    (x : Vector UInt32 16) (k : Nat) (t : RamState) : Prop where
  rip : t.RIP = if k < 10 then 0x101180 else 0x1012e3
  space : Space sp st input output size t
  slots : Slots sp st input output size t
  le : k ≤ 10
  working : Working sp (Nat.repeat doubleRound k x) t
  initial : Initial sp x t
  count : slot64 t sp 0x58 = BitVec.ofNat 64 (10 - k)
  offset : slot64 t sp 0x40 = BitVec.ofNat 64 (base size)
  nonzero : tail size ≠ 0
  rest : Rest input size msg (base size) t

structure Keyed (sp st input output : BitVec 64) (size : Nat) (msg : Nat → UInt8)
    (x : Vector UInt32 16) (t : RamState) : Prop where
  rip : t.RIP = 0x1013a3
  space : Space sp st input output size t
  slots : Slots sp st input output size t
  block : BytesAt (st + 0x40) (stream x) t
  state : reg64 t 9 = st
  offset : slot64 t sp 0x40 = BitVec.ofNat 64 (base size)
  nonzero : tail size ≠ 0
  rest : Rest input size msg (base size) t

structure Branched (sp st input output : BitVec 64) (size : Nat) (msg : Nat → UInt8)
    (x : Vector UInt32 16) (t : RamState) : Prop where
  rip : t.RIP = if tail size < 4 then 0x1013bf else 0x1013e3
  space : Space sp st input output size t
  slots : Slots sp st input output size t
  block : BytesAt (st + 0x40) (stream x) t
  state : reg64 t 9 = st
  offset : slot64 t sp 0x40 = BitVec.ofNat 64 (base size)
  nonzero : tail size ≠ 0
  rest : Rest input size msg (base size) t
  length : reg64 t 10 = BitVec.ofNat 64 size
  rem : reg64 t 0 = BitVec.ofNat 64 (tail size % 4)
  tail : reg64 t 14 = BitVec.ofNat 64 (tail size)

structure Quad (sp st input output : BitVec 64) (size : Nat) (msg : Nat → UInt8)
    (x : Vector UInt32 16) (j : Nat) (t : RamState) : Prop where
  rip : t.RIP = 0x101420
  space : Space sp st input output size t
  block : BytesAt (st + 0x40) (stream x) t
  aligned : j % 4 = 0
  lt : j < quad size
  state : reg64 t 9 = st
  index : reg64 t 6 = BitVec.ofNat 64 j
  src : reg64 t 1 = inTail input size + 3
  dst : reg64 t 2 = outTail output size + 3
  bound : reg64 t 10 = BitVec.ofNat 64 (quad size)
  rem : reg64 t 0 = BitVec.ofNat 64 (tail size % 4)
  tail : reg64 t 14 = BitVec.ofNat 64 (tail size)
  head : reg64 t 8 = 0
  offset : reg64 t 15 = BitVec.ofNat 64 (base size)
  inPtr : reg64 t 11 = input
  outPtr : reg64 t 3 = output
  rest : Rest input size msg (base size + j) t
  wrote : Wrote output size msg (stream x) (base size + j) t

structure QuadNext (sp st input output : BitVec 64) (size : Nat) (msg : Nat → UInt8)
    (x : Vector UInt32 16) (j : Nat) (t : RamState) : Prop where
  rip : t.RIP = if j < quad size then 0x101420 else 0x101467
  space : Space sp st input output size t
  block : BytesAt (st + 0x40) (stream x) t
  aligned : j % 4 = 0
  le : j ≤ quad size
  state : reg64 t 9 = st
  index : reg64 t 6 = BitVec.ofNat 64 j
  src : reg64 t 1 = inTail input size + 3
  dst : reg64 t 2 = outTail output size + 3
  bound : reg64 t 10 = BitVec.ofNat 64 (quad size)
  rem : reg64 t 0 = BitVec.ofNat 64 (tail size % 4)
  tail : reg64 t 14 = BitVec.ofNat 64 (tail size)
  head : reg64 t 8 = 0
  offset : reg64 t 15 = BitVec.ofNat 64 (base size)
  inPtr : reg64 t 11 = input
  outPtr : reg64 t 3 = output
  rest : Rest input size msg (base size + j) t
  wrote : Wrote output size msg (stream x) (base size + j) t

structure Single (sp st input output : BitVec 64) (size : Nat) (msg : Nat → UInt8)
    (x : Vector UInt32 16) (j : Nat) (t : RamState) : Prop where
  rip : t.RIP = 0x101490
  space : Space sp st input output size t
  block : BytesAt (st + 0x40) (stream x) t
  ge : quad size ≤ j
  lt : j < tail size
  state : reg64 t 9 = st
  index : reg64 t 2 = BitVec.ofNat 64 (j - quad size)
  src : reg64 t 1 = st + 0x40 + BitVec.ofNat 64 (quad size)
  inPtr : reg64 t 11 = inTail input size + BitVec.ofNat 64 (quad size)
  outPtr : reg64 t 3 = outTail output size + BitVec.ofNat 64 (quad size)
  rem : reg64 t 0 = BitVec.ofNat 64 (tail size % 4)
  tail : reg64 t 14 = BitVec.ofNat 64 (tail size)
  rest : Rest input size msg (base size + j) t
  wrote : Wrote output size msg (stream x) (base size + j) t

structure Rem (sp st input output : BitVec 64) (size : Nat) (msg : Nat → UInt8)
    (x : Vector UInt32 16) (t : RamState) : Prop where
  rip : t.RIP = 0x10146c
  space : Space sp st input output size t
  block : BytesAt (st + 0x40) (stream x) t
  nonzero : tail size % 4 ≠ 0
  state : reg64 t 9 = st
  index : reg64 t 6 = BitVec.ofNat 64 (quad size)
  head : reg64 t 8 = 0
  offset : reg64 t 15 = BitVec.ofNat 64 (base size)
  inPtr : reg64 t 11 = input
  outPtr : reg64 t 3 = output
  rem : reg64 t 0 = BitVec.ofNat 64 (tail size % 4)
  tail : reg64 t 14 = BitVec.ofNat 64 (tail size)
  rest : Rest input size msg (base size + quad size) t
  wrote : Wrote output size msg (stream x) (base size + quad size) t

structure Done (sp st input output : BitVec 64) (size : Nat) (msg : Nat → UInt8)
    (x : Vector UInt32 16) (t : RamState) : Prop where
  rip : t.RIP = 0x1014a4
  space : Space sp st input output size t
  state : reg64 t 9 = st
  tail : reg64 t 14 = BitVec.ofNat 64 (tail size)
  wrote : Wrote output size msg (stream x) size t

structure Final (output : BitVec 64) (size : Nat) (msg : Nat → UInt8) (x : Vector UInt32 16)
    (t : RamState) : Prop where
  rip : t.RIP = 0x1014aa
  status : (rax.read t).setWidth 8 = 0
  wrote : Wrote output size msg (stream x) size t

def Reach [Bindings] (boundary : ReturnBoundary) (sp st output : BitVec 64) (size : Nat)
    (t : RamState) (P : RamState → Prop) : Prop :=
  ∃ fuel u, Advances boundary fuel t u ∧ ReadyToStep u ∧ CodeIn Extracted.programImage u ∧
    AgreesExcept (changes sp st output size) t u ∧ P u

theorem Reach.trans [Bindings] {boundary : ReturnBoundary} {sp st output : BitVec 64}
    {size : Nat} {t : RamState} {P Q : RamState → Prop}
    (h : Reach boundary sp st output size t P)
    (k : ∀ u, ReadyToStep u → CodeIn Extracted.programImage u → P u →
      Reach boundary sp st output size u Q) :
    Reach boundary sp st output size t Q := by
  obtain ⟨f, u, ha, hr, hc, hg, hp⟩ := h
  obtain ⟨g, v, ha', hr', hc', hg', hq⟩ := k u hr hc hp
  exact ⟨f + g, v, ha.trans ha', hr', hc', (hg.trans hg').mono (by simp), hq⟩

theorem reach_refl [Bindings] {boundary : ReturnBoundary} {sp st output : BitVec 64}
    {size : Nat} {t : RamState} {P : RamState → Prop} (hr : ReadyToStep t)
    (hc : CodeIn Extracted.programImage t) (h : P t) : Reach boundary sp st output size t P :=
  ⟨0, t, (advances_zero _ _ _).mpr rfl, hr, hc, AgreesExcept.refl _ _, h⟩

section Helpers

open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

theorem ne_boundary {boundary : ReturnBoundary}
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) {p : BitVec 64}
    (h1 : 0x100a80 ≤ p.toNat) (h2 : p.toNat < 0x1014bc) : p ≠ boundary.rip := by
  rintro rfl; omega

theorem NotCode.slice {a : BitVec 64} {n : Nat} (h : NotCode a n) (off k : Nat)
    (hk : off + k ≤ n) : NotCode (a + BitVec.ofNat 64 off) k := by
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

theorem NotCode.apart {a p : BitVec 64} {n len : Nat} (h : NotCode a n)
    (hp : ∀ j < len, InProgram (p + BitVec.ofNat 64 j)) : RangeApart a n p len :=
  fun i hi j hj he ↦ h i hi (he ▸ hp j hj)

theorem text_in_program (off len : Nat) (h : off + len ≤ Extracted.textBytes.size) :
    ∀ j < len, InProgram (Extracted.textAddress + BitVec.ofNat 64 off + BitVec.ofNat 64 j) := by
  intro j hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program _ (by omega)

theorem text_in_program' (p : BitVec 64) (off len : Nat)
    (hp : p = Extracted.textAddress + BitVec.ofNat 64 off)
    (h : off + len ≤ Extracted.textBytes.size) :
    ∀ j < len, InProgram (p + BitVec.ofNat 64 j) := by
  subst hp; exact text_in_program off len h

theorem writable_slice {s : RamState} {a : BitVec 64} {n : Nat} (h : MemWritable s a n)
    (off len : Nat) (hn : off + len ≤ n) : MemWritable s (a + BitVec.ofNat 64 off) len := by
  have hl := h.low
  have ha : (a + BitVec.ofNat 64 off).toNat = a.toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨by omega, fun i hi => ?_, ?_⟩
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h.mem _ (by omega)
  · rw [ha]; exact h.tables.sub (by omega) (by omega)

theorem store_avoids {e : Effect} {a : BitVec 64} {n : Nat} (hcs : e.components = [.mem a n, .rip])
    (h : NotCode a n) : e.Avoids Extracted.programImage := by
  intro x hx c hc hcov
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨i, hi, he⟩ := hcov
    exact h i hi (he ▸ inProgram_of_mem hx)
  · exact hcov

theorem step [Bindings] {pre : RamState → Prop} {e : RamState → Effect}
    {boundary : ReturnBoundary} {p : BitVec 64} {bytes : List UInt8}
    (hStep : StepEffect pre (codeRange p bytes) e) {u : RamState} (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hbytes : CodeIn (codeRange p bytes) u)
    (hpre : pre u) (hne : (e u).rip ≠ boundary.rip) (hav : (e u).Avoids Extracted.programImage) :
    ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      (e u).Holds u v := by
  obtain ⟨v, ha, hr', he⟩ := hStep.advances hr hbytes hpre hne
  exact ⟨v, ha, hr', he.codeIn hav hc, he⟩

theorem out_addr (output : BitVec 64) {size i : Nat} (hi : base size ≤ i) :
    output + BitVec.ofNat 64 i = outTail output size + BitVec.ofNat 64 (i - base size) := by
  unfold outTail
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hi]

theorem in_addr (input : BitVec 64) {size i : Nat} (hi : base size ≤ i) :
    input + BitVec.ofNat 64 i = inTail input size + BitVec.ofNat 64 (i - base size) := by
  unfold inTail
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hi]

theorem base_le (size : Nat) : base size + tail size = size := by
  unfold base tail; omega

theorem readable_of_get {t : RamState} {a : BitVec 64} {b : UInt8}
    (h : t.external[a]? = some b) (hl : a.toNat + 1 ≤ 2 ^ 32) : MemReadable t a 1 :=
  ⟨hl, fun i hi ↦ by rw [show i = 0 by omega, BitVec.add_zero, h]; rfl⟩

theorem load8_of_get {m : Ram} {a : BitVec 64} {b : UInt8} (h : m[a]? = some b) :
    memLoad m a 8 = b.toBitVec := by
  rw [memLoad_8, memByte]
  simp [PhysicalMemory.read, h]

theorem get_of_load8 {m : Ram} {a : BitVec 64} {b : BitVec 8} (hs : (m[a]?).isSome)
    (h : memLoad m a 8 = b) : m[a]? = some (UInt8.ofBitVec b) := by
  rw [memLoad_8, memByte] at h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
  simp only [PhysicalMemory.read, hc, Option.getD_some] at h
  rw [hc, ← h]

theorem toNat_add_ofNat {a : BitVec 64} {k : Nat} (h : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt h]

theorem add_ofNat_ne {a : BitVec 64} {i k : Nat} (hi : a.toNat + i < 2 ^ 64)
    (hk : a.toNat + k < 2 ^ 64) (hne : i ≠ k) : a + BitVec.ofNat 64 i ≠ a + BitVec.ofNat 64 k := by
  intro he
  have := congrArg BitVec.toNat he
  rw [toNat_add_ofNat hi, toNat_add_ofNat hk] at this
  omega

theorem writable_grow {cs : List Component} {t u : RamState} {a : BitVec 64} {n : Nat}
    (h : MemWritable t a n) (g : AgreesExcept cs t u) : MemWritable u a n :=
  ⟨h.low, fun i hi ↦ g.grow _ (h.mem i hi), h.tables⟩

theorem stackPtr_agrees {cs : List Component} {t u : RamState} (g : AgreesExcept cs t u)
    (h : Component.reg 4 ∉ cs) : stackPtr u = stackPtr t :=
  g.agree _ h rfl

theorem Space.transfer {sp st input output : BitVec 64} {size : Nat} {cs : List Component}
    {t u : RamState} (h : Space sp st input output size t) (g : AgreesExcept cs t u)
    (h4 : Component.reg 4 ∉ cs) : Space sp st input output size u :=
  { h with
    rsp := (stackPtr_agrees g h4).trans h.rsp
    stack := writable_grow h.stack g
    state := writable_grow h.state g
    out := fun hz ↦ writable_grow (h.out hz) g }

theorem BytesAt.transfer {a : BitVec 64} {bs : Vector UInt8 64} {cs : List Component}
    {t u : RamState} (h : BytesAt a bs t) (g : AgreesExcept cs t u)
    (hx : ∀ i < 64, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) : BytesAt a bs u :=
  fun i ↦ (g.byte (hx i.val i.isLt)).trans (h i)

theorem reg8_eq (r : BitVec 5) (s : RamState) :
    (Operand.reg r : Operand 8).read s = ((Operand.reg r : Operand 64).read s).setWidth 8 := by
  simp [Operand.read]

theorem not_covers_of {L : List Component} {a y : BitVec 64} {n : Nat}
    (hL : ∀ c ∈ L, c = .mem a n ∨ c.isMem = false)
    (hy : ∀ k < n, y ≠ a + BitVec.ofNat 64 k) : ∀ c ∈ L, ¬ c.Covers y := by
  intro c hc hcv
  rcases hL c hc with rfl | hm
  · obtain ⟨k, hk, rfl⟩ := hcv
    exact hy k hk rfl
  · cases c <;> simp_all [Component.isMem, Component.Covers]

theorem covered_of {L L' : List Component} {a : BitVec 64} {n : Nat}
    (hL : ∀ c ∈ L, c = .mem a n ∨ c.isMem = false)
    (h : ∀ k < n, ∃ c' ∈ L', c'.Covers (a + BitVec.ofNat 64 k)) :
    ∀ y, ∀ c ∈ L, c.Covers y → ∃ c' ∈ L', c'.Covers y := by
  intro y c hc hcv
  rcases hL c hc with rfl | hm
  · obtain ⟨k, hk, rfl⟩ := hcv
    exact h k hk
  · cases c <;> simp_all [Component.isMem, Component.Covers]

theorem mergeGPR8_low (r : BitVec 8) (old : BitVec 64) : (mergeGPR 8 r old).setWidth 8 = r := by
  unfold mergeGPR
  simp only [show (8 : Nat) ≠ 32 by decide, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp [hi]

theorem sib_addr {b : BitVec 4} {d : Disp} {t u : RamState} {cs : List Component} (next : BitVec 64)
    (g : AgreesExcept cs t u) (hb : Component.reg (b.setWidth 5) ∉ cs) (h6 : Component.reg 6 ∉ cs) :
    AddrMode.addr (.sib b (some 6) 0 d) u next = AddrMode.addr (.sib b (some 6) 0 d) t next := by
  simp only [AddrMode.addr, AddrMode.reg64]
  rw [g.read hb, show ((6 : BitVec 4).setWidth 5) = 6 from rfl, g.read h6]

theorem xor_byte [Bindings] {boundary : ReturnBoundary} {t : RamState} (hr : ReadyToStep t)
    (hc : CodeIn Extracted.programImage t) (p p2 p3 p4 : BitVec 64) (bL bX bS : BitVec 4)
    (dL dX dS : Disp)
    (hvL : (AddrMode.sib bL (some 6) 0 dL).Valid) (hvX : (AddrMode.sib bX (some 6) 0 dX).Valid)
    (hvS : (AddrMode.sib bS (some 6) 0 dS).Valid)
    (hxL : rexX (UInt8.toBitVec 0x41) = (AddrMode.sib bL (some 6) 0 dL).rexX)
    (hbL : rexB (UInt8.toBitVec 0x41) = (AddrMode.sib bL (some 6) 0 dL).rexB)
    (hxX : rexX (UInt8.toBitVec 0x40) = (AddrMode.sib bX (some 6) 0 dX).rexX)
    (hbX : rexB (UInt8.toBitVec 0x40) = (AddrMode.sib bX (some 6) 0 dX).rexB)
    (hxS : rexX (UInt8.toBitVec 0x40) = (AddrMode.sib bS (some 6) 0 dS).rexX)
    (hbS : rexB (UInt8.toBitVec 0x40) = (AddrMode.sib bS (some 6) 0 dS).rexB)
    (hbX7 : bX.setWidth 5 ≠ 7) (hbS7 : bS.setWidth 5 ≠ 7)
    (hp2 : p + BitVec.ofNat 64 (4 + (AddrMode.sib bL (some 6) 0 dL).tail.length) = p2)
    (hp3 : p2 + BitVec.ofNat 64 (3 + (AddrMode.sib bX (some 6) 0 dX).tail.length) = p3)
    (hp4 : p3 + BitVec.ofNat 64 (3 + (AddrMode.sib bS (some 6) 0 dS).tail.length) = p4)
    (hcode : ∀ u, CodeIn Extracted.programImage u →
      CodeIn (codeRange p (0x41 :: 0x0F :: 0xB6 :: (AddrMode.sib bL (some 6) 0 dL).modrm 7 ::
          (AddrMode.sib bL (some 6) 0 dL).tail)) u ∧
      CodeIn (codeRange p2 (0x40 :: 0x32 :: (AddrMode.sib bX (some 6) 0 dX).modrm 7 ::
          (AddrMode.sib bX (some 6) 0 dX).tail)) u ∧
      CodeIn (codeRange p3 (0x40 :: 0x88 :: (AddrMode.sib bS (some 6) 0 dS).modrm 7 ::
          (AddrMode.sib bS (some 6) 0 dS).tail)) u)
    (hn2 : p2 ≠ boundary.rip) (hn3 : p3 ≠ boundary.rip) (hn4 : p4 ≠ boundary.rip)
    (lenS : Nat) (hlenS : 3 + (AddrMode.sib bS (some 6) 0 dS).tail.length = lenS)
    (hcodeIn2 : ∀ j < lenS, InProgram (p3 + BitVec.ofNat 64 j))
    {aL aX aS : BitVec 64} {kb mb : UInt8} (hip : t.RIP = p)
    (hAL : AddrMode.addr (.sib bL (some 6) 0 dL) t p2 = aL)
    (hAX : AddrMode.addr (.sib bX (some 6) 0 dX) t p3 = aX)
    (hAS : AddrMode.addr (.sib bS (some 6) 0 dS) t p4 = aS)
    (hkb : t.external[aL]? = some kb) (hmb : t.external[aX]? = some mb)
    (hlL : aL.toNat + 1 ≤ 2 ^ 32) (hlX : aX.toNat + 1 ≤ 2 ^ 32)
    (hwS : MemWritable t aS 1) (hncS : NotCode aS 1) :
    ∃ v, Advances boundary (1 + 1 + 1) t v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      AgreesExcept [.reg 7, .flags, .rip, .mem aS 1] t v ∧ v.RIP = p4 ∧
      v.external[aS]? = some (mb ^^^ kb) := by
  obtain ⟨u1, a1, r1, c1, e1⟩ := step (boundary := boundary)
    (movzx_r32_m8_rex_effect_step p 0x41 (by unfold RexNoWPrefix; decide) 7
      (.sib bL (some 6) 0 dL) hvL hxL hbL)
    hr hc (hcode t hc).1 ⟨hip, by rw [hp2, hAL]; exact readable_of_get hkb hlL⟩
    (by intro he; apply hn2; rw [← hp2]; exact he)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x41)) 7 = 7 from rfl] at e1
  have g1 := e1.agrees
  simp only [movzxR32M8Effect_components] at g1
  have v1 : (Operand.reg 7 : Operand 8).read u1 = kb.toBitVec := by
    have hw := e1.writes
    simp only [movzxR32M8Effect, Write.AllHold] at hw
    rw [reg8_eq, hw, hp2, hAL]
    show ((memLoad t.external aL 8).setWidth 64).setWidth 8 = _
    rw [load8_of_get hkb]
    simp [BitVec.setWidth_setWidth_of_le]
  have hx1 : u1.external = t.external := g1.external (by simp [Component.Covers])
  have hAX1 : AddrMode.addr (.sib bX (some 6) 0 dX) u1 p3 = aX := by
    rw [sib_addr _ g1 (by simpa using hbX7) (by simp)]; exact hAX
  obtain ⟨u2, a2, r2, c2, e2⟩ := step (boundary := boundary)
    (xor_r8_m8_rex_effect_step p2 0x40 (by unfold RexPrefix; decide) 7
      (.sib bX (some 6) 0 dX) hvX hxX hbX)
    r1 c1 (hcode u1 c1).2.1
    ⟨e1.rip.trans hp2, by
      rw [hp3, hAX1]; exact readable_of_get (by rw [hx1]; exact hmb) hlX⟩
    (by intro he; apply hn3; rw [← hp3]; exact he)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x40)) 7 = 7 from rfl] at e2
  have g2 := e2.agrees
  simp only [xorR8M8Effect_components] at g2
  have v2 : (Operand.reg 7 : Operand 8).read u2 = (mb ^^^ kb).toBitVec := by
    have hw := e2.writes
    simp only [xorR8M8Effect, Write.AllHold] at hw
    rw [reg8_eq, hw, mergeGPR8_low, hp3, hAX1, v1]
    change _ ^^^ memLoad u1.external _ 8 = _
    rw [hx1, load8_of_get hmb, UInt8.xor_comm]
    rfl
  have g12 := g1.trans g2
  have hAS2 : AddrMode.addr (.sib bS (some 6) 0 dS) u2 p4 = aS := by
    rw [sib_addr _ g12 (by simpa using hbS7) (by simp)]; exact hAS
  obtain ⟨v, a3, r3, c3, e3⟩ := step (boundary := boundary)
    (mov_m8_r8_rex_effect_step p3 0x40 (by unfold RexPrefix; decide) 7
      (.sib bS (some 6) 0 dS) hvS hxS hbS)
    r2 c2 (hcode u2 c2).2.2
    ⟨e2.rip.trans hp3, by rw [hp4, hAS2]; exact writable_grow hwS g12, by
      rw [hp4, hAS2, hlenS]; exact hncS.apart hcodeIn2⟩
    (by intro he; apply hn4; rw [← hp4]; exact he)
    (store_avoids (a := aS) (n := 1)
      (by simp only [movM8R8Effect, storeEffect_components, hp4, hAS2]) hncS)
  have g3 := e3.agrees
  rw [show (movM8R8Effect p3 (3 + (AddrMode.sib bS (some 6) 0 dS).tail.length)
      (gprNumber 0 (rexR (UInt8.toBitVec 0x40)) 7) (.sib bS (some 6) 0 dS) u2).components =
      [.mem aS 1, .rip] by simp only [movM8R8Effect, storeEffect_components, hp4, hAS2]] at g3
  refine ⟨v, (a1.trans a2).trans a3, r3, c3, (g12.trans g3).mono (by simp), e3.rip.trans hp4, ?_⟩
  have hw := e3.writes
  simp only [movM8R8Effect, storeEffect, Write.AllHold, hp4, hAS2] at hw
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x40)) 7 = 7 from rfl, v2] at hw
  have hs := (writable_grow hwS (g12.trans g3)).mem 0 (by decide)
  rw [BitVec.add_zero] at hs
  rw [get_of_load8 hs hw]

theorem rstep [Bindings] {e : RamState → Effect} {boundary : ReturnBoundary}
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) {p q : BitVec 64}
    {bytes : List UInt8} (hStep : StepEffect (fun s ↦ s.RIP = p) (codeRange p bytes) e)
    {u : RamState} (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u)
    (hbytes : CodeIn (codeRange p bytes) u) (hip : u.RIP = p) (hq : (e u).rip = q)
    (hq1 : 0x100a80 ≤ q.toNat) (hq2 : q.toNat < 0x1014bc)
    (hnm : ∀ c ∈ (e u).components, c.isMem = false) :
    ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      (e u).Holds u v ∧ v.RIP = q := by
  obtain ⟨v, a, r, c, e'⟩ := step hStep hr hc hbytes hip (by rw [hq]; exact ne_boundary hb hq1 hq2)
    (Effect.Avoids.of_noMem (fun c hc x ↦ by
      have := hnm c hc
      cases c <;> simp_all [Component.isMem, Component.Covers]) _)
  exact ⟨v, a, r, c, e', e'.rip.trans hq⟩

theorem keep {t u : RamState} {a y : BitVec 64} {cs : List Component}
    (g : AgreesExcept (cs ++ [.mem a 1]) t u) (hcs : ∀ c ∈ cs, c.isMem = false) (hy : y ≠ a) :
    u.external[y]? = t.external[y]? := by
  refine g.byte fun c hc hcv ↦ ?_
  rcases List.mem_append.mp hc with hc | hc
  · have := hcs c hc
    cases c <;> simp_all [Component.isMem, Component.Covers]
  · simp only [List.mem_singleton] at hc
    subst hc
    obtain ⟨k, hk, rfl⟩ := hcv
    exact hy (by rw [show k = 0 by omega, BitVec.add_zero])

theorem keep7 {t u : RamState} {a y : BitVec 64}
    (g : AgreesExcept [.reg 7, .flags, .rip, .mem a 1] t u) (hy : y ≠ a) :
    u.external[y]? = t.external[y]? :=
  keep (cs := [.reg 7, .flags, .rip]) g (by simp [Component.isMem]) hy

theorem addL (a : BitVec 64) (j c : Nat) :
    a + BitVec.ofNat 64 j + BitVec.ofNat 64 c = a + BitVec.ofNat 64 (c + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

theorem addX (a : BitVec 64) (j k : Nat) :
    a + 3 + BitVec.ofNat 64 j + BitVec.ofNat 64 (2 ^ 64 - 3 + k) = a + BitVec.ofNat 64 (j + k) := by
  bv_omega

theorem addX3 (a : BitVec 64) (j : Nat) :
    a + 3 + BitVec.ofNat 64 j + 0 = a + BitVec.ofNat 64 (j + 3) := by
  bv_omega

theorem blk_addr (st : BitVec 64) (off j : Nat) (h : 0x40 ≤ off) :
    st + BitVec.ofNat 64 off + BitVec.ofNat 64 j = st + 0x40 + BitVec.ofNat 64 (off - 0x40 + j) := by
  bv_omega

theorem addB (a : BitVec 64) (m : Nat) :
    a + 0x40 + BitVec.ofNat 64 m = a + BitVec.ofNat 64 (0x40 + m) := by
  bv_omega

theorem tail_add (a : BitVec 64) (b m : Nat) :
    a + BitVec.ofNat 64 b + BitVec.ofNat 64 m = a + BitVec.ofNat 64 (b + m) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem Space.out_ne {sp st input output : BitVec 64} {size : Nat} {t : RamState}
    (h : Space sp st input output size t) {i k : Nat} (hi : i < size) (hk : k < size) (hne : i ≠ k) :
    output + BitVec.ofNat 64 i ≠ output + BitVec.ofNat 64 k :=
  add_ofNat_ne (by have := h.outLow; omega) (by have := h.outLow; omega) hne

theorem Space.in_out_ne {sp st input output : BitVec 64} {size : Nat} {t : RamState}
    (h : Space sp st input output size t) {i k : Nat} (hi1 : base size ≤ i) (hi : i < size)
    (hk1 : base size ≤ k) (hk : k < size) (hne : i ≠ k) :
    input + BitVec.ofNat 64 i ≠ output + BitVec.ofNat 64 k := by
  have := base_le size
  rcases h.alias with he | hap
  · subst he
    exact add_ofNat_ne (by have := h.outLow; omega) (by have := h.outLow; omega) hne
  · rw [in_addr input (size := size) hi1, out_addr output (size := size) hk1]
    exact hap (i - base size) (by omega) (k - base size) (by omega)

theorem Space.state_out_ne {sp st input output : BitVec 64} {size : Nat} {t : RamState}
    (h : Space sp st input output size t) {i k : Nat} (hi : i < stateBytes) (hk1 : base size ≤ k)
    (hk : k < size) : st + BitVec.ofNat 64 i ≠ output + BitVec.ofNat 64 k := by
  have := base_le size
  rw [out_addr output (size := size) hk1]
  exact fun he ↦ h.outState (k - base size) (by omega) i hi he.symm

theorem sib_val {b : BitVec 4} {d : Disp} {t : RamState} {B : BitVec 64} {j : Nat} (next : BitVec 64)
    (hb : (Operand.reg (b.setWidth 5) : Operand 64).read t = B)
    (h6 : (Operand.reg 6 : Operand 64).read t = BitVec.ofNat 64 j) :
    AddrMode.addr (.sib b (some 6) 0 d) t next = B + BitVec.ofNat 64 j + d.value := by
  simp only [AddrMode.addr, AddrMode.reg64]
  rw [hb, show ((6 : BitVec 4).setWidth 5) = 6 from rfl, h6,
    show BitVec.toNat (0 : BitVec 2) = 0 from rfl, BitVec.shiftLeft_zero]

theorem reg64_rsp (u : RamState) : AddrMode.reg64 4 u = stackPtr u := by
  simp [AddrMode.reg64, Operand.read, stackPtr]

theorem load_slot [Bindings] {boundary : ReturnBoundary}
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat)
    {sp st input output : BitVec 64} {size : Nat} {u : RamState} (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (hsp : Space sp st input output size u)
    (p q : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (d : Disp)
    (off : Nat) (hd : d.value = BitVec.ofNat 64 off) (hoff : off + 8 ≤ frameBytes)
    (hv : (AddrMode.sib 4 none 0 d).Valid)
    (hx : rexX rex.toBitVec = (AddrMode.sib 4 none 0 d).rexX)
    (hbx : rexB rex.toBitVec = (AddrMode.sib 4 none 0 d).rexB)
    (hcode : CodeIn (codeRange p (rex :: 0x8B :: (AddrMode.sib 4 none 0 d).modrm reg ::
      (AddrMode.sib 4 none 0 d).tail)) u) (hip : u.RIP = p)
    (hq : p + BitVec.ofNat 64 (movLoadLen (AddrMode.sib 4 none 0 d)) = q)
    (hq1 : 0x100a80 ≤ q.toNat) (hq2 : q.toNat < 0x1014bc) :
    ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      AgreesExcept [.reg (gprNumber 0 (rexR rex.toBitVec) reg), .rip] u v ∧ v.RIP = q ∧
      (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read v = slot64 u sp off := by
  have ha : AddrMode.addr (.sib 4 none 0 d) u q = sp + BitVec.ofNat 64 off := by
    simp only [AddrMode.addr]
    rw [reg64_rsp, hsp.rsp, hd]
  obtain ⟨v, a, r, c, e⟩ := step (mov_r64_m64_effect_step p rex hrex reg (.sib 4 none 0 d) hv hx hbx)
    hr hc hcode ⟨hip, by rw [hq, ha]; exact (writable_slice hsp.stack off 8 hoff).readable⟩
    (by intro he; apply ne_boundary hb hq1 hq2; rw [← hq]; exact he)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  refine ⟨v, a, r, c, by simpa using e.agrees, e.rip.trans hq, ?_⟩
  have hw := e.writes
  simp only [movR64M64Effect, Write.AllHold] at hw
  rw [hw, hq, ha]
  rfl

theorem slot_ext {t u : RamState} (hx : u.external = t.external) (sp : BitVec 64) (off : Nat) :
    slot64 u sp off = slot64 t sp off := by
  unfold slot64; rw [hx]

theorem Slots.ext {sp st input output : BitVec 64} {size : Nat} {t u : RamState}
    (h : Slots sp st input output size t) (hx : u.external = t.external) :
    Slots sp st input output size u :=
  ⟨(slot_ext hx _ _).trans h.state, (slot_ext hx _ _).trans h.output,
    (slot_ext hx _ _).trans h.input, (slot_ext hx _ _).trans h.head,
    (slot_ext hx _ _).trans h.tail, (slot_ext hx _ _).trans h.length⟩

theorem and60 (n : Nat) : n &&& 60 = n % 64 - n % 64 % 4 := by
  have h1 : n &&& 60 = (n % 64) &&& 60 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.testBit_and, Nat.testBit_and, Nat.testBit_mod_two_pow]
    by_cases hi : i < 6
    · simp [hi]
    · have h60 : Nat.testBit 60 i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 60 < 2 ^ 6)
          (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h60]
  rw [h1]
  have hm : n % 64 < 64 := Nat.mod_lt _ (by decide)
  generalize n % 64 = m at hm ⊢
  revert m
  decide

def RoundScratch (m : Nat) : Prop :=
  (4 ≤ m ∧ m < 12) ∨ (0x14 ≤ m ∧ m < 0x18) ∨ (0x58 ≤ m ∧ m < 0x60) ∨ (0x78 ≤ m ∧ m < 0x7c)

theorem tail_scratch_nc {sp y : BitVec 64}
    (hy : ∀ (o : BitVec 64) (j : Nat), o.toNat + j < 0x80 → RoundScratch (o.toNat + j) →
      y ≠ sp + o + BitVec.ofNat 64 j) :
    ∀ c ∈ Rounds.tailScratch sp, ¬ c.Covers y := by
  intro c hc hcv
  simp only [Rounds.tailScratch, Rounds.tailQR, Rounds.regScratch, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | (h | h | h | h)) | h <;> subst h <;>
    simp only [Component.Covers] at hcv
  all_goals obtain ⟨j, hj, he⟩ := hcv
  all_goals exact hy _ j (by simp; omega) (by unfold RoundScratch; simp; omega) he

theorem add_toNat (sp o : BitVec 64) (j : Nat) :
    sp + o + BitVec.ofNat 64 j = sp + BitVec.ofNat 64 (o.toNat + j) := by
  bv_omega

theorem stack_ne (sp : BitVec 64) {m j : Nat} {o : BitVec 64} (h : m ≠ o.toNat + j)
    (hm : m < 2 ^ 63) (hoj : o.toNat + j < 2 ^ 63) :
    sp + BitVec.ofNat 64 m ≠ sp + o + BitVec.ofNat 64 j := by
  intro he
  rw [BitVec.add_assoc] at he
  have := congrArg BitVec.toNat ((BitVec.add_right_inj sp).mp he)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

theorem off_scratch {sp : BitVec 64} {m : Nat} (hm : m < 2 ^ 32) (hd : ¬ RoundScratch m) :
    ∀ c ∈ Rounds.tailScratch sp, ¬ c.Covers (sp + BitVec.ofNat 64 m) :=
  tail_scratch_nc fun o j h1 h2 ↦ stack_ne sp (fun he ↦ hd (he ▸ h2)) (by omega) (by omega)

theorem slot_keep {t u : RamState} {sp : BitVec 64} {cs : List Component} (n : Nat)
    (hag : AgreesExcept cs t u) (off : Nat)
    (h : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (sp + BitVec.ofNat 64 (off + i))) :
    memLoad u.external (slot sp off) n = memLoad t.external (slot sp off) n :=
  Rounds.read_mem_agrees (n := n) hag fun i hi ↦ by unfold slot; rw [tail_add]; exact h i hi

theorem serialize_word (x : Vector UInt32 16) (w : Nat) (hw : w < 16) (i : Nat) (hi : i < 4) :
    (serialize x)[4 * w + i]'(by omega) = storedByte x[w].toBitVec i := by
  have e1 : (4 * w + i) / 4 = w := by omega
  have e2 : (4 * w + i) % 4 = i := by omega
  simp only [serialize, Vector.getElem_ofFn, e1, e2]
  apply UInt8.toNat_inj.mp
  simp only [storedByte, UInt8.toNat_ofNat', UInt32.toNat_toUInt8, UInt32.toNat_shiftRight]
  have : (8 * i).toUInt32.toNat % 32 = 8 * i := by simp [Nat.toUInt32]; omega
  rw [this]
  rfl

theorem load_word {t : RamState} {st : BitVec 64} {x : Vector UInt32 16}
    (h : BytesAt st (serialize x) t) (w : Nat) (hw : w < 16) :
    memLoad t.external (st + BitVec.ofNat 64 (4 * w)) 32 = x[w].toBitVec := by
  apply memLoad_eq_of_memByte (by decide)
  intro i hi
  rw [← serialize_word x w hw i (by omega), memByte, tail_add]
  simp only [PhysicalMemory.read]
  rw [h ⟨4 * w + i, by omega⟩]
  rfl

theorem mask_base (size : Nat) (hs : size < 2 ^ 64) :
    BitVec.ofNat 64 size &&& 0xffffffffffffffc0 = BitVec.ofNat 64 (base size) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
  rw [Nat.mod_eq_of_lt (by unfold base; omega)]
  have hm : (0xffffffffffffffc0 : BitVec 64).toNat = (2 ^ 58 - 1) <<< 6 := by decide
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro i
  have hb : base size = (size >>> 6) <<< 6 := by
    unfold base; rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega
  rw [hb, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h6 : 6 ≤ i
  · rw [show 6 + (i - 6) = i by omega]
    by_cases ht : size.testBit i
    · have h64 : i < 64 := by
        rcases Nat.lt_or_ge i 64 with h | h
        · exact h
        · have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) h))
          rw [ht] at this; exact absurd this (by decide)
      simp [h6, ht]; omega
    · simp [ht]
  · simp [h6]

theorem rspOf_eq (u : RamState) : rspOf u = stackPtr u := by
  simp [rspOf, Operand.read, stackPtr]

theorem store_keeps_state {st : BitVec 64} {u v : RamState} {o o' : Nat}
    (g : AgreesExcept [.mem (st + BitVec.ofNat 64 o') 4, .rip] u v) (hst : st.toNat + 0x80 ≤ 2 ^ 32)
    (ho : o + 4 ≤ 0x80) (ho' : o' + 4 ≤ 0x80) (h : o + 4 ≤ o' ∨ o' + 4 ≤ o) :
    memLoad v.external (st + BitVec.ofNat 64 o) 32 = memLoad u.external (st + BitVec.ofNat 64 o) 32 := by
  apply memLoad_congr
  intro i hi
  simp only [memByte]
  congr 1
  refine g.byte fun c hc hcv ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hcv
    rw [tail_add, tail_add] at he
    exact add_ofNat_ne (a := st) (i := o + i) (k := o' + j) (by omega) (by omega) (by omega) he
  · exact hcv

theorem store_keeps_stack {sp st : BitVec 64} {u v : RamState} {o' off n : Nat}
    (g : AgreesExcept [.mem (st + BitVec.ofNat 64 o') 4, .rip] u v)
    (hap : RangeApart st stateBytes sp frameBytes) (ho' : o' + 4 ≤ 0x80) (hoff : off + n / 8 ≤ 0x170) :
    memLoad v.external (sp + BitVec.ofNat 64 off) n = memLoad u.external (sp + BitVec.ofNat 64 off) n := by
  apply memLoad_congr
  intro i hi
  simp only [memByte]
  congr 1
  refine g.byte fun c hc hcv ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hcv
    rw [tail_add, tail_add] at he
    exact hap _ (by unfold stateBytes; omega) _ (by unfold frameBytes; omega) he.symm
  · exact hcv

theorem store_keeps_far {st y : BitVec 64} {u v : RamState} {o' : Nat}
    (g : AgreesExcept [.mem (st + BitVec.ofNat 64 o') 4, .rip] u v)
    (hy : ∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) (ho' : o' + 4 ≤ 0x80) :
    v.external[y]? = u.external[y]? := by
  refine g.byte fun c hc hcv ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hcv
    rw [tail_add] at he
    exact hy _ (by omega) he
  · exact hcv

theorem storeAddr_base {u : RamState} {st : BitVec 64} (b : BitVec 4) (d : BitVec 8) (off : Nat)
    (next : BitVec 64) (hb : (Operand.reg (b.setWidth 5) : Operand 64).read u = st)
    (hd : d.signExtend 64 = BitVec.ofNat 64 off) :
    AddrMode.addr (.base b (.d8 d)) u next = st + BitVec.ofNat 64 off := by
  simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
  rw [hb, hd]

end Helpers

section SetupBlocks

open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

structure SFrame (sp st : BitVec 64) (s : RamState) : Prop where
  rsp : rspOf s = sp
  rdi : (Operand.reg 7 : Operand 64).read s = st
  stack : MemWritable s sp 0x80
  code : ∀ i < 0x80, ¬ InProgram (sp + BitVec.ofNat 64 i)
  state : MemReadable s st 0x40

theorem r_slice {s : RamState} {a : BitVec 64} {n : Nat} (h : MemReadable s a n) (off len : Nat)
    (hn : off + len ≤ n) : MemReadable s (a + BitVec.ofNat 64 off) len := by
  have hl := h.low
  refine ⟨by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega, fun i hi => ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h.mem _ (by omega)

macro "sf_frame " hP:ident : tactic => `(tactic| (
  have hF := ($hP).2
  have hS := hF.rsp
  have hD := hF.rdi
  try x86_norm at hS hD
  try x86_norm
  try simp only [hS, hD]
  first
  | exact (Rounds.w_slice hF.stack _ _ (by decide)).readable
  | exact Rounds.w_slice hF.stack _ _ (by decide)
  | exact Rounds.ap_code hF.code _ _ (by decide) _ (by decide) (by decide)
  | exact r_slice hF.state _ _ (by decide)
  | exact hF.state))

macro "sf_begin " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_first ?k $t ?sub ?pre ?av ?boundary
  case sub => first | x86_sub | rr_sub
  case pre =>
    intro s hP
    first
    | exact hP.1
    | exact ⟨hP.1⟩
    | (refine LoadPre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.1
         (by x86_addr_obs) ?_
       sf_frame hP)
    | (refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.1
         (by x86_addr_obs) ?_ ?_ <;> sf_frame hP)
  case av =>
    intro s hP
    first
    | (solve | apply Effect.Avoids.of_noMem; simp [Component.Covers])
    | (x86_avoid
       all_goals sf_frame hP)
  case boundary => rr_bd
  case' k => skip))

macro "sf_then " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case sub => first | x86_sub | rr_sub
  case full =>
    first
    | (intro s _
       apply Effect.Local.full
       repeat' first
         | (solve | x86_local)
         | apply Effect.Local.seq
       done)
    | x86_full
  case mid =>
    intro s s' hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · first
      | exact hH.rip_of (by first | rfl | x86_norm)
      | exact ⟨hH.rip_of (by first | rfl | x86_norm)⟩
      | (refine LoadPre.of_holds hH (hO true) (by first | rfl | x86_norm) (by x86_addr_obs) ?_
         sf_frame hP)
      | (refine StorePre.of_holds hH (hO true) (by first | rfl | x86_norm) (by x86_addr_obs)
           ?_ ?_ <;> sf_frame hP)
    · first
      | (solve | apply Effect.Avoids.of_noMem; simp [Component.Covers])
      | (x86_avoid
         all_goals sf_frame hP)
  case boundary => rr_bd
  case' k => skip))

def setup1Bytes : List UInt8 :=
  [0x49, 0x83, 0xe3, 0xc0, 0x4c, 0x89, 0x5c, 0x24, 0x40, 0x8b, 0x1f, 0x44, 0x8b, 0x6f, 0x4, 0x8b, 0x77, 0x8, 0x8b, 0x47, 0xc, 0x89, 0x44, 0x24, 0xc, 0x44, 0x8b, 0x4f, 0x10, 0x8b, 0x6f, 0x14, 0x44, 0x8b, 0x7f, 0x18, 0x8b, 0x47, 0x1c]

def setup1Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (andR64Imm8Effect 0x1010d5 11 0xc0) (movM64R64Effect 0x1010d9 11 (.sib 4 none 0 (.d8 0x40)))) (movR32M32LowEffect 0x1010de 3 (.base 7 .none))) (movR32M32Effect 0x1010e0 13 (.base 7 (.d8 0x4)))) (movR32M32LowEffect 0x1010e4 6 (.base 7 (.d8 0x8)))) (movR32M32LowEffect 0x1010e7 0 (.base 7 (.d8 0xc)))) (movM32R32LowEffect 0x1010ea 0 (.sib 4 none 0 (.d8 0xc)))) (movR32M32Effect 0x1010ee 9 (.base 7 (.d8 0x10)))) (movR32M32LowEffect 0x1010f2 5 (.base 7 (.d8 0x14)))) (movR32M32Effect 0x1010f5 15 (.base 7 (.d8 0x18)))) (movR32M32LowEffect 0x1010f9 0 (.base 7 (.d8 0x1c))))

theorem setup1Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp st : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1010d5 ∧ SFrame sp st s)
      (codeRange 0x1010d5 setup1Bytes) setup1Effect := by
  unfold setup1Bytes
  sf_begin (and_r64_imm8_effect_step 0x1010d5 0x49 0xe3 0xc0 (by unfold RexWPrefix; decide) (by decide) (by decide))
  sf_then (mov_m64_r64_effect_step 0x1010d9 0x4c (by unfold RexWPrefix; decide) 3 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_low_effect_step 0x1010de 3 (.base 7 .none) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_effect_step 0x1010e0 0x44 (by unfold RexNoWPrefix; decide) 5 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_low_effect_step 0x1010e4 6 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_low_effect_step 0x1010e7 0 (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide))
  sf_then (mov_m32_r32_low_effect_step 0x1010ea 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_effect_step 0x1010ee 0x44 (by unfold RexNoWPrefix; decide) 1 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_low_effect_step 0x1010f2 5 (.base 7 (.d8 0x14)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_effect_step 0x1010f5 0x44 (by unfold RexNoWPrefix; decide) 7 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_low_effect_step 0x1010f9 0 (.base 7 (.d8 0x1c)) (by decide) (by decide) (by decide))
  rr_finish

def setup2Bytes : List UInt8 :=
  [0x89, 0x44, 0x24, 0x10, 0x8b, 0x47, 0x20, 0x44, 0x8b, 0x57, 0x24, 0x44, 0x8b, 0x77, 0x28, 0x44, 0x8b, 0x67, 0x2c, 0x8b, 0x4f, 0x30, 0x8b, 0x57, 0x34, 0x44, 0x8b, 0x47, 0x38, 0x44, 0x8b, 0x5f, 0x3c, 0xbf, 0xa, 0x0, 0x0, 0x0]

def setup2Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (movM32R32LowEffect 0x1010fc 0 (.sib 4 none 0 (.d8 0x10))) (movR32M32LowEffect 0x101100 0 (.base 7 (.d8 0x20)))) (movR32M32Effect 0x101103 10 (.base 7 (.d8 0x24)))) (movR32M32Effect 0x101107 14 (.base 7 (.d8 0x28)))) (movR32M32Effect 0x10110b 12 (.base 7 (.d8 0x2c)))) (movR32M32LowEffect 0x10110f 1 (.base 7 (.d8 0x30)))) (movR32M32LowEffect 0x101112 2 (.base 7 (.d8 0x34)))) (movR32M32Effect 0x101115 8 (.base 7 (.d8 0x38)))) (movR32M32Effect 0x101119 11 (.base 7 (.d8 0x3c)))) (movR32Imm32Effect 0x10111d 5 7 0xa))

theorem setup2Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp st : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1010fc ∧ SFrame sp st s)
      (codeRange 0x1010fc setup2Bytes) setup2Effect := by
  unfold setup2Bytes
  sf_begin (mov_m32_r32_low_effect_step 0x1010fc 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_low_effect_step 0x101100 0 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_effect_step 0x101103 0x44 (by unfold RexNoWPrefix; decide) 2 (.base 7 (.d8 0x24)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_effect_step 0x101107 0x44 (by unfold RexNoWPrefix; decide) 6 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_effect_step 0x10110b 0x44 (by unfold RexNoWPrefix; decide) 4 (.base 7 (.d8 0x2c)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_low_effect_step 0x10110f 1 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_low_effect_step 0x101112 2 (.base 7 (.d8 0x34)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_effect_step 0x101115 0x44 (by unfold RexNoWPrefix; decide) 0 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_m32_effect_step 0x101119 0x44 (by unfold RexNoWPrefix; decide) 3 (.base 7 (.d8 0x3c)) (by decide) (by decide) (by decide))
  sf_then (mov_r32_imm32_effect_step 0x10111d 0xbf (by decide) 0xa)
  rr_finish

def setup3Bytes : List UInt8 :=
  [0x48, 0x89, 0x7c, 0x24, 0x58, 0x89, 0x5c, 0x24, 0x38, 0x89, 0x5c, 0x24, 0x8, 0x44, 0x89, 0x4c, 0x24, 0x50, 0x89, 0x4c, 0x24, 0x34, 0x89, 0x44, 0x24, 0x18]

def setup3Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (movM64R64Effect 0x101122 7 (.sib 4 none 0 (.d8 0x58))) (movM32R32LowEffect 0x101127 3 (.sib 4 none 0 (.d8 0x38)))) (movM32R32LowEffect 0x10112b 3 (.sib 4 none 0 (.d8 0x8)))) (movM32R32Effect 0x10112f 9 (.sib 4 none 0 (.d8 0x50)))) (movM32R32LowEffect 0x101134 1 (.sib 4 none 0 (.d8 0x34)))) (movM32R32LowEffect 0x101138 0 (.sib 4 none 0 (.d8 0x18))))

theorem setup3Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x101122 ∧ Rounds.RFrame sp s)
      (codeRange 0x101122 setup3Bytes) setup3Effect := by
  unfold setup3Bytes
  rr_begin (mov_m64_r64_effect_step 0x101122 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x101127 3 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x10112b 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x10112f 0x44 (by unfold RexNoWPrefix; decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x101134 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x101138 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
  rr_finish

def setup4Bytes : List UInt8 :=
  [0x89, 0x44, 0x24, 0x4, 0x44, 0x89, 0x6c, 0x24, 0x60, 0x89, 0x6c, 0x24, 0x70, 0x89, 0x54, 0x24, 0x28, 0x44, 0x89, 0x54, 0x24, 0x1c, 0x89, 0x74, 0x24, 0x68]

def setup4Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (movM32R32LowEffect 0x10113c 0 (.sib 4 none 0 (.d8 0x4))) (movM32R32Effect 0x101140 13 (.sib 4 none 0 (.d8 0x60)))) (movM32R32LowEffect 0x101145 5 (.sib 4 none 0 (.d8 0x70)))) (movM32R32LowEffect 0x101149 2 (.sib 4 none 0 (.d8 0x28)))) (movM32R32Effect 0x10114d 10 (.sib 4 none 0 (.d8 0x1c)))) (movM32R32LowEffect 0x101152 6 (.sib 4 none 0 (.d8 0x68))))

theorem setup4Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x10113c ∧ Rounds.RFrame sp s)
      (codeRange 0x10113c setup4Bytes) setup4Effect := by
  unfold setup4Bytes
  rr_begin (mov_m32_r32_low_effect_step 0x10113c 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x101140 0x44 (by unfold RexNoWPrefix; decide) 5 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x101145 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x101149 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x10114d 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x101152 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide))
  rr_finish

def setup5Bytes : List UInt8 :=
  [0x89, 0xf0, 0x44, 0x89, 0x7c, 0x24, 0x3c, 0x44, 0x89, 0x44, 0x24, 0x2c, 0x44, 0x89, 0x74, 0x24, 0x20, 0x8b, 0x7c, 0x24, 0xc, 0x8b, 0x74, 0x24, 0x10, 0x44, 0x89, 0x5c, 0x24, 0x30, 0x44, 0x89, 0x64, 0x24, 0x24]

def setup5Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (movR32R32Effect 0x101156 2 0 6) (movM32R32Effect 0x101158 15 (.sib 4 none 0 (.d8 0x3c)))) (movM32R32Effect 0x10115d 8 (.sib 4 none 0 (.d8 0x2c)))) (movM32R32Effect 0x101162 14 (.sib 4 none 0 (.d8 0x20)))) (movR32M32LowEffect 0x101167 7 (.sib 4 none 0 (.d8 0xc)))) (movR32M32LowEffect 0x10116b 6 (.sib 4 none 0 (.d8 0x10)))) (movM32R32Effect 0x10116f 11 (.sib 4 none 0 (.d8 0x30)))) (movM32R32Effect 0x101174 12 (.sib 4 none 0 (.d8 0x24))))

theorem setup5Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x101156 ∧ Rounds.RFrame sp s)
      (codeRange 0x101156 setup5Bytes) setup5Effect := by
  unfold setup5Bytes
  rr_begin (mov_r32_r32_effect_step 0x101156 0xf0 (by decide))
  rr_then (mov_m32_r32_effect_step 0x101158 0x44 (by unfold RexNoWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x10115d 0x44 (by unfold RexNoWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x101162 0x44 (by unfold RexNoWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x101167 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x10116b 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x10116f 0x44 (by unfold RexNoWPrefix; decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x101174 0x44 (by unfold RexNoWPrefix; decide) 4 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide))
  rr_finish

theorem write_reg_external (s : RamState) {n : Nat} (r : BitVec 5) (v : BitVec n) :
    (Operand.write s (Operand.reg r) v).external = s.external := rfl

theorem write_mem_external (s : RamState) {n : Nat} (a : BitVec 64) (v : BitVec n) :
    (Operand.write s (Operand.mem a) v).external = memStore s.external a v := rfl

def StackStateApart (sp st : BitVec 64) : Prop :=
  ∀ (m : Ram) (o₁ o₂ : BitVec 64) (n : Nat) (v : BitVec n) (k : Nat),
    o₁.toNat + n / 8 ≤ 0x80 → o₂.toNat + k / 8 ≤ 0x40 →
    memLoad (memStore m (sp + o₁) v) (st + o₂) k = memLoad m (st + o₂) k

theorem stackStateApart {sp st : BitVec 64} (h : RangeApart st stateBytes sp frameBytes) :
    StackStateApart sp st := by
  intro m o₁ o₂ n v k h1 h2
  apply memLoad_memStore_of_rangeApart
  intro i hi j hj he
  have hk : st + o₂ + BitVec.ofNat 64 j = st + BitVec.ofNat 64 (o₂.toNat + j) := add_toNat _ _ _
  have hk' : sp + o₁ + BitVec.ofNat 64 i = sp + BitVec.ofNat 64 (o₁.toNat + i) := add_toNat _ _ _
  rw [hk, hk'] at he
  exact h _ (by unfold stateBytes; omega) _ (by unfold frameBytes; omega) he.symm

def stL : List (Fin 16 × Rounds.Loc) :=
  [(0, .slot 0), (1, .slot 4), (2, .slot 8), (3, .slot 0xc), (4, .slot 0x10), (5, .slot 0x14),
    (6, .slot 0x18), (7, .slot 0x1c), (8, .slot 0x20), (9, .slot 0x24), (10, .slot 0x28),
    (11, .slot 0x2c), (12, .slot 0x30), (13, .slot 0x34), (14, .slot 0x38), (15, .slot 0x3c)]

def setupL1 : List (Fin 16 × Rounds.Loc) :=
  [(0, .reg 3), (1, .reg 13), (2, .reg 6), (3, .slot 0xc), (4, .reg 9), (5, .reg 5), (6, .reg 15), (7, .reg 0)]
def setupL2 : List (Fin 16 × Rounds.Loc) :=
  [(0, .reg 3), (1, .reg 13), (2, .reg 6), (3, .slot 0xc), (4, .reg 9), (5, .reg 5), (6, .reg 15), (7, .slot 0x10), (8, .reg 0), (9, .reg 10), (10, .reg 14), (11, .reg 12), (12, .reg 1), (13, .reg 2), (14, .reg 8), (15, .reg 11)]
def setupL3 : List (Fin 16 × Rounds.Loc) :=
  [(0, .reg 3), (1, .reg 13), (2, .reg 6), (3, .slot 0xc), (4, .reg 9), (5, .reg 5), (6, .reg 15), (7, .slot 0x10), (8, .reg 0), (9, .reg 10), (10, .reg 14), (11, .reg 12), (12, .reg 1), (13, .reg 2), (14, .reg 8), (15, .reg 11), (0, .slot 0x38), (0, .slot 0x8), (4, .slot 0x50), (12, .slot 0x34), (8, .slot 0x18)]
def setupL4 : List (Fin 16 × Rounds.Loc) :=
  [(0, .reg 3), (1, .reg 13), (2, .reg 6), (3, .slot 0xc), (4, .reg 9), (5, .reg 5), (6, .reg 15), (7, .slot 0x10), (8, .reg 0), (9, .reg 10), (10, .reg 14), (11, .reg 12), (12, .reg 1), (13, .reg 2), (14, .reg 8), (15, .reg 11), (0, .slot 0x38), (0, .slot 0x8), (4, .slot 0x50), (12, .slot 0x34), (8, .slot 0x18), (8, .slot 0x4), (1, .slot 0x60), (5, .slot 0x70), (13, .slot 0x28), (9, .slot 0x1c), (2, .slot 0x68)]
def setupInit : List (Fin 16 × Rounds.Loc) :=
  [(0, .slot 0x38), (1, .slot 0x60), (2, .slot 0x68), (3, .slot 0xc), (4, .slot 0x50), (5, .slot 0x70), (6, .slot 0x3c), (7, .slot 0x10), (8, .slot 0x18), (9, .slot 0x1c), (10, .slot 0x20), (11, .slot 0x24), (12, .slot 0x34), (13, .slot 0x28), (14, .slot 0x2c), (15, .slot 0x30)]

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem setup1Words {sp st R : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = sp) (hd : (Operand.reg 7 : Operand 64).read s = st) (hap : StackStateApart sp st) (hst : Write.AllHold s (Rounds.cut st stL x)) (hw : Write.AllHold s (Rounds.cut sp ([] : List (Fin 16 × Rounds.Loc)) x ++ [⟨(Operand.reg 11 : Operand 64), R⟩, ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩]))
    (he : (setup1Effect s).Holds s t) :
    Write.AllHold t (Rounds.cut sp setupL1 x ++ [⟨(Operand.mem (sp + 0x40) : Operand 64), R &&& 0xffffffffffffffc0⟩, ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩, ⟨(Operand.reg 7 : Operand 64), st⟩]) := by
  have hfull : ∀ w ∈ (setup1Effect s).writes, w.Full := by x86_norm [setup1Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs hd
  simp only [Rounds.cut, setupL1, Rounds.tailBase, setupInit, stL, List.map, Rounds.Loc.op, List.cons_append, List.nil_append, List.append_nil, Write.AllHold, List.append_assoc] at hst hw ⊢
  obtain ⟨h0, h1⟩ := hw
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hst
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [setup1Effect, hs, hd]
  x86_norm at h0 h1 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
  unfold StackStateApart at hap
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    and_true, hap, write_reg_external, write_mem_external]
  x86_norm
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, and_true]

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem setup2Words {sp st R : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = sp) (hd : (Operand.reg 7 : Operand 64).read s = st) (hap : StackStateApart sp st) (hst : Write.AllHold s (Rounds.cut st stL x)) (hw : Write.AllHold s (Rounds.cut sp setupL1 x ++ [⟨(Operand.mem (sp + 0x40) : Operand 64), R &&& 0xffffffffffffffc0⟩, ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩, ⟨(Operand.reg 7 : Operand 64), st⟩]))
    (he : (setup2Effect s).Holds s t) :
    Write.AllHold t (Rounds.cut sp setupL2 x ++ [⟨(Operand.mem (sp + 0x40) : Operand 64), R &&& 0xffffffffffffffc0⟩, ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩, ⟨(Operand.reg 7 : Operand 64), 0xa⟩]) := by
  have hfull : ∀ w ∈ (setup2Effect s).writes, w.Full := by x86_norm [setup2Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs hd
  simp only [Rounds.cut, setupL1, setupL2, Rounds.tailBase, setupInit, stL, List.map, Rounds.Loc.op, List.cons_append, List.nil_append, List.append_nil, Write.AllHold, List.append_assoc] at hst hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hw
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hst
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [setup2Effect, hs, hd]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
  unfold StackStateApart at hap
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    and_true, hap, write_reg_external, write_mem_external]
  x86_norm
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, and_true]

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem setup3Words {sp st R : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = sp) (hw : Write.AllHold s (Rounds.cut sp setupL2 x ++ [⟨(Operand.mem (sp + 0x40) : Operand 64), R &&& 0xffffffffffffffc0⟩, ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩, ⟨(Operand.reg 7 : Operand 64), 0xa⟩]))
    (he : (setup3Effect s).Holds s t) :
    Write.AllHold t (Rounds.cut sp setupL3 x ++ [⟨(Operand.mem (sp + 0x40) : Operand 64), R &&& 0xffffffffffffffc0⟩, ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩, ⟨(Operand.mem (sp + 0x58) : Operand 64), 0xa⟩]) := by
  have hfull : ∀ w ∈ (setup3Effect s).writes, w.Full := by x86_norm [setup3Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [Rounds.cut, setupL2, setupL3, Rounds.tailBase, setupInit, stL, List.map, Rounds.Loc.op, List.cons_append, List.nil_append, List.append_nil, Write.AllHold, List.append_assoc] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [setup3Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, and_true]

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem setup4Words {sp st R : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = sp) (hw : Write.AllHold s (Rounds.cut sp setupL3 x ++ [⟨(Operand.mem (sp + 0x40) : Operand 64), R &&& 0xffffffffffffffc0⟩, ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩, ⟨(Operand.mem (sp + 0x58) : Operand 64), 0xa⟩]))
    (he : (setup4Effect s).Holds s t) :
    Write.AllHold t (Rounds.cut sp setupL4 x ++ [⟨(Operand.mem (sp + 0x40) : Operand 64), R &&& 0xffffffffffffffc0⟩, ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩, ⟨(Operand.mem (sp + 0x58) : Operand 64), 0xa⟩]) := by
  have hfull : ∀ w ∈ (setup4Effect s).writes, w.Full := by x86_norm [setup4Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [Rounds.cut, setupL3, setupL4, Rounds.tailBase, setupInit, stL, List.map, Rounds.Loc.op, List.cons_append, List.nil_append, List.append_nil, Write.AllHold, List.append_assoc] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [setup4Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, and_true]

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem setup5Words {sp st R : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = sp) (hw : Write.AllHold s (Rounds.cut sp setupL4 x ++ [⟨(Operand.mem (sp + 0x40) : Operand 64), R &&& 0xffffffffffffffc0⟩, ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩, ⟨(Operand.mem (sp + 0x58) : Operand 64), 0xa⟩]))
    (he : (setup5Effect s).Holds s t) :
    Write.AllHold t (Rounds.cut sp (Rounds.tailBase ++ setupInit) x ++ [⟨(Operand.mem (sp + 0x40) : Operand 64), R &&& 0xffffffffffffffc0⟩, ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩, ⟨(Operand.mem (sp + 0x58) : Operand 64), 0xa⟩]) := by
  have hfull : ∀ w ∈ (setup5Effect s).writes, w.Full := by x86_norm [setup5Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [Rounds.cut, setupL4, Rounds.tailBase, setupInit, stL, List.map, Rounds.Loc.op, List.cons_append, List.nil_append, List.append_nil, Write.AllHold, List.append_assoc] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [setup5Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, and_true]

def setupScratch (sp : BitVec 64) : List Component :=
  Rounds.regScratch ++ [.mem (sp + 0x40) 8, .mem (sp + 0xc) 4, .mem (sp + 0x10) 4,
    .mem (sp + 0x58) 8, .mem (sp + 0x38) 4, .mem (sp + 0x8) 4, .mem (sp + 0x50) 4,
    .mem (sp + 0x34) 4, .mem (sp + 0x18) 4, .mem (sp + 0x4) 4, .mem (sp + 0x60) 4,
    .mem (sp + 0x70) 4, .mem (sp + 0x28) 4, .mem (sp + 0x1c) 4, .mem (sp + 0x68) 4,
    .mem (sp + 0x3c) 4, .mem (sp + 0x2c) 4, .mem (sp + 0x20) 4, .mem (sp + 0x30) 4,
    .mem (sp + 0x24) 4]

theorem setupScratch_good (sp : BitVec 64) : Rounds.Good sp (setupScratch sp) := by
  refine ⟨by simp [setupScratch, Rounds.regScratch], ?_⟩
  simp only [setupScratch, Rounds.regScratch, List.cons_append, List.nil_append,
    List.forall_mem_cons]
  repeat' apply And.intro
  all_goals (intro x hx; first | exact hx.elim | exact Rounds.mem_good (by decide) hx | simp at hx)

theorem run_block [Bindings] {boundary : ReturnBoundary} {p q sp : BitVec 64} {bytes : List UInt8}
    {eff : RamState → Effect} {P : RamState → Prop}
    (hBlock : AdvancesBlock boundary P (codeRange p bytes) eff)
    (hText : ∀ s, CodeIn Extracted.programImage s → CodeIn (codeRange p bytes) s)
    (hRip : ∀ s t, (eff s).Holds s t → t.RIP = q)
    (hAg : ∀ s t, rspOf s = sp → (eff s).Holds s t → AgreesExcept (setupScratch sp) s t)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hP : P s)
    (hrf : Rounds.RFrame sp s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = q ∧ Rounds.RFrame sp t ∧ AgreesExcept (setupScratch sp) s t ∧ (eff s).Holds s t := by
  obtain ⟨fuel, t, ha, hr', _, he⟩ := hBlock s hr (hText s hc) hP
  have hag := hAg s t hrf.rsp he
  exact ⟨fuel, t, ha, hr', hrf.codeIn (setupScratch_good sp) hag hc, hRip s t he,
    hrf.of_agrees (setupScratch_good sp) hag, hag, he⟩

theorem setup1Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp st : BitVec 64)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hP : (fun s => s.RIP = 0x1010d5 ∧ SFrame sp st s) s) (hrf : Rounds.RFrame sp s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x1010fc ∧ Rounds.RFrame sp t ∧ AgreesExcept (setupScratch sp) s t ∧
      (setup1Effect s).Holds s t := by
  refine run_block (setup1Block boundary hb sp st) ?_ ?_ ?_ hr hc hP hrf
  · intro s hc
    have h := MemoryRoutines.Machine.program_text_slice hc 0x10d5 39 (by rw [Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x10d5 39 = setup1Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x10d5 = 0x1010d5 from by decide] at h
  · intro s t he
    exact he.rip.trans (by x86_norm [setup1Effect])
  · intro s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [setup1Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [setupScratch, Rounds.regScratch])

theorem setup2Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp st : BitVec 64)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hP : (fun s => s.RIP = 0x1010fc ∧ SFrame sp st s) s) (hrf : Rounds.RFrame sp s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101122 ∧ Rounds.RFrame sp t ∧ AgreesExcept (setupScratch sp) s t ∧
      (setup2Effect s).Holds s t := by
  refine run_block (setup2Block boundary hb sp st) ?_ ?_ ?_ hr hc hP hrf
  · intro s hc
    have h := MemoryRoutines.Machine.program_text_slice hc 0x10fc 38 (by rw [Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x10fc 38 = setup2Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x10fc = 0x1010fc from by decide] at h
  · intro s t he
    exact he.rip.trans (by x86_norm [setup2Effect])
  · intro s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [setup2Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [setupScratch, Rounds.regScratch])

theorem setup3Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hP : (fun s => s.RIP = 0x101122 ∧ Rounds.RFrame sp s) s) (hrf : Rounds.RFrame sp s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x10113c ∧ Rounds.RFrame sp t ∧ AgreesExcept (setupScratch sp) s t ∧
      (setup3Effect s).Holds s t := by
  refine run_block (setup3Block boundary hb sp) ?_ ?_ ?_ hr hc hP hrf
  · intro s hc
    have h := MemoryRoutines.Machine.program_text_slice hc 0x1122 26 (by rw [Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x1122 26 = setup3Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x1122 = 0x101122 from by decide] at h
  · intro s t he
    exact he.rip.trans (by x86_norm [setup3Effect])
  · intro s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [setup3Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [setupScratch, Rounds.regScratch])

theorem setup4Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hP : (fun s => s.RIP = 0x10113c ∧ Rounds.RFrame sp s) s) (hrf : Rounds.RFrame sp s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101156 ∧ Rounds.RFrame sp t ∧ AgreesExcept (setupScratch sp) s t ∧
      (setup4Effect s).Holds s t := by
  refine run_block (setup4Block boundary hb sp) ?_ ?_ ?_ hr hc hP hrf
  · intro s hc
    have h := MemoryRoutines.Machine.program_text_slice hc 0x113c 26 (by rw [Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x113c 26 = setup4Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x113c = 0x10113c from by decide] at h
  · intro s t he
    exact he.rip.trans (by x86_norm [setup4Effect])
  · intro s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [setup4Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [setupScratch, Rounds.regScratch])

theorem setup5Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hP : (fun s => s.RIP = 0x101156 ∧ Rounds.RFrame sp s) s) (hrf : Rounds.RFrame sp s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101179 ∧ Rounds.RFrame sp t ∧ AgreesExcept (setupScratch sp) s t ∧
      (setup5Effect s).Holds s t := by
  refine run_block (setup5Block boundary hb sp) ?_ ?_ ?_ hr hc hP hrf
  · intro s hc
    have h := MemoryRoutines.Machine.program_text_slice hc 0x1156 35 (by rw [Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x1156 35 = setup5Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x1156 = 0x101156 from by decide] at h
  · intro s t he
    exact he.rip.trans (by x86_norm [setup5Effect])
  · intro s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [setup5Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [setupScratch, Rounds.regScratch])

theorem state_nc {sp st : BitVec 64} (h : RangeApart st stateBytes sp frameBytes) (o : BitVec 64)
    (i : Nat) (ho : o.toNat + i < 0x80) :
    ∀ c ∈ setupScratch sp, ¬ c.Covers (st + o + BitVec.ofNat 64 i) := fun c hc hcv ↦ by
  obtain ⟨j, hj, he⟩ := (setupScratch_good sp).2 c hc _ hcv
  rw [add_toNat] at he
  exact h _ (by unfold stateBytes; omega) j (by unfold frameBytes; omega) he

theorem far_nc {sp y : BitVec 64} (hy : ∀ j < 0x80, y ≠ sp + BitVec.ofNat 64 j) :
    ∀ c ∈ setupScratch sp, ¬ c.Covers y := fun c hc hcv ↦ by
  obtain ⟨j, hj, he⟩ := (setupScratch_good sp).2 c hc y hcv
  exact hy j hj he

theorem stL_keep {sp st : BitVec 64} {x : Vector UInt32 16} {t u : RamState}
    (g : AgreesExcept (setupScratch sp) t u) (hap : RangeApart st stateBytes sp frameBytes)
    (h : Write.AllHold t (Rounds.cut st stL x)) : Write.AllHold u (Rounds.cut st stL x) := by
  refine Rounds.allHold_congr (fun w hw ↦ ?_) h
  simp only [Rounds.cut, List.mem_map] at hw
  obtain ⟨e, he, rfl⟩ := hw
  simp only [stL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
  exact Rounds.read_mem_agrees g (fun i hi ↦ state_nc hap _ i (by simp at hi; simp; omega))

end SetupBlocks

section FeedBlocks

open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

def feed1Bytes : List UInt8 :=
  [0x8b, 0x5c, 0x24, 0x8, 0x3, 0x5c, 0x24, 0x38, 0x89, 0x5c, 0x24, 0x8, 0x44, 0x3, 0x6c, 0x24, 0x60, 0x44, 0x89, 0x6c, 0x24, 0x14, 0x3, 0x44, 0x24, 0x68, 0x3, 0x7c, 0x24, 0xc]

def feed1Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (movR32M32LowEffect 0x1012e3 3 (.sib 4 none 0 (.d8 0x8))) (addR32M32Effect 0x1012e7 4 3 (.sib 4 none 0 (.d8 0x38)))) (movM32R32LowEffect 0x1012eb 3 (.sib 4 none 0 (.d8 0x8)))) (addR32M32Effect 0x1012ef 5 13 (.sib 4 none 0 (.d8 0x60)))) (movM32R32Effect 0x1012f4 13 (.sib 4 none 0 (.d8 0x14)))) (addR32M32Effect 0x1012f9 4 0 (.sib 4 none 0 (.d8 0x68)))) (addR32M32Effect 0x1012fd 4 7 (.sib 4 none 0 (.d8 0xc))))

set_option maxHeartbeats 1000000 in
theorem feed1Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1012e3 ∧ Rounds.RFrame sp s)
      (codeRange 0x1012e3 feed1Bytes) feed1Effect := by
  unfold feed1Bytes
  rr_begin (mov_r32_m32_low_effect_step 0x1012e3 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_effect_step 0x1012e7 3 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x1012eb 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_rex_effect_step 0x1012ef 0x44 (by unfold RexNoWPrefix; decide) 5 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x1012f4 0x44 (by unfold RexNoWPrefix; decide) 5 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_effect_step 0x1012f9 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_effect_step 0x1012fd 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide))
  rr_finish

def feed2Bytes : List UInt8 :=
  [0x44, 0x3, 0x4c, 0x24, 0x50, 0x3, 0x6c, 0x24, 0x70, 0x44, 0x3, 0x7c, 0x24, 0x3c, 0x3, 0x74, 0x24, 0x10, 0x8b, 0x5c, 0x24, 0x4, 0x3, 0x5c, 0x24, 0x18, 0x89, 0x5c, 0x24, 0x4]

def feed2Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32M32Effect 0x101301 5 9 (.sib 4 none 0 (.d8 0x50))) (addR32M32Effect 0x101306 4 5 (.sib 4 none 0 (.d8 0x70)))) (addR32M32Effect 0x10130a 5 15 (.sib 4 none 0 (.d8 0x3c)))) (addR32M32Effect 0x10130f 4 6 (.sib 4 none 0 (.d8 0x10)))) (movR32M32LowEffect 0x101313 3 (.sib 4 none 0 (.d8 0x4)))) (addR32M32Effect 0x101317 4 3 (.sib 4 none 0 (.d8 0x18)))) (movM32R32LowEffect 0x10131b 3 (.sib 4 none 0 (.d8 0x4))))

set_option maxHeartbeats 1000000 in
theorem feed2Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x101301 ∧ Rounds.RFrame sp s)
      (codeRange 0x101301 feed2Bytes) feed2Effect := by
  unfold feed2Bytes
  rr_begin (add_r32_m32_rex_effect_step 0x101301 0x44 (by unfold RexNoWPrefix; decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_effect_step 0x101306 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_rex_effect_step 0x10130a 0x44 (by unfold RexNoWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_effect_step 0x10130f 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x101313 3 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_effect_step 0x101317 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
  rr_then (mov_m32_r32_low_effect_step 0x10131b 3 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_finish

def feed3Bytes : List UInt8 :=
  [0x44, 0x3, 0x54, 0x24, 0x1c, 0x44, 0x3, 0x74, 0x24, 0x20, 0x44, 0x3, 0x64, 0x24, 0x24, 0x3, 0x54, 0x24, 0x28, 0x44, 0x3, 0x44, 0x24, 0x2c, 0x44, 0x3, 0x5c, 0x24, 0x30, 0x8b, 0x5c, 0x24, 0x34, 0x1, 0xd9, 0xff, 0xc3, 0x41, 0x89, 0xdd]

def feed3Effect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (addR32M32Effect 0x10131f 5 10 (.sib 4 none 0 (.d8 0x1c))) (addR32M32Effect 0x101324 5 14 (.sib 4 none 0 (.d8 0x20)))) (addR32M32Effect 0x101329 5 12 (.sib 4 none 0 (.d8 0x24)))) (addR32M32Effect 0x10132e 4 2 (.sib 4 none 0 (.d8 0x28)))) (addR32M32Effect 0x101332 5 8 (.sib 4 none 0 (.d8 0x2c)))) (addR32M32Effect 0x101337 5 11 (.sib 4 none 0 (.d8 0x30)))) (movR32M32LowEffect 0x10133c 3 (.sib 4 none 0 (.d8 0x34)))) (addR32R32Effect 0x101340 2 1 3)) (incR32Effect 0x101342 2 3)) (movR32R32Effect 0x101344 3 13 3))

set_option maxHeartbeats 1000000 in
theorem feed3Block [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x10131f ∧ Rounds.RFrame sp s)
      (codeRange 0x10131f feed3Bytes) feed3Effect := by
  unfold feed3Bytes
  rr_begin (add_r32_m32_rex_effect_step 0x10131f 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_rex_effect_step 0x101324 0x44 (by unfold RexNoWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_rex_effect_step 0x101329 0x44 (by unfold RexNoWPrefix; decide) 4 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_effect_step 0x10132e 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_rex_effect_step 0x101332 0x44 (by unfold RexNoWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide))
  rr_then (add_r32_m32_rex_effect_step 0x101337 0x44 (by unfold RexNoWPrefix; decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x10133c 3 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide))
  rr_then (add_r32_r32_effect_step 0x101340 0xd9 (by decide))
  rr_then (inc_r32_effect_step 0x101342 0xc3 (by decide) (by decide))
  rr_then (mov_r32_r32_rex_effect_step 0x101344 0x41 0xdd (by unfold RexNoWPrefix; decide) (by decide))
  rr_finish

def feedA1 : List (Fin 16 × Rounds.Loc) :=
  [(4, .reg 9), (5, .reg 5), (6, .reg 15), (7, .reg 6), (8, .slot 0x4), (9, .reg 10), (10, .reg 14), (11, .reg 12), (12, .reg 1), (13, .reg 2), (14, .reg 8), (15, .reg 11)]
def feedA2 : List (Fin 16 × Rounds.Loc) :=
  [(9, .reg 10), (10, .reg 14), (11, .reg 12), (12, .reg 1), (13, .reg 2), (14, .reg 8), (15, .reg 11)]
def feedC1 : List (Fin 16 × Rounds.Loc) :=
  [(0, .slot 0x8), (1, .slot 0x14), (2, .reg 0), (3, .reg 7)]
def feedC2 : List (Fin 16 × Rounds.Loc) :=
  [(0, .slot 0x8), (1, .slot 0x14), (2, .reg 0), (3, .reg 7), (4, .reg 9), (5, .reg 5), (6, .reg 15), (7, .reg 6), (8, .slot 0x4)]
def feedC3 : List (Fin 16 × Rounds.Loc) :=
  [(0, .slot 0x8), (1, .slot 0x14), (2, .reg 0), (3, .reg 7), (4, .reg 9), (5, .reg 5), (6, .reg 15), (7, .reg 6), (8, .slot 0x4), (9, .reg 10), (10, .reg 14), (11, .reg 12), (13, .reg 2), (14, .reg 8), (15, .reg 11), (12, .reg 1)]

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem feed1Words {sp : BitVec 64} {m x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = sp) (hw : Write.AllHold s (Rounds.cut sp Rounds.tailBase m ++ Rounds.cut sp setupInit x ++ Rounds.cut sp ([] : List (Fin 16 × Rounds.Loc)) (Vector.ofFn fun i => m[i] + x[i])))
    (he : (feed1Effect s).Holds s t) :
    Write.AllHold t (Rounds.cut sp feedA1 m ++ Rounds.cut sp setupInit x ++ Rounds.cut sp feedC1 (Vector.ofFn fun i => m[i] + x[i])) := by
  have hfull : ∀ w ∈ (feed1Effect s).writes, w.Full := by x86_norm [feed1Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [Rounds.cut, Rounds.tailBase, feedA1, feedC1, setupInit, List.map, Rounds.Loc.op, List.cons_append, List.nil_append,
    List.append_nil, List.append_assoc, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [feed1Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, Vector.getElem_ofFn, UInt32.toBitVec_add, Fin.getElem_fin, Fin.isValue,
    and_true]

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem feed2Words {sp : BitVec 64} {m x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = sp) (hw : Write.AllHold s (Rounds.cut sp feedA1 m ++ Rounds.cut sp setupInit x ++ Rounds.cut sp feedC1 (Vector.ofFn fun i => m[i] + x[i])))
    (he : (feed2Effect s).Holds s t) :
    Write.AllHold t (Rounds.cut sp feedA2 m ++ Rounds.cut sp setupInit x ++ Rounds.cut sp feedC2 (Vector.ofFn fun i => m[i] + x[i])) := by
  have hfull : ∀ w ∈ (feed2Effect s).writes, w.Full := by x86_norm [feed2Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [Rounds.cut, feedA1, feedA2, feedC1, feedC2, setupInit, List.map, Rounds.Loc.op, List.cons_append, List.nil_append,
    List.append_nil, List.append_assoc, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [feed2Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, Vector.getElem_ofFn, UInt32.toBitVec_add, Fin.getElem_fin, Fin.isValue,
    and_true]

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem feed3Words {sp : BitVec 64} {m x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = sp) (hw : Write.AllHold s (Rounds.cut sp feedA2 m ++ Rounds.cut sp setupInit x ++ Rounds.cut sp feedC2 (Vector.ofFn fun i => m[i] + x[i])))
    (he : (feed3Effect s).Holds s t) :
    Write.AllHold t (Rounds.cut sp ([] : List (Fin 16 × Rounds.Loc)) m ++ Rounds.cut sp ([] : List (Fin 16 × Rounds.Loc)) x ++ Rounds.cut sp feedC3 (Vector.ofFn fun i => m[i] + x[i])) := by
  have hfull : ∀ w ∈ (feed3Effect s).writes, w.Full := by x86_norm [feed3Effect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [Rounds.cut, feedA2, feedC2, feedC3, setupInit, List.map, Rounds.Loc.op, List.cons_append, List.nil_append,
    List.append_nil, List.append_assoc, Write.AllHold] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [feed3Effect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, Vector.getElem_ofFn, UInt32.toBitVec_add, Fin.getElem_fin, Fin.isValue,
    and_true]

def feedScratch (sp : BitVec 64) : List Component :=
  Rounds.regScratch ++ [.mem (sp + 0x8) 4, .mem (sp + 0x14) 4, .mem (sp + 0x4) 4]

theorem feedScratch_good (sp : BitVec 64) : Rounds.Good sp (feedScratch sp) := by
  refine ⟨by simp [feedScratch, Rounds.regScratch], ?_⟩
  simp only [feedScratch, Rounds.regScratch, List.cons_append, List.nil_append,
    List.forall_mem_cons]
  repeat' apply And.intro
  all_goals (intro x hx; first | exact hx.elim | exact Rounds.mem_good (by decide) hx | simp at hx)

theorem feed_run [Bindings] {boundary : ReturnBoundary} {p q sp : BitVec 64} {bytes : List UInt8}
    {eff : RamState → Effect}
    (hBlock : AdvancesBlock boundary (fun s => s.RIP = p ∧ Rounds.RFrame sp s) (codeRange p bytes) eff)
    (hText : ∀ s, CodeIn Extracted.programImage s → CodeIn (codeRange p bytes) s)
    (hRip : ∀ s t, (eff s).Holds s t → t.RIP = q)
    (hAg : ∀ s t, rspOf s = sp → (eff s).Holds s t → AgreesExcept (feedScratch sp) s t)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hp : s.RIP = p)
    (hrf : Rounds.RFrame sp s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = q ∧ Rounds.RFrame sp t ∧ AgreesExcept (feedScratch sp) s t ∧ (eff s).Holds s t := by
  obtain ⟨fuel, t, ha, hr', _, he⟩ := hBlock s hr (hText s hc) ⟨hp, hrf⟩
  have hag := hAg s t hrf.rsp he
  exact ⟨fuel, t, ha, hr', hrf.codeIn (feedScratch_good sp) hag hc, hRip s t he,
    hrf.of_agrees (feedScratch_good sp) hag, hag, he⟩

theorem feed1Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : s.RIP = 0x1012e3) (hrf : Rounds.RFrame sp s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101301 ∧ Rounds.RFrame sp t ∧ AgreesExcept (feedScratch sp) s t ∧
      (feed1Effect s).Holds s t := by
  refine feed_run (feed1Block boundary hb sp) ?_ ?_ ?_ hr hc hp hrf
  · intro s hc
    have h := MemoryRoutines.Machine.program_text_slice hc 0x12e3 30 (by rw [Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x12e3 30 = feed1Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x12e3 = 0x1012e3 from by decide] at h
  · intro s t he
    exact he.rip.trans (by x86_norm [feed1Effect])
  · intro s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [feed1Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [feedScratch, Rounds.regScratch])

theorem feed2Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : s.RIP = 0x101301) (hrf : Rounds.RFrame sp s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x10131f ∧ Rounds.RFrame sp t ∧ AgreesExcept (feedScratch sp) s t ∧
      (feed2Effect s).Holds s t := by
  refine feed_run (feed2Block boundary hb sp) ?_ ?_ ?_ hr hc hp hrf
  · intro s hc
    have h := MemoryRoutines.Machine.program_text_slice hc 0x1301 30 (by rw [Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x1301 30 = feed2Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x1301 = 0x101301 from by decide] at h
  · intro s t he
    exact he.rip.trans (by x86_norm [feed2Effect])
  · intro s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [feed2Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [feedScratch, Rounds.regScratch])

theorem feed3Run [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (sp : BitVec 64)
    {s : RamState} (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : s.RIP = 0x10131f) (hrf : Rounds.RFrame sp s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101347 ∧ Rounds.RFrame sp t ∧ AgreesExcept (feedScratch sp) s t ∧
      (feed3Effect s).Holds s t := by
  refine feed_run (feed3Block boundary hb sp) ?_ ?_ ?_ hr hc hp hrf
  · intro s hc
    have h := MemoryRoutines.Machine.program_text_slice hc 0x131f 40 (by rw [Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0x131f 40 = feed3Bytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0x131f = 0x10131f from by decide] at h
  · intro s t he
    exact he.rip.trans (by x86_norm [feed3Effect])
  · intro s t hs he
    have ha := he.agrees
    x86_norm at hs
    x86_norm [feed3Effect, hs] at ha
    exact ha.mono (by simp (config := {decide := true}) [feedScratch, Rounds.regScratch])

theorem reg32_eq (r : BitVec 5) (s : RamState) :
    (Operand.reg r : Operand 32).read s = ((Operand.reg r : Operand 64).read s).setWidth 32 := by
  simp [Operand.read]

theorem words_block {u : RamState} {st : BitVec 64} {y : Vector UInt32 16}
    (hw : MemWritable u st 0x80)
    (h : ∀ i < 16, memLoad u.external (st + BitVec.ofNat 64 (0x40 + 4 * i)) 32 = y[i]!.toBitVec) :
    BytesAt (st + 0x40) (serialize y) u := by
  intro j
  have hj := j.isLt
  have hm := storedByte_memLoad u.external (st + BitVec.ofNat 64 (0x40 + 4 * (j.val / 4)))
    (n := 32) (j.val % 4) (by omega)
  rw [h _ (by omega), tail_add] at hm
  have hs := hw.mem (0x40 + 4 * (j.val / 4) + j.val % 4) (by omega)
  have ha : st + 0x40 + BitVec.ofNat 64 j.val =
      st + BitVec.ofNat 64 (0x40 + 4 * (j.val / 4) + j.val % 4) := by
    rw [show 0x40 + 4 * (j.val / 4) + j.val % 4 = 0x40 + j.val by omega, addB]
  rw [ha]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
  rw [hb]
  simp only [memByte, PhysicalMemory.read, hb, Option.getD_some] at hm
  rw [← hm, getElem!_pos y (j.val / 4) (by omega)]
  have := serialize_word y (j.val / 4) (by omega) (j.val % 4) (by omega)
  simp only [show 4 * (j.val / 4) + j.val % 4 = j.val by omega] at this
  rw [← this]
  rfl

theorem feed_scratch_nc {sp y : BitVec 64}
    (hy : ∀ (o : BitVec 64) (j : Nat), o.toNat + j < 0x80 → RoundScratch (o.toNat + j) →
      y ≠ sp + o + BitVec.ofNat 64 j) :
    ∀ c ∈ feedScratch sp, ¬ c.Covers y := by
  intro c hc hcv
  simp only [feedScratch, Rounds.regScratch, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | (h | h | h) <;>
    subst h <;> simp only [Component.Covers] at hcv
  all_goals obtain ⟨j, hj, he⟩ := hcv
  all_goals exact hy _ j (by simp; omega) (by unfold RoundScratch; simp; omega) he

end FeedBlocks

section Stubs

variable [Bindings] (boundary : ReturnBoundary)
  (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat)
  {sp st input output : BitVec 64} {size : Nat} {msg : Nat → UInt8} {x : Vector UInt32 16}
  {t : RamState} (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t)

include hb hr hc

theorem tail_empty (h : TailCut sp st input output size msg x t) (hz : tail size = 0) :
    Reach boundary sp st output size t (Final output size msg x) := by
  obtain ⟨u, a1, r1, c1, e1⟩ := step (boundary := boundary)
    (test_r64_r64_effect_step 0x1010cc 0x4d 0xff (by unfold RexWPrefix; decide) (by decide))
    hr hc (MemoryRoutines.Machine.program_text_slice hc 0x10cc 3 (by decide +kernel)) h.rip
    (by
      intro he
      apply ne_boundary hb (p := 0x1010cf) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  have hg : gprNumber 0 (rexB (UInt8.toBitVec 0x4d)) (modrmRm 0xff) = 15 := by decide
  have hg' : gprNumber 0 (rexR (UInt8.toBitVec 0x4d)) (modrmReg 0xff) = 15 := by decide
  rw [hg, hg'] at e1
  have hZF : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = true := by
    obtain ⟨-, -, -, hZ, -⟩ := e1.flags
    have h0 : (Operand.reg 15 : Operand 64).read t = 0 := by
      rw [show (Operand.reg 15 : Operand 64).read t = reg64 t 15 from rfl, h.tail, hz]; rfl
    simp only [testFlags, FlagAllows, h0] at hZ
    rw [hZ]; rfl
  have hj : (jccEffect 0x1010cf 6 4 ((0x3d3 : BitVec 32).signExtend 64) u).rip = 0x1014a8 := by
    simp only [jccEffect, branchEffect, condHolds_4, hZF]; rfl
  obtain ⟨v, a2, r2, c2, e2⟩ := step (boundary := boundary)
    (jcc_rel32_effect_step 0x1010cf 4 0x3d3)
    r1 c1 (MemoryRoutines.Machine.program_text_slice c1 0x10cf 6 (by decide +kernel))
    ⟨e1.rip.trans rfl, fun _ ↦ by decide⟩
    (by rw [hj]; exact ne_boundary hb (by decide) (by decide))
    (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _)
  obtain ⟨w, a3, r3, c3, e3⟩ := step (boundary := boundary)
    (xor_r32_r32_effect_step 0x1014a8 0xc0 (by decide))
    r2 c2 (MemoryRoutines.Machine.program_text_slice c2 0x14a8 2 (by decide +kernel))
    (e2.rip.trans hj)
    (by
      intro he
      apply ne_boundary hb (p := 0x1014aa) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  have hg0 : gprNumber 0 0 (modrmRm 192) = 0 := by decide
  have hg0' : gprNumber 0 0 (modrmReg 192) = 0 := by decide
  rw [hg0, hg0'] at e3
  have g1 := e1.agrees
  have g2 := e2.agrees
  have g3 := e3.agrees
  simp only [testR64R64Effect_components] at g1
  simp only [jccEffect, branchEffect_components] at g2
  simp only [xorR32R32Effect_components] at g3
  refine ⟨1 + 1 + 1, w, (a1.trans a2).trans a3, r3, c3, ?_, ⟨e3.rip, ?_, ?_⟩⟩
  · exact ((g1.trans g2).trans g3).mono (by simp [changes])
  · have hw := e3.writes
    simp only [xorR32R32Effect, Write.AllHold] at hw
    rw [show rax = (Operand.reg 0 : Operand 64) from rfl, hw]
    simp
  · intro i hi1 hi2
    have := base_le size
    omega

theorem tail_setup (h : TailCut sp st input output size msg x t) (hz : tail size ≠ 0) :
    Reach boundary sp st output size t (Rounds sp st input output size msg x 0) := by
  have hsp := h.space
  have hsl := hsp.stack.low
  have hT : tail size < 64 := Nat.mod_lt _ (by decide)
  have houl := hsp.outLow
  obtain ⟨u1, a1, r1, c1, e1⟩ := step (boundary := boundary)
    (test_r64_r64_effect_step 0x1010cc 0x4d 0xff (by unfold RexWPrefix; decide) (by decide))
    hr hc (MemoryRoutines.Machine.program_text_slice hc 0x10cc 3 (by decide +kernel)) h.rip
    (by
      intro he
      apply ne_boundary hb (p := 0x1010cf) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x4d)) (modrmRm 0xff) = 15 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x4d)) (modrmReg 0xff) = 15 by decide] at e1
  have hZF : (StatusFlags.ofRFLAGS u1.RFLAGS).ZF = false := by
    obtain ⟨-, -, -, hZ, -⟩ := e1.flags
    have h0 : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (tail size) := h.tail
    simp only [testFlags, FlagAllows, h0, BitVec.and_self] at hZ
    rw [hZ, beq_eq_false_iff_ne]
    intro hv
    have := congrArg BitVec.toNat hv
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact hz this
  have hj : (jccEffect 0x1010cf 6 4 ((0x3d3 : BitVec 32).signExtend 64) u1).rip = 0x1010d5 := by
    simp only [jccEffect, branchEffect, condHolds_4, hZF]; rfl
  obtain ⟨u2, a2, r2, c2, e2⟩ := step (boundary := boundary)
    (jcc_rel32_effect_step 0x1010cf 4 0x3d3)
    r1 c1 (MemoryRoutines.Machine.program_text_slice c1 0x10cf 6 (by decide +kernel))
    ⟨e1.rip.trans rfl, fun _ ↦ by decide⟩
    (by rw [hj]; exact ne_boundary hb (by decide) (by decide))
    (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _)
  have g1 := e1.agrees
  have g2 := e2.agrees
  simp only [testR64R64Effect_components] at g1
  simp only [jccEffect, branchEffect_components] at g2
  have g12 : AgreesExcept (setupScratch sp) t u2 :=
    (g1.trans g2).mono (by simp [setupScratch, Rounds.regScratch])
  have hrf0 : Rounds.RFrame sp t :=
    ⟨(rspOf_eq t).trans hsp.rsp, by simpa using writable_slice hsp.stack 0 0x80 (by decide),
      fun i hi ↦ hsp.stackCode i (by unfold frameBytes; omega)⟩
  have hrf2 := hrf0.of_agrees (setupScratch_good sp) g12
  have hx2 : u2.external = t.external := (g1.trans g2).external (by simp [Component.Covers])
  have hrd2 (r : BitVec 5) : (Operand.reg r : Operand 64).read u2 = (Operand.reg r : Operand 64).read t :=
    (g1.trans g2).read (by simp)
  have hsf2 : SFrame sp st u2 :=
    ⟨hrf2.rsp, (hrd2 7).trans h.state, hrf2.writable, hrf2.code,
      by have := (writable_slice hsp.state 0 0x40 (by decide)).readable
         simp only [BitVec.add_zero] at this
         exact this.of_external_eq hx2⟩
  obtain ⟨f3, v1, a3, r3, c3, i3, hrf3, ag3, he3⟩ := setup1Run boundary hb sp st r2 c2
    ⟨e2.rip.trans hj, hsf2⟩ hrf2
  have hap := stackStateApart hsp.stateStack
  have hB : BytesAt st (serialize x) u2 := fun i ↦ by rw [hx2]; exact h.words i
  have hst0 : Write.AllHold u2 (Rounds.cut st stL x) := by
    simp only [Rounds.cut, stL, List.map, Rounds.Loc.op, Write.AllHold]
    exact ⟨load_word hB 0 (by decide), load_word hB 1 (by decide), load_word hB 2 (by decide), load_word hB 3 (by decide), load_word hB 4 (by decide), load_word hB 5 (by decide), load_word hB 6 (by decide), load_word hB 7 (by decide), load_word hB 8 (by decide), load_word hB 9 (by decide), load_word hB 10 (by decide), load_word hB 11 (by decide), load_word hB 12 (by decide), load_word hB 13 (by decide), load_word hB 14 (by decide), load_word hB 15 (by decide)⟩
  have hw0 : Write.AllHold u2 (Rounds.cut sp ([] : List (Fin 16 × Rounds.Loc)) x ++
      [⟨(Operand.reg 11 : Operand 64), BitVec.ofNat 64 size⟩,
        ⟨(Operand.mem (sp + 0x48) : Operand 64), st⟩]) := by
    simp only [Rounds.cut, List.map, List.nil_append, Write.AllHold]
    exact ⟨(hrd2 11).trans h.length, by
      change memLoad u2.external (sp + BitVec.ofNat 64 0x48) 64 = st
      rw [hx2]; exact h.slots.state⟩
  have W1 := setup1Words hrf2.rsp hsf2.rdi hap hst0 hw0 he3
  have hW1 := W1
  simp only [Rounds.cut, setupL1, List.map, Rounds.Loc.op, List.cons_append, List.nil_append,
    Write.AllHold] at hW1
  have hsf3 : SFrame sp st v1 :=
    ⟨hrf3.rsp, hW1.2.2.2.2.2.2.2.2.2.2, hrf3.writable, hrf3.code,
      ⟨hsf2.state.low, fun i hi ↦ ag3.grow _ (hsf2.state.mem i hi)⟩⟩
  obtain ⟨f4, v2, a4, r4, c4, i4, hrf4, ag4, he4⟩ := setup2Run boundary hb sp st r3 c3
    ⟨i3, hsf3⟩ hrf3
  have W2 := setup2Words hrf3.rsp hsf3.rdi hap (stL_keep ag3 hsp.stateStack hst0) W1 he4
  obtain ⟨f5, v3, a5, r5, c5, i5, hrf5, ag5, he5⟩ := setup3Run boundary hb sp r4 c4
    ⟨i4, hrf4⟩ hrf4
  have W3 := setup3Words hrf4.rsp W2 he5
  obtain ⟨f6, v4, a6, r6, c6, i6, hrf6, ag6, he6⟩ := setup4Run boundary hb sp r5 c5
    ⟨i5, hrf5⟩ hrf5
  have W4 := setup4Words hrf5.rsp W3 he6
  obtain ⟨f7, v5, a7, r7, c7, i7, hrf7, ag7, he7⟩ := setup5Run boundary hb sp r6 c6
    ⟨i6, hrf6⟩ hrf6
  have W5 := setup5Words hrf6.rsp W4 he7
  obtain ⟨w, a8, r8, c8, e8, i8⟩ := rstep hb (q := 0x101180)
    (nop_m_effect_step 0x101179 [] (by decide) (by decide) (.base 0 (.d32 0)) (by decide) (by decide)
      (by decide))
    r7 c7 (MemoryRoutines.Machine.program_text_slice c7 0x1179 7 (by decide +kernel)) i7 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  have g8 := e8.agrees
  simp only [nopEffect_components] at g8
  have g8' : AgreesExcept (setupScratch sp) v5 w := g8.mono (by simp [setupScratch, Rounds.regScratch])
  have G : AgreesExcept (setupScratch sp) t w :=
    ((((((g12.trans ag3).trans ag4).trans ag5).trans ag6).trans ag7).trans g8').mono (by simp)
  have hx8 : w.external = v5.external := g8.external (by simp [Component.Covers])
  simp only [Rounds.cut, Rounds.tailBase, setupInit, List.map, Rounds.Loc.op, List.cons_append,
    List.nil_append, Write.AllHold] at W5
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, j0, j1, j2, j3, j4,
    j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15, o40, o48, o58⟩ := W5
  have hreg (r : BitVec 5) : (Operand.reg r : Operand 32).read w = (Operand.reg r : Operand 32).read v5 :=
    g8.read (by simp)
  have hm32 (a : BitVec 64) : (Operand.mem a : Operand 32).read w = (Operand.mem a : Operand 32).read v5 := by
    simp only [Operand.read, hx8]
  have hm64 (a : BitVec 64) : (Operand.mem a : Operand 64).read w = (Operand.mem a : Operand 64).read v5 := by
    simp only [Operand.read, hx8]
  have hfar (off : Nat) (h1 : 0x80 ≤ off) (h2 : off + 8 ≤ 0x170) : slot64 w sp off = slot64 t sp off :=
    Rounds.read_mem_agrees (n := 64) G fun i hi ↦ far_nc fun j hj ↦ by
      unfold slot; rw [tail_add]
      exact add_ofNat_ne (by unfold frameBytes at hsl; omega) (by omega) (by omega)
  refine ⟨_, w, ((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8)),
    r8, c8, ?_, ?_⟩
  · refine G.widen (by simp [setupScratch, Rounds.regScratch, changes, Component.isMem])
      (fun y c hc hcv ↦ ?_)
    obtain ⟨j, hj, rfl⟩ := (setupScratch_good sp).2 c hc y hcv
    exact ⟨.mem sp frameBytes, by simp [changes], j, by unfold frameBytes; omega, rfl⟩
  · exact
      { rip := by rw [i8]; rfl
        space := hsp.transfer G (by simp [setupScratch, Rounds.regScratch])
        slots := ⟨(hm64 _).trans o48, (hfar 0x88 (by decide) (by decide)).trans h.slots.output,
          (hfar 0x90 (by decide) (by decide)).trans h.slots.input,
          (hfar 0x98 (by decide) (by decide)).trans h.slots.head,
          (hfar 0xa0 (by decide) (by decide)).trans h.slots.tail,
          (hfar 0xa8 (by decide) (by decide)).trans h.slots.length⟩
        le := by omega
        working := ⟨(hm32 _).trans w0, (hreg _).trans w1, (hreg _).trans w2, (hreg _).trans w3,
          (hreg _).trans w4, (hreg _).trans w5, (hreg _).trans w6, (hreg _).trans w7,
          (hm32 _).trans w8, (hreg _).trans w9, (hreg _).trans w10, (hreg _).trans w11,
          (hreg _).trans w12, (hreg _).trans w13, (hreg _).trans w14, (hreg _).trans w15⟩
        initial := ⟨(hm32 _).trans j0, (hm32 _).trans j1, (hm32 _).trans j2, (hm32 _).trans j3,
          (hm32 _).trans j4, (hm32 _).trans j5, (hm32 _).trans j6, (hm32 _).trans j7,
          (hm32 _).trans j8, (hm32 _).trans j9, (hm32 _).trans j10, (hm32 _).trans j11,
          (hm32 _).trans j12, (hm32 _).trans j13, (hm32 _).trans j14, (hm32 _).trans j15⟩
        count := (hm64 _).trans o58
        offset := by
          rw [show slot64 w sp 0x40 = _ from (hm64 _).trans o40]
          exact mask_base size (by omega)
        nonzero := hz
        rest := fun i h1 h2 ↦ by
          rw [G.byte (far_nc fun j hj ↦ ?_)]
          · exact h.rest i h1 h2
          · rw [in_addr input (size := size) h1]
            exact hsp.inStack (i - base size) (by have := base_le size; omega) j
              (by unfold frameBytes; omega) }

theorem round_step {k : Nat} (h : Rounds sp st input output size msg x k t) (hk : k < 10) :
    Reach boundary sp st output size t (Rounds sp st input output size msg x (k + 1)) := by
  have hsp := h.space
  have hip : t.RIP = 0x101180 := by rw [h.rip]; simp [hk]
  have hsl := hsp.stack.low
  have hrf : Rounds.RFrame sp t :=
    ⟨hsp.rsp, by simpa using writable_slice hsp.stack 0 0x80 (by decide),
      fun i hi ↦ hsp.stackCode i (by unfold frameBytes; omega)⟩
  have hW := h.working
  have hw : Write.AllHold t (Rounds.cut sp Rounds.tailBase (Nat.repeat doubleRound k x)) := by
    simp only [Rounds.cut, Rounds.tailBase, List.map, Rounds.Loc.op, Write.AllHold]
    exact ⟨hW.w0, hW.w1, hW.w2, hW.w3, hW.w4, hW.w5, hW.w6, hW.w7, hW.w8, hW.w9, hW.w10, hW.w11,
      hW.w12, hW.w13, hW.w14, hW.w15⟩
  obtain ⟨f, u, a, ru, cu, hrip, -, hw', hcnt, hag⟩ := Rounds.tailIter boundary hb sp _ (9 - k) t
    hr hc hip hrf hw (by rw [show 9 - k + 1 = 10 - k by omega]; exact h.count) (by omega)
  have hkeep (m : Nat) (hm : m < 2 ^ 32) (hd : ¬ RoundScratch m) :
      u.external[sp + BitVec.ofNat 64 m]? = t.external[sp + BitVec.ofNat 64 m]? :=
    hag.byte (off_scratch hm hd)
  have hslot (n off : Nat) (hn : off + n / 8 ≤ 0x170) (hd : ∀ i < n / 8, ¬ RoundScratch (off + i)) :
      memLoad u.external (slot sp off) n = memLoad t.external (slot sp off) n :=
    slot_keep n hag off fun i hi ↦ off_scratch (by unfold frameBytes at hsl; omega) (hd i hi)
  have s64 (off : Nat) (hn : off + 8 ≤ 0x170) (hd : ∀ i < 8, ¬ RoundScratch (off + i)) :
      slot64 u sp off = slot64 t sp off := hslot 64 off (by omega) hd
  have s32 (off : Nat) (hn : off + 4 ≤ 0x170) (hd : ∀ i < 4, ¬ RoundScratch (off + i)) :
      slot32 u sp off = slot32 t sp off := hslot 32 off (by omega) hd
  have hI := h.initial
  have hS := h.slots
  refine ⟨f, u, a, ru, cu, hag.widen (by simp [Rounds.tailScratch, Rounds.tailQR,
    Rounds.regScratch, changes, Component.isMem]) ?_, ?_⟩
  · intro y c hc hcv
    refine ⟨.mem sp frameBytes, by simp [changes], ?_⟩
    simp only [Rounds.tailScratch, Rounds.tailQR, Rounds.regScratch, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) |
      (h | h | h | h)) | h <;> subst h <;> simp only [Component.Covers] at hcv
    all_goals obtain ⟨j, hj, rfl⟩ := hcv
    all_goals exact ⟨_, by unfold frameBytes; simp; omega, (tail_add sp _ j)⟩
  · simp only [Rounds.cut, Rounds.tailBase, List.map, Rounds.Loc.op, Write.AllHold] at hw'
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ := hw'
    exact
      { rip := by rw [hrip]; by_cases he : k + 1 < 10 <;> simp [he] <;> omega
        space := hsp.transfer hag (by simp [Rounds.tailScratch, Rounds.tailQR, Rounds.regScratch])
        slots :=
          ⟨(s64 0x48 (by decide) (by unfold RoundScratch; omega)).trans hS.state,
            (s64 0x88 (by decide) (by unfold RoundScratch; omega)).trans hS.output,
            (s64 0x90 (by decide) (by unfold RoundScratch; omega)).trans hS.input,
            (s64 0x98 (by decide) (by unfold RoundScratch; omega)).trans hS.head,
            (s64 0xa0 (by decide) (by unfold RoundScratch; omega)).trans hS.tail,
            (s64 0xa8 (by decide) (by unfold RoundScratch; omega)).trans hS.length⟩
        le := by omega
        working := ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩
        initial :=
          ⟨(s32 0x38 (by decide) (by unfold RoundScratch; omega)).trans hI.w0,
            (s32 0x60 (by decide) (by unfold RoundScratch; omega)).trans hI.w1,
            (s32 0x68 (by decide) (by unfold RoundScratch; omega)).trans hI.w2,
            (s32 0xc (by decide) (by unfold RoundScratch; omega)).trans hI.w3,
            (s32 0x50 (by decide) (by unfold RoundScratch; omega)).trans hI.w4,
            (s32 0x70 (by decide) (by unfold RoundScratch; omega)).trans hI.w5,
            (s32 0x3c (by decide) (by unfold RoundScratch; omega)).trans hI.w6,
            (s32 0x10 (by decide) (by unfold RoundScratch; omega)).trans hI.w7,
            (s32 0x18 (by decide) (by unfold RoundScratch; omega)).trans hI.w8,
            (s32 0x1c (by decide) (by unfold RoundScratch; omega)).trans hI.w9,
            (s32 0x20 (by decide) (by unfold RoundScratch; omega)).trans hI.w10,
            (s32 0x24 (by decide) (by unfold RoundScratch; omega)).trans hI.w11,
            (s32 0x34 (by decide) (by unfold RoundScratch; omega)).trans hI.w12,
            (s32 0x28 (by decide) (by unfold RoundScratch; omega)).trans hI.w13,
            (s32 0x2c (by decide) (by unfold RoundScratch; omega)).trans hI.w14,
            (s32 0x30 (by decide) (by unfold RoundScratch; omega)).trans hI.w15⟩
        count := by
          have : slot64 u sp 0x58 = BitVec.ofNat 64 (9 - k) := hcnt
          rw [this]; congr 1; omega
        offset := (s64 0x40 (by decide) (by unfold RoundScratch; omega)).trans h.offset
        nonzero := h.nonzero
        rest := fun i h1 h2 ↦ by
          rw [hag.byte (tail_scratch_nc fun o j _ _ ↦ ?_)]
          · exact h.rest i h1 h2
          · rw [in_addr input (size := size) h1, add_toNat]
            exact hsp.inStack (i - base size) (by have := base_le size; omega) _
              (by unfold frameBytes; omega) }

set_option maxHeartbeats 20000000 in
theorem tail_feed (h : Rounds sp st input output size msg x 10 t) :
    Reach boundary sp st output size t (Keyed sp st input output size msg x) := by
  have hsp := h.space
  have hsl := hsp.stack.low
  have hstl : st.toNat + 0x80 ≤ 2 ^ 32 := hsp.state.low
  have hip : t.RIP = 0x1012e3 := by rw [h.rip]; rfl
  have hrf : Rounds.RFrame sp t :=
    ⟨(rspOf_eq t).trans hsp.rsp, by simpa using writable_slice hsp.stack 0 0x80 (by decide),
      fun i hi ↦ hsp.stackCode i (by unfold frameBytes; omega)⟩
  have hW := h.working
  have hI := h.initial
  have hw0 : Write.AllHold t (Rounds.cut sp Rounds.tailBase (Nat.repeat doubleRound 10 x) ++
      Rounds.cut sp setupInit x ++ Rounds.cut sp ([] : List (Fin 16 × Rounds.Loc))
        (Vector.ofFn fun i => (Nat.repeat doubleRound 10 x)[i] + x[i])) := by
    simp only [Rounds.cut, Rounds.tailBase, setupInit, List.map, Rounds.Loc.op, List.cons_append,
      List.nil_append, List.append_nil, Write.AllHold]
    exact ⟨hW.w0, hW.w1, hW.w2, hW.w3, hW.w4, hW.w5, hW.w6, hW.w7, hW.w8, hW.w9, hW.w10, hW.w11, hW.w12, hW.w13, hW.w14, hW.w15, hI.w0, hI.w1, hI.w2, hI.w3, hI.w4, hI.w5, hI.w6, hI.w7, hI.w8, hI.w9, hI.w10, hI.w11, hI.w12, hI.w13, hI.w14, hI.w15⟩
  obtain ⟨n1, f1, fa1, rf1, cf1, if1, hrf1, ag1, he1⟩ := feed1Run boundary hb sp hr hc hip hrf
  have W1 := feed1Words hrf.rsp hw0 he1
  obtain ⟨n2, f2, fa2, rf2, cf2, if2, hrf2, ag2, he2⟩ := feed2Run boundary hb sp rf1 cf1 if1 hrf1
  have W2 := feed2Words hrf1.rsp W1 he2
  obtain ⟨n3, u0, fa3, r0, c0, i0, hrf3, ag3, he3⟩ := feed3Run boundary hb sp rf2 cf2 if2 hrf2
  have W3 := feed3Words hrf2.rsp W2 he3
  simp only [Rounds.cut, feedC3, List.map, Rounds.Loc.op, List.nil_append,
    List.append_nil, Write.AllHold] at W3
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15⟩ := W3
  have Gf : AgreesExcept (feedScratch sp) t u0 := ((ag1.trans ag2).trans ag3).mono (by simp)
  have hfoff (off : Nat) (hn : off + 8 ≤ 0x170) (hd : ∀ i < 8, ¬ RoundScratch (off + i)) :
      memLoad u0.external (sp + BitVec.ofNat 64 off) 64 = memLoad t.external (sp + BitVec.ofNat 64 off) 64 :=
    Rounds.read_mem_agrees (n := 64) Gf fun i hi ↦ by
      rw [tail_add]
      exact feed_scratch_nc fun o j h1 h2 ↦ stack_ne sp (fun he ↦ hd i (by omega) (he ▸ h2))
        (by unfold frameBytes at hsl; omega) (by omega)
  have h48 : memLoad u0.external (sp + BitVec.ofNat 64 0x48) 64 = st :=
    (hfoff 0x48 (by decide) (by unfold RoundScratch; omega)).trans h.slots.state
  have ss0 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u0.external (sp + BitVec.ofNat 64 off) n =
      memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun _ _ _ ↦ rfl
  have fs0 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u0.external[y]? = u0.external[y]? :=
    fun _ _ ↦ rfl
  have G0 : AgreesExcept (changes sp st output size) u0 u0 := AgreesExcept.refl _ _
  have hsp0 : Space sp st input output size u0 := hsp.transfer Gf (by simp [feedScratch, Rounds.regScratch])
  obtain ⟨u1, a0, r1, c1, g0, i1, v0⟩ := load_slot hb r0 c0 hsp0 0x101347 0x10134c 0x48
    (by unfold RexWPrefix; decide) 3 (.d8 0x48) 0x48 (by decide) (by decide) (by decide)
    (by decide) (by decide) (MemoryRoutines.Machine.program_text_slice c0 0x1347 5 (by decide +kernel))
    i0 (by decide) (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x48)) 3 = 3 from rfl] at v0 g0
  have b0 : (Operand.reg 3 : Operand 64).read u1 = st := by
    rw [v0]; unfold slot64 slot; rw [ss0 0x48 64 (by decide)]; exact h48
  have hx0 : u1.external = u0.external := g0.external (by simp [Component.Covers])
  have ss1 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u1.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (congrArg (fun m ↦ memLoad m (sp + BitVec.ofNat 64 off) n) hx0).trans (ss0 off n h)
  have hsp1 : Space sp st input output size u1 := hsp0.transfer g0 (by simp)
  have G1 : AgreesExcept (changes sp st output size) u0 u1 := (G0.trans (g0.mono (cs' := changes sp st output size) (by simp [changes]))).mono (by simp)
  have fs1 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u1.external[y]? = u0.external[y]? := fun y hy ↦ (congrArg (fun m : Ram ↦ m[y]?) hx0).trans (fs0 y hy)
  have ha1 : AddrMode.addr (.base 3 (.d8 0x30)) u1 (0x10134c + BitVec.ofNat 64 (3 + 1)) = st + BitVec.ofNat 64 0x30 :=
    storeAddr_base _ _ _ _ b0 (by decide)
  obtain ⟨u2, a1, r2, c2, e1⟩ := step (boundary := boundary) (mov_m32_r32_effect_step 0x10134c 0x44 (by unfold RexNoWPrefix; decide) 5 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide))
    r1 c1 (MemoryRoutines.Machine.program_text_slice c1 0x134c 4 (by decide +kernel))
    ⟨i1, by simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x30)).tail.length) = 3 + 1 from rfl, ha1]; exact writable_slice hsp1.state 0x30 4 (by decide), by
      simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x30)).tail.length) = 3 + 1 from rfl, ha1]
      exact (hsp1.stateCode.slice 0x30 4 (by decide)).apart (text_in_program' 0x10134c 0x134c 4 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x101350) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x30) (n := 4)
      (by simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x30)).tail.length) = 3 + 1 from rfl, ha1]) (hsp1.stateCode.slice 0x30 4 (by decide)))
  have g1 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x30) 4, .rip] u1 u2 := by
    have := e1.agrees
    simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x30)).tail.length) = 3 + 1 from rfl, ha1] at this
    exact this
  have i2 : u2.RIP = 0x101350 := e1.rip.trans rfl
  have ss2 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u2.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g1 hsp.stateStack (by decide) h).trans (ss1 off n h)
  have hsp2 : Space sp st input output size u2 := hsp1.transfer g1 (by simp)
  have G2 : AgreesExcept (changes sp st output size) u0 u2 :=
    (G1.trans (g1.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x30) 4, by simp [changes], j, hj, rfl⟩
      · exact hcv.elim))).mono (by simp)
  have fs2 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u2.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g1 hy (by decide)).trans (fs1 y hy)
  have ha2 : AddrMode.addr (.sib 4 none 0 (.d8 0x8)) u2 (0x101350 + BitVec.ofNat 64 (2 + 2)) = sp + BitVec.ofNat 64 0x8 := by
    simp only [AddrMode.addr]; rw [reg64_rsp, hsp2.rsp]; rfl
  obtain ⟨u3, a2, r3, c3, e2⟩ := step (boundary := boundary) (mov_r32_m32_low_effect_step 0x101350 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
    r2 c2 (MemoryRoutines.Machine.program_text_slice c2 0x1350 4 (by decide +kernel))
    ⟨i2, by rw [show (2 + (AddrMode.sib 4 none 0 (.d8 0x8)).tail.length) = 2 + 2 from rfl, ha2]; exact (writable_slice hsp2.stack 0x8 4 (by decide)).readable⟩
    (by intro he; apply ne_boundary hb (p := 0x101354) (by decide) (by decide); rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  rw [show gprNumber 0 0 3 = 3 from rfl] at e2
  have g2 := e2.agrees
  simp only [movR32M32LowEffect_components] at g2
  have i3 : u3.RIP = 0x101354 := e2.rip.trans rfl
  have v2 : (Operand.reg 3 : Operand 32).read u3 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[0].toBitVec := by
    have hw := e2.writes
    simp only [movR32M32LowEffect, Write.AllHold] at hw
    rw [reg32_eq, hw, show (2 + (AddrMode.sib 4 none 0 (.d8 0x8)).tail.length) = 2 + 2 from rfl]
    change ((memLoad u2.external _ 32).setWidth 64).setWidth 32 = _
    rw [ha2, ss2 0x8 32 (by decide), BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    exact q0
  have hx2 : u3.external = u2.external := g2.external (by simp [Component.Covers])
  have ss3 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u3.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (congrArg (fun m ↦ memLoad m (sp + BitVec.ofNat 64 off) n) hx2).trans (ss2 off n h)
  have hsp3 : Space sp st input output size u3 := hsp2.transfer g2 (by simp)
  have G3 : AgreesExcept (changes sp st output size) u0 u3 := (G2.trans (g2.mono (cs' := changes sp st output size) (by simp [changes]))).mono (by simp)
  have fs3 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u3.external[y]? = u0.external[y]? := fun y hy ↦ (congrArg (fun m : Ram ↦ m[y]?) hx2).trans (fs2 y hy)
  obtain ⟨u4, a3, r4, c4, g3, i4, v3⟩ := load_slot hb r3 c3 hsp3 0x101354 0x101359 0x4c
    (by unfold RexWPrefix; decide) 5 (.d8 0x48) 0x48 (by decide) (by decide) (by decide)
    (by decide) (by decide) (MemoryRoutines.Machine.program_text_slice c3 0x1354 5 (by decide +kernel))
    i3 (by decide) (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 5 = 13 from rfl] at v3 g3
  have b3 : (Operand.reg 13 : Operand 64).read u4 = st := by
    rw [v3]; unfold slot64 slot; rw [ss3 0x48 64 (by decide)]; exact h48
  have hx3 : u4.external = u3.external := g3.external (by simp [Component.Covers])
  have ss4 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u4.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (congrArg (fun m ↦ memLoad m (sp + BitVec.ofNat 64 off) n) hx3).trans (ss3 off n h)
  have hsp4 : Space sp st input output size u4 := hsp3.transfer g3 (by simp)
  have G4 : AgreesExcept (changes sp st output size) u0 u4 := (G3.trans (g3.mono (cs' := changes sp st output size) (by simp [changes]))).mono (by simp)
  have fs4 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u4.external[y]? = u0.external[y]? := fun y hy ↦ (congrArg (fun m : Ram ↦ m[y]?) hx3).trans (fs3 y hy)
  have ha4 : AddrMode.addr (.base 13 (.d8 0x40)) u4 (0x101359 + BitVec.ofNat 64 (3 + 1)) = st + BitVec.ofNat 64 0x40 :=
    storeAddr_base _ _ _ _ b3 (by decide)
  obtain ⟨u5, a4, r5, c5, e4⟩ := step (boundary := boundary) (mov_m32_r32_effect_step 0x101359 0x41 (by unfold RexNoWPrefix; decide) 3 (.base 13 (.d8 0x40)) (by decide) (by decide) (by decide))
    r4 c4 (MemoryRoutines.Machine.program_text_slice c4 0x1359 4 (by decide +kernel))
    ⟨i4, by simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 13 (.d8 0x40)).tail.length) = 3 + 1 from rfl, ha4]; exact writable_slice hsp4.state 0x40 4 (by decide), by
      simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 13 (.d8 0x40)).tail.length) = 3 + 1 from rfl, ha4]
      exact (hsp4.stateCode.slice 0x40 4 (by decide)).apart (text_in_program' 0x101359 0x1359 4 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x10135d) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x40) (n := 4)
      (by simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 13 (.d8 0x40)).tail.length) = 3 + 1 from rfl, ha4]) (hsp4.stateCode.slice 0x40 4 (by decide)))
  have g4 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x40) 4, .rip] u4 u5 := by
    have := e4.agrees
    simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 13 (.d8 0x40)).tail.length) = 3 + 1 from rfl, ha4] at this
    exact this
  have i5 : u5.RIP = 0x10135d := e4.rip.trans rfl
  have w4 : memLoad u5.external (st + BitVec.ofNat 64 0x40) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[0].toBitVec := by
    have hw := e4.writes
    simp only [movM32R32Effect, storeEffect, storeAddrAt, Write.AllHold, show (3 + (AddrMode.base 13 (.d8 0x40)).tail.length) = 3 + 1 from rfl, ha4] at hw
    rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x41)) 3 = 3 from rfl] at hw
    exact hw.trans ((show (Operand.reg 3 : Operand 32).read u4 = (Operand.reg 3 : Operand 32).read u3 from g3.read (by simp)).trans v2)
  have ss5 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u5.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g4 hsp.stateStack (by decide) h).trans (ss4 off n h)
  have hsp5 : Space sp st input output size u5 := hsp4.transfer g4 (by simp)
  have G5 : AgreesExcept (changes sp st output size) u0 u5 :=
    (G4.trans (g4.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x40 - 0x40 + j, by omega, blk_addr st 0x40 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs5 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u5.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g4 hy (by decide)).trans (fs4 y hy)
  obtain ⟨u6, a5, r6, c6, g5, i6, v5⟩ := load_slot hb r5 c5 hsp5 0x10135d 0x101362 0x48
    (by unfold RexWPrefix; decide) 3 (.d8 0x48) 0x48 (by decide) (by decide) (by decide)
    (by decide) (by decide) (MemoryRoutines.Machine.program_text_slice c5 0x135d 5 (by decide +kernel))
    i5 (by decide) (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x48)) 3 = 3 from rfl] at v5 g5
  have b5 : (Operand.reg 3 : Operand 64).read u6 = st := by
    rw [v5]; unfold slot64 slot; rw [ss5 0x48 64 (by decide)]; exact h48
  have hx5 : u6.external = u5.external := g5.external (by simp [Component.Covers])
  have ss6 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u6.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (congrArg (fun m ↦ memLoad m (sp + BitVec.ofNat 64 off) n) hx5).trans (ss5 off n h)
  have hsp6 : Space sp st input output size u6 := hsp5.transfer g5 (by simp)
  have G6 : AgreesExcept (changes sp st output size) u0 u6 := (G5.trans (g5.mono (cs' := changes sp st output size) (by simp [changes]))).mono (by simp)
  have fs6 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u6.external[y]? = u0.external[y]? := fun y hy ↦ (congrArg (fun m : Ram ↦ m[y]?) hx5).trans (fs5 y hy)
  have ha6 : AddrMode.addr (.sib 4 none 0 (.d8 0x14)) u6 (0x101362 + BitVec.ofNat 64 (3 + 2)) = sp + BitVec.ofNat 64 0x14 := by
    simp only [AddrMode.addr]; rw [reg64_rsp, hsp6.rsp]; rfl
  obtain ⟨u7, a6, r7, c7, e6⟩ := step (boundary := boundary) (mov_r32_m32_effect_step 0x101362 0x44 (by unfold RexNoWPrefix; decide) 5 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide))
    r6 c6 (MemoryRoutines.Machine.program_text_slice c6 0x1362 5 (by decide +kernel))
    ⟨i6, by rw [show (movLoadLen (AddrMode.sib 4 none 0 (.d8 0x14))) = 3 + 2 from rfl, ha6]; exact (writable_slice hsp6.stack 0x14 4 (by decide)).readable⟩
    (by intro he; apply ne_boundary hb (p := 0x101367) (by decide) (by decide); rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 5 = 13 from rfl] at e6
  have g6 := e6.agrees
  simp only [movR32M32Effect_components] at g6
  have i7 : u7.RIP = 0x101367 := e6.rip.trans rfl
  have v6 : (Operand.reg 13 : Operand 32).read u7 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[1].toBitVec := by
    have hw := e6.writes
    simp only [movR32M32Effect, Write.AllHold] at hw
    rw [reg32_eq, hw, show (movLoadLen (AddrMode.sib 4 none 0 (.d8 0x14))) = 3 + 2 from rfl]
    change ((memLoad u6.external _ 32).setWidth 64).setWidth 32 = _
    rw [ha6, ss6 0x14 32 (by decide), BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    exact q1
  have hx6 : u7.external = u6.external := g6.external (by simp [Component.Covers])
  have ss7 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u7.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (congrArg (fun m ↦ memLoad m (sp + BitVec.ofNat 64 off) n) hx6).trans (ss6 off n h)
  have hsp7 : Space sp st input output size u7 := hsp6.transfer g6 (by simp)
  have G7 : AgreesExcept (changes sp st output size) u0 u7 := (G6.trans (g6.mono (cs' := changes sp st output size) (by simp [changes]))).mono (by simp)
  have fs7 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u7.external[y]? = u0.external[y]? := fun y hy ↦ (congrArg (fun m : Ram ↦ m[y]?) hx6).trans (fs6 y hy)
  have ha7 : AddrMode.addr (.base 3 (.d8 0x44)) u7 (0x101367 + BitVec.ofNat 64 (3 + 1)) = st + BitVec.ofNat 64 0x44 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u7 = (Operand.reg 3 : Operand 64).read u6 from g6.read (by simp)).trans b5) (by decide)
  obtain ⟨u8, a7, r8, c8, e7⟩ := step (boundary := boundary) (mov_m32_r32_effect_step 0x101367 0x44 (by unfold RexNoWPrefix; decide) 5 (.base 3 (.d8 0x44)) (by decide) (by decide) (by decide))
    r7 c7 (MemoryRoutines.Machine.program_text_slice c7 0x1367 4 (by decide +kernel))
    ⟨i7, by simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x44)).tail.length) = 3 + 1 from rfl, ha7]; exact writable_slice hsp7.state 0x44 4 (by decide), by
      simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x44)).tail.length) = 3 + 1 from rfl, ha7]
      exact (hsp7.stateCode.slice 0x44 4 (by decide)).apart (text_in_program' 0x101367 0x1367 4 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x10136b) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x44) (n := 4)
      (by simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x44)).tail.length) = 3 + 1 from rfl, ha7]) (hsp7.stateCode.slice 0x44 4 (by decide)))
  have g7 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x44) 4, .rip] u7 u8 := by
    have := e7.agrees
    simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x44)).tail.length) = 3 + 1 from rfl, ha7] at this
    exact this
  have i8 : u8.RIP = 0x10136b := e7.rip.trans rfl
  have w7 : memLoad u8.external (st + BitVec.ofNat 64 0x44) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[1].toBitVec := by
    have hw := e7.writes
    simp only [movM32R32Effect, storeEffect, storeAddrAt, Write.AllHold, show (3 + (AddrMode.base 3 (.d8 0x44)).tail.length) = 3 + 1 from rfl, ha7] at hw
    rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 5 = 13 from rfl] at hw
    exact hw.trans v6
  have ss8 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u8.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g7 hsp.stateStack (by decide) h).trans (ss7 off n h)
  have hsp8 : Space sp st input output size u8 := hsp7.transfer g7 (by simp)
  have G8 : AgreesExcept (changes sp st output size) u0 u8 :=
    (G7.trans (g7.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x44 - 0x40 + j, by omega, blk_addr st 0x44 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs8 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u8.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g7 hy (by decide)).trans (fs7 y hy)
  have ha8 : AddrMode.addr (.base 3 (.d8 0x48)) u8 (0x10136b + BitVec.ofNat 64 (2 + 1)) = st + BitVec.ofNat 64 0x48 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u8 = (Operand.reg 3 : Operand 64).read u6 from (g6.trans g7).read (by simp)).trans b5) (by decide)
  obtain ⟨u9, a8, r9, c9, e8⟩ := step (boundary := boundary) (mov_m32_r32_low_effect_step 0x10136b 0 (.base 3 (.d8 0x48)) (by decide) (by decide) (by decide))
    r8 c8 (MemoryRoutines.Machine.program_text_slice c8 0x136b 3 (by decide +kernel))
    ⟨i8, by rw [show (2 + (AddrMode.base 3 (.d8 0x48)).tail.length) = 2 + 1 from rfl, ha8]; exact writable_slice hsp8.state 0x48 4 (by decide), by
      rw [show (2 + (AddrMode.base 3 (.d8 0x48)).tail.length) = 2 + 1 from rfl, ha8]
      exact (hsp8.stateCode.slice 0x48 4 (by decide)).apart (text_in_program' 0x10136b 0x136b 3 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x10136e) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x48) (n := 4)
      (by simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x48)).tail.length) = 2 + 1 from rfl, ha8]) (hsp8.stateCode.slice 0x48 4 (by decide)))
  have g8 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x48) 4, .rip] u8 u9 := by
    have := e8.agrees
    simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x48)).tail.length) = 2 + 1 from rfl, ha8] at this
    exact this
  have i9 : u9.RIP = 0x10136e := e8.rip.trans rfl
  have w8 : memLoad u9.external (st + BitVec.ofNat 64 0x48) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[2].toBitVec := by
    have hw := e8.writes
    simp only [movM32R32LowEffect, storeEffect, Write.AllHold, show (2 + (AddrMode.base 3 (.d8 0x48)).tail.length) = 2 + 1 from rfl, ha8] at hw
    rw [show gprNumber 0 0 0 = 0 from rfl] at hw
    exact hw.trans ((show (Operand.reg 0 : Operand 32).read u8 = (Operand.reg 0 : Operand 32).read u0 from (((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).read (by simp)).trans q2)
  have ss9 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u9.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g8 hsp.stateStack (by decide) h).trans (ss8 off n h)
  have hsp9 : Space sp st input output size u9 := hsp8.transfer g8 (by simp)
  have G9 : AgreesExcept (changes sp st output size) u0 u9 :=
    (G8.trans (g8.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x48 - 0x40 + j, by omega, blk_addr st 0x48 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs9 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u9.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g8 hy (by decide)).trans (fs8 y hy)
  have ha9 : AddrMode.addr (.base 3 (.d8 0x4c)) u9 (0x10136e + BitVec.ofNat 64 (2 + 1)) = st + BitVec.ofNat 64 0x4c :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u9 = (Operand.reg 3 : Operand 64).read u6 from ((g6.trans g7).trans g8).read (by simp)).trans b5) (by decide)
  obtain ⟨u10, a9, r10, c10, e9⟩ := step (boundary := boundary) (mov_m32_r32_low_effect_step 0x10136e 7 (.base 3 (.d8 0x4c)) (by decide) (by decide) (by decide))
    r9 c9 (MemoryRoutines.Machine.program_text_slice c9 0x136e 3 (by decide +kernel))
    ⟨i9, by rw [show (2 + (AddrMode.base 3 (.d8 0x4c)).tail.length) = 2 + 1 from rfl, ha9]; exact writable_slice hsp9.state 0x4c 4 (by decide), by
      rw [show (2 + (AddrMode.base 3 (.d8 0x4c)).tail.length) = 2 + 1 from rfl, ha9]
      exact (hsp9.stateCode.slice 0x4c 4 (by decide)).apart (text_in_program' 0x10136e 0x136e 3 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x101371) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x4c) (n := 4)
      (by simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x4c)).tail.length) = 2 + 1 from rfl, ha9]) (hsp9.stateCode.slice 0x4c 4 (by decide)))
  have g9 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x4c) 4, .rip] u9 u10 := by
    have := e9.agrees
    simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x4c)).tail.length) = 2 + 1 from rfl, ha9] at this
    exact this
  have i10 : u10.RIP = 0x101371 := e9.rip.trans rfl
  have w9 : memLoad u10.external (st + BitVec.ofNat 64 0x4c) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[3].toBitVec := by
    have hw := e9.writes
    simp only [movM32R32LowEffect, storeEffect, Write.AllHold, show (2 + (AddrMode.base 3 (.d8 0x4c)).tail.length) = 2 + 1 from rfl, ha9] at hw
    rw [show gprNumber 0 0 7 = 7 from rfl] at hw
    exact hw.trans ((show (Operand.reg 7 : Operand 32).read u9 = (Operand.reg 7 : Operand 32).read u0 from ((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).read (by simp)).trans q3)
  have ss10 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u10.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g9 hsp.stateStack (by decide) h).trans (ss9 off n h)
  have hsp10 : Space sp st input output size u10 := hsp9.transfer g9 (by simp)
  have G10 : AgreesExcept (changes sp st output size) u0 u10 :=
    (G9.trans (g9.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x4c - 0x40 + j, by omega, blk_addr st 0x4c j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs10 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u10.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g9 hy (by decide)).trans (fs9 y hy)
  have ha10 : AddrMode.addr (.base 3 (.d8 0x50)) u10 (0x101371 + BitVec.ofNat 64 (3 + 1)) = st + BitVec.ofNat 64 0x50 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u10 = (Operand.reg 3 : Operand 64).read u6 from (((g6.trans g7).trans g8).trans g9).read (by simp)).trans b5) (by decide)
  obtain ⟨u11, a10, r11, c11, e10⟩ := step (boundary := boundary) (mov_m32_r32_effect_step 0x101371 0x44 (by unfold RexNoWPrefix; decide) 1 (.base 3 (.d8 0x50)) (by decide) (by decide) (by decide))
    r10 c10 (MemoryRoutines.Machine.program_text_slice c10 0x1371 4 (by decide +kernel))
    ⟨i10, by simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x50)).tail.length) = 3 + 1 from rfl, ha10]; exact writable_slice hsp10.state 0x50 4 (by decide), by
      simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x50)).tail.length) = 3 + 1 from rfl, ha10]
      exact (hsp10.stateCode.slice 0x50 4 (by decide)).apart (text_in_program' 0x101371 0x1371 4 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x101375) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x50) (n := 4)
      (by simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x50)).tail.length) = 3 + 1 from rfl, ha10]) (hsp10.stateCode.slice 0x50 4 (by decide)))
  have g10 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x50) 4, .rip] u10 u11 := by
    have := e10.agrees
    simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x50)).tail.length) = 3 + 1 from rfl, ha10] at this
    exact this
  have i11 : u11.RIP = 0x101375 := e10.rip.trans rfl
  have w10 : memLoad u11.external (st + BitVec.ofNat 64 0x50) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[4].toBitVec := by
    have hw := e10.writes
    simp only [movM32R32Effect, storeEffect, storeAddrAt, Write.AllHold, show (3 + (AddrMode.base 3 (.d8 0x50)).tail.length) = 3 + 1 from rfl, ha10] at hw
    rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 1 = 9 from rfl] at hw
    exact hw.trans ((show (Operand.reg 9 : Operand 32).read u10 = (Operand.reg 9 : Operand 32).read u0 from (((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).read (by simp)).trans q4)
  have ss11 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u11.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g10 hsp.stateStack (by decide) h).trans (ss10 off n h)
  have hsp11 : Space sp st input output size u11 := hsp10.transfer g10 (by simp)
  have G11 : AgreesExcept (changes sp st output size) u0 u11 :=
    (G10.trans (g10.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x50 - 0x40 + j, by omega, blk_addr st 0x50 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs11 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u11.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g10 hy (by decide)).trans (fs10 y hy)
  obtain ⟨u12, a11, r12, c12, e11, i12⟩ := rstep hb (q := 0x101378)
    (mov_r64_r64_effect_step 0x101375 0x49 0xd9 (by unfold RexWPrefix; decide) (by decide))
    r11 c11 (MemoryRoutines.Machine.program_text_slice c11 0x1375 3 (by decide +kernel)) i11 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x49)) (modrmRm 0xd9) = 9 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x49)) (modrmReg 0xd9) = 3 by decide] at e11
  have g11 := e11.agrees
  simp only [movR64R64Effect_components] at g11
  have b11 : (Operand.reg 9 : Operand 64).read u12 = st := by
    have hw := e11.writes
    simp only [movR64R64Effect, Write.AllHold] at hw
    rw [hw]; exact ((show (Operand.reg 3 : Operand 64).read u11 = (Operand.reg 3 : Operand 64).read u6 from ((((g6.trans g7).trans g8).trans g9).trans g10).read (by simp)).trans b5)
  have hx11 : u12.external = u11.external := g11.external (by simp [Component.Covers])
  have ss12 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u12.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (congrArg (fun m ↦ memLoad m (sp + BitVec.ofNat 64 off) n) hx11).trans (ss11 off n h)
  have hsp12 : Space sp st input output size u12 := hsp11.transfer g11 (by simp)
  have G12 : AgreesExcept (changes sp st output size) u0 u12 := (G11.trans (g11.mono (cs' := changes sp st output size) (by simp [changes]))).mono (by simp)
  have fs12 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u12.external[y]? = u0.external[y]? := fun y hy ↦ (congrArg (fun m : Ram ↦ m[y]?) hx11).trans (fs11 y hy)
  have ha12 : AddrMode.addr (.base 3 (.d8 0x54)) u12 (0x101378 + BitVec.ofNat 64 (2 + 1)) = st + BitVec.ofNat 64 0x54 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u12 = (Operand.reg 3 : Operand 64).read u6 from (((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).read (by simp)).trans b5) (by decide)
  obtain ⟨u13, a12, r13, c13, e12⟩ := step (boundary := boundary) (mov_m32_r32_low_effect_step 0x101378 5 (.base 3 (.d8 0x54)) (by decide) (by decide) (by decide))
    r12 c12 (MemoryRoutines.Machine.program_text_slice c12 0x1378 3 (by decide +kernel))
    ⟨i12, by rw [show (2 + (AddrMode.base 3 (.d8 0x54)).tail.length) = 2 + 1 from rfl, ha12]; exact writable_slice hsp12.state 0x54 4 (by decide), by
      rw [show (2 + (AddrMode.base 3 (.d8 0x54)).tail.length) = 2 + 1 from rfl, ha12]
      exact (hsp12.stateCode.slice 0x54 4 (by decide)).apart (text_in_program' 0x101378 0x1378 3 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x10137b) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x54) (n := 4)
      (by simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x54)).tail.length) = 2 + 1 from rfl, ha12]) (hsp12.stateCode.slice 0x54 4 (by decide)))
  have g12 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x54) 4, .rip] u12 u13 := by
    have := e12.agrees
    simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x54)).tail.length) = 2 + 1 from rfl, ha12] at this
    exact this
  have i13 : u13.RIP = 0x10137b := e12.rip.trans rfl
  have w12 : memLoad u13.external (st + BitVec.ofNat 64 0x54) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[5].toBitVec := by
    have hw := e12.writes
    simp only [movM32R32LowEffect, storeEffect, Write.AllHold, show (2 + (AddrMode.base 3 (.d8 0x54)).tail.length) = 2 + 1 from rfl, ha12] at hw
    rw [show gprNumber 0 0 5 = 5 from rfl] at hw
    exact hw.trans ((show (Operand.reg 5 : Operand 32).read u12 = (Operand.reg 5 : Operand 32).read u0 from (((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).read (by simp)).trans q5)
  have ss13 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u13.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g12 hsp.stateStack (by decide) h).trans (ss12 off n h)
  have hsp13 : Space sp st input output size u13 := hsp12.transfer g12 (by simp)
  have G13 : AgreesExcept (changes sp st output size) u0 u13 :=
    (G12.trans (g12.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x54 - 0x40 + j, by omega, blk_addr st 0x54 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs13 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u13.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g12 hy (by decide)).trans (fs12 y hy)
  have ha13 : AddrMode.addr (.base 3 (.d8 0x58)) u13 (0x10137b + BitVec.ofNat 64 (3 + 1)) = st + BitVec.ofNat 64 0x58 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u13 = (Operand.reg 3 : Operand 64).read u6 from ((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (by simp)).trans b5) (by decide)
  obtain ⟨u14, a13, r14, c14, e13⟩ := step (boundary := boundary) (mov_m32_r32_effect_step 0x10137b 0x44 (by unfold RexNoWPrefix; decide) 7 (.base 3 (.d8 0x58)) (by decide) (by decide) (by decide))
    r13 c13 (MemoryRoutines.Machine.program_text_slice c13 0x137b 4 (by decide +kernel))
    ⟨i13, by simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x58)).tail.length) = 3 + 1 from rfl, ha13]; exact writable_slice hsp13.state 0x58 4 (by decide), by
      simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x58)).tail.length) = 3 + 1 from rfl, ha13]
      exact (hsp13.stateCode.slice 0x58 4 (by decide)).apart (text_in_program' 0x10137b 0x137b 4 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x10137f) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x58) (n := 4)
      (by simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x58)).tail.length) = 3 + 1 from rfl, ha13]) (hsp13.stateCode.slice 0x58 4 (by decide)))
  have g13 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x58) 4, .rip] u13 u14 := by
    have := e13.agrees
    simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x58)).tail.length) = 3 + 1 from rfl, ha13] at this
    exact this
  have i14 : u14.RIP = 0x10137f := e13.rip.trans rfl
  have w13 : memLoad u14.external (st + BitVec.ofNat 64 0x58) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[6].toBitVec := by
    have hw := e13.writes
    simp only [movM32R32Effect, storeEffect, storeAddrAt, Write.AllHold, show (3 + (AddrMode.base 3 (.d8 0x58)).tail.length) = 3 + 1 from rfl, ha13] at hw
    rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 7 = 15 from rfl] at hw
    exact hw.trans ((show (Operand.reg 15 : Operand 32).read u13 = (Operand.reg 15 : Operand 32).read u0 from ((((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (by simp)).trans q6)
  have ss14 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u14.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g13 hsp.stateStack (by decide) h).trans (ss13 off n h)
  have hsp14 : Space sp st input output size u14 := hsp13.transfer g13 (by simp)
  have G14 : AgreesExcept (changes sp st output size) u0 u14 :=
    (G13.trans (g13.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x58 - 0x40 + j, by omega, blk_addr st 0x58 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs14 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u14.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g13 hy (by decide)).trans (fs13 y hy)
  have ha14 : AddrMode.addr (.base 3 (.d8 0x5c)) u14 (0x10137f + BitVec.ofNat 64 (2 + 1)) = st + BitVec.ofNat 64 0x5c :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u14 = (Operand.reg 3 : Operand 64).read u6 from (((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).read (by simp)).trans b5) (by decide)
  obtain ⟨u15, a14, r15, c15, e14⟩ := step (boundary := boundary) (mov_m32_r32_low_effect_step 0x10137f 6 (.base 3 (.d8 0x5c)) (by decide) (by decide) (by decide))
    r14 c14 (MemoryRoutines.Machine.program_text_slice c14 0x137f 3 (by decide +kernel))
    ⟨i14, by rw [show (2 + (AddrMode.base 3 (.d8 0x5c)).tail.length) = 2 + 1 from rfl, ha14]; exact writable_slice hsp14.state 0x5c 4 (by decide), by
      rw [show (2 + (AddrMode.base 3 (.d8 0x5c)).tail.length) = 2 + 1 from rfl, ha14]
      exact (hsp14.stateCode.slice 0x5c 4 (by decide)).apart (text_in_program' 0x10137f 0x137f 3 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x101382) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x5c) (n := 4)
      (by simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x5c)).tail.length) = 2 + 1 from rfl, ha14]) (hsp14.stateCode.slice 0x5c 4 (by decide)))
  have g14 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x5c) 4, .rip] u14 u15 := by
    have := e14.agrees
    simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x5c)).tail.length) = 2 + 1 from rfl, ha14] at this
    exact this
  have i15 : u15.RIP = 0x101382 := e14.rip.trans rfl
  have w14 : memLoad u15.external (st + BitVec.ofNat 64 0x5c) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[7].toBitVec := by
    have hw := e14.writes
    simp only [movM32R32LowEffect, storeEffect, Write.AllHold, show (2 + (AddrMode.base 3 (.d8 0x5c)).tail.length) = 2 + 1 from rfl, ha14] at hw
    rw [show gprNumber 0 0 6 = 6 from rfl] at hw
    exact hw.trans ((show (Operand.reg 6 : Operand 32).read u14 = (Operand.reg 6 : Operand 32).read u0 from (((((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).read (by simp)).trans q7)
  have ss15 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u15.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g14 hsp.stateStack (by decide) h).trans (ss14 off n h)
  have hsp15 : Space sp st input output size u15 := hsp14.transfer g14 (by simp)
  have G15 : AgreesExcept (changes sp st output size) u0 u15 :=
    (G14.trans (g14.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x5c - 0x40 + j, by omega, blk_addr st 0x5c j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs15 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u15.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g14 hy (by decide)).trans (fs14 y hy)
  have ha15 : AddrMode.addr (.sib 4 none 0 (.d8 0x4)) u15 (0x101382 + BitVec.ofNat 64 (2 + 2)) = sp + BitVec.ofNat 64 0x4 := by
    simp only [AddrMode.addr]; rw [reg64_rsp, hsp15.rsp]; rfl
  obtain ⟨u16, a15, r16, c16, e15⟩ := step (boundary := boundary) (mov_r32_m32_low_effect_step 0x101382 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
    r15 c15 (MemoryRoutines.Machine.program_text_slice c15 0x1382 4 (by decide +kernel))
    ⟨i15, by rw [show (2 + (AddrMode.sib 4 none 0 (.d8 0x4)).tail.length) = 2 + 2 from rfl, ha15]; exact (writable_slice hsp15.stack 0x4 4 (by decide)).readable⟩
    (by intro he; apply ne_boundary hb (p := 0x101386) (by decide) (by decide); rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  rw [show gprNumber 0 0 0 = 0 from rfl] at e15
  have g15 := e15.agrees
  simp only [movR32M32LowEffect_components] at g15
  have i16 : u16.RIP = 0x101386 := e15.rip.trans rfl
  have v15 : (Operand.reg 0 : Operand 32).read u16 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[8].toBitVec := by
    have hw := e15.writes
    simp only [movR32M32LowEffect, Write.AllHold] at hw
    rw [reg32_eq, hw, show (2 + (AddrMode.sib 4 none 0 (.d8 0x4)).tail.length) = 2 + 2 from rfl]
    change ((memLoad u15.external _ 32).setWidth 64).setWidth 32 = _
    rw [ha15, ss15 0x4 32 (by decide), BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    exact q8
  have hx15 : u16.external = u15.external := g15.external (by simp [Component.Covers])
  have ss16 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u16.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (congrArg (fun m ↦ memLoad m (sp + BitVec.ofNat 64 off) n) hx15).trans (ss15 off n h)
  have hsp16 : Space sp st input output size u16 := hsp15.transfer g15 (by simp)
  have G16 : AgreesExcept (changes sp st output size) u0 u16 := (G15.trans (g15.mono (cs' := changes sp st output size) (by simp [changes]))).mono (by simp)
  have fs16 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u16.external[y]? = u0.external[y]? := fun y hy ↦ (congrArg (fun m : Ram ↦ m[y]?) hx15).trans (fs15 y hy)
  have ha16 : AddrMode.addr (.base 3 (.d8 0x60)) u16 (0x101386 + BitVec.ofNat 64 (2 + 1)) = st + BitVec.ofNat 64 0x60 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u16 = (Operand.reg 3 : Operand 64).read u6 from (((((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).read (by simp)).trans b5) (by decide)
  obtain ⟨u17, a16, r17, c17, e16⟩ := step (boundary := boundary) (mov_m32_r32_low_effect_step 0x101386 0 (.base 3 (.d8 0x60)) (by decide) (by decide) (by decide))
    r16 c16 (MemoryRoutines.Machine.program_text_slice c16 0x1386 3 (by decide +kernel))
    ⟨i16, by rw [show (2 + (AddrMode.base 3 (.d8 0x60)).tail.length) = 2 + 1 from rfl, ha16]; exact writable_slice hsp16.state 0x60 4 (by decide), by
      rw [show (2 + (AddrMode.base 3 (.d8 0x60)).tail.length) = 2 + 1 from rfl, ha16]
      exact (hsp16.stateCode.slice 0x60 4 (by decide)).apart (text_in_program' 0x101386 0x1386 3 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x101389) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x60) (n := 4)
      (by simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x60)).tail.length) = 2 + 1 from rfl, ha16]) (hsp16.stateCode.slice 0x60 4 (by decide)))
  have g16 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x60) 4, .rip] u16 u17 := by
    have := e16.agrees
    simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x60)).tail.length) = 2 + 1 from rfl, ha16] at this
    exact this
  have i17 : u17.RIP = 0x101389 := e16.rip.trans rfl
  have w16 : memLoad u17.external (st + BitVec.ofNat 64 0x60) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[8].toBitVec := by
    have hw := e16.writes
    simp only [movM32R32LowEffect, storeEffect, Write.AllHold, show (2 + (AddrMode.base 3 (.d8 0x60)).tail.length) = 2 + 1 from rfl, ha16] at hw
    rw [show gprNumber 0 0 0 = 0 from rfl] at hw
    exact hw.trans v15
  have ss17 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u17.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g16 hsp.stateStack (by decide) h).trans (ss16 off n h)
  have hsp17 : Space sp st input output size u17 := hsp16.transfer g16 (by simp)
  have G17 : AgreesExcept (changes sp st output size) u0 u17 :=
    (G16.trans (g16.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x60 - 0x40 + j, by omega, blk_addr st 0x60 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs17 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u17.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g16 hy (by decide)).trans (fs16 y hy)
  have ha17 : AddrMode.addr (.base 3 (.d8 0x64)) u17 (0x101389 + BitVec.ofNat 64 (3 + 1)) = st + BitVec.ofNat 64 0x64 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u17 = (Operand.reg 3 : Operand 64).read u6 from ((((((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).read (by simp)).trans b5) (by decide)
  obtain ⟨u18, a17, r18, c18, e17⟩ := step (boundary := boundary) (mov_m32_r32_effect_step 0x101389 0x44 (by unfold RexNoWPrefix; decide) 2 (.base 3 (.d8 0x64)) (by decide) (by decide) (by decide))
    r17 c17 (MemoryRoutines.Machine.program_text_slice c17 0x1389 4 (by decide +kernel))
    ⟨i17, by simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x64)).tail.length) = 3 + 1 from rfl, ha17]; exact writable_slice hsp17.state 0x64 4 (by decide), by
      simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x64)).tail.length) = 3 + 1 from rfl, ha17]
      exact (hsp17.stateCode.slice 0x64 4 (by decide)).apart (text_in_program' 0x101389 0x1389 4 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x10138d) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x64) (n := 4)
      (by simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x64)).tail.length) = 3 + 1 from rfl, ha17]) (hsp17.stateCode.slice 0x64 4 (by decide)))
  have g17 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x64) 4, .rip] u17 u18 := by
    have := e17.agrees
    simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x64)).tail.length) = 3 + 1 from rfl, ha17] at this
    exact this
  have i18 : u18.RIP = 0x10138d := e17.rip.trans rfl
  have w17 : memLoad u18.external (st + BitVec.ofNat 64 0x64) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[9].toBitVec := by
    have hw := e17.writes
    simp only [movM32R32Effect, storeEffect, storeAddrAt, Write.AllHold, show (3 + (AddrMode.base 3 (.d8 0x64)).tail.length) = 3 + 1 from rfl, ha17] at hw
    rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 2 = 10 from rfl] at hw
    exact hw.trans ((show (Operand.reg 10 : Operand 32).read u17 = (Operand.reg 10 : Operand 32).read u0 from ((((((((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).read (by simp)).trans q9)
  have ss18 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u18.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g17 hsp.stateStack (by decide) h).trans (ss17 off n h)
  have hsp18 : Space sp st input output size u18 := hsp17.transfer g17 (by simp)
  have G18 : AgreesExcept (changes sp st output size) u0 u18 :=
    (G17.trans (g17.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x64 - 0x40 + j, by omega, blk_addr st 0x64 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs18 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u18.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g17 hy (by decide)).trans (fs17 y hy)
  have ha18 : AddrMode.addr (.base 3 (.d8 0x68)) u18 (0x10138d + BitVec.ofNat 64 (3 + 1)) = st + BitVec.ofNat 64 0x68 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u18 = (Operand.reg 3 : Operand 64).read u6 from (((((((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).read (by simp)).trans b5) (by decide)
  obtain ⟨u19, a18, r19, c19, e18⟩ := step (boundary := boundary) (mov_m32_r32_effect_step 0x10138d 0x44 (by unfold RexNoWPrefix; decide) 6 (.base 3 (.d8 0x68)) (by decide) (by decide) (by decide))
    r18 c18 (MemoryRoutines.Machine.program_text_slice c18 0x138d 4 (by decide +kernel))
    ⟨i18, by simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x68)).tail.length) = 3 + 1 from rfl, ha18]; exact writable_slice hsp18.state 0x68 4 (by decide), by
      simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x68)).tail.length) = 3 + 1 from rfl, ha18]
      exact (hsp18.stateCode.slice 0x68 4 (by decide)).apart (text_in_program' 0x10138d 0x138d 4 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x101391) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x68) (n := 4)
      (by simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x68)).tail.length) = 3 + 1 from rfl, ha18]) (hsp18.stateCode.slice 0x68 4 (by decide)))
  have g18 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x68) 4, .rip] u18 u19 := by
    have := e18.agrees
    simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x68)).tail.length) = 3 + 1 from rfl, ha18] at this
    exact this
  have i19 : u19.RIP = 0x101391 := e18.rip.trans rfl
  have w18 : memLoad u19.external (st + BitVec.ofNat 64 0x68) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[10].toBitVec := by
    have hw := e18.writes
    simp only [movM32R32Effect, storeEffect, storeAddrAt, Write.AllHold, show (3 + (AddrMode.base 3 (.d8 0x68)).tail.length) = 3 + 1 from rfl, ha18] at hw
    rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 6 = 14 from rfl] at hw
    exact hw.trans ((show (Operand.reg 14 : Operand 32).read u18 = (Operand.reg 14 : Operand 32).read u0 from (((((((((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).read (by simp)).trans q10)
  have ss19 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u19.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g18 hsp.stateStack (by decide) h).trans (ss18 off n h)
  have hsp19 : Space sp st input output size u19 := hsp18.transfer g18 (by simp)
  have G19 : AgreesExcept (changes sp st output size) u0 u19 :=
    (G18.trans (g18.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x68 - 0x40 + j, by omega, blk_addr st 0x68 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs19 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u19.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g18 hy (by decide)).trans (fs18 y hy)
  have ha19 : AddrMode.addr (.base 3 (.d8 0x6c)) u19 (0x101391 + BitVec.ofNat 64 (3 + 1)) = st + BitVec.ofNat 64 0x6c :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u19 = (Operand.reg 3 : Operand 64).read u6 from ((((((((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).read (by simp)).trans b5) (by decide)
  obtain ⟨u20, a19, r20, c20, e19⟩ := step (boundary := boundary) (mov_m32_r32_effect_step 0x101391 0x44 (by unfold RexNoWPrefix; decide) 4 (.base 3 (.d8 0x6c)) (by decide) (by decide) (by decide))
    r19 c19 (MemoryRoutines.Machine.program_text_slice c19 0x1391 4 (by decide +kernel))
    ⟨i19, by simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x6c)).tail.length) = 3 + 1 from rfl, ha19]; exact writable_slice hsp19.state 0x6c 4 (by decide), by
      simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x6c)).tail.length) = 3 + 1 from rfl, ha19]
      exact (hsp19.stateCode.slice 0x6c 4 (by decide)).apart (text_in_program' 0x101391 0x1391 4 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x101395) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x6c) (n := 4)
      (by simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x6c)).tail.length) = 3 + 1 from rfl, ha19]) (hsp19.stateCode.slice 0x6c 4 (by decide)))
  have g19 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x6c) 4, .rip] u19 u20 := by
    have := e19.agrees
    simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x6c)).tail.length) = 3 + 1 from rfl, ha19] at this
    exact this
  have i20 : u20.RIP = 0x101395 := e19.rip.trans rfl
  have w19 : memLoad u20.external (st + BitVec.ofNat 64 0x6c) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[11].toBitVec := by
    have hw := e19.writes
    simp only [movM32R32Effect, storeEffect, storeAddrAt, Write.AllHold, show (3 + (AddrMode.base 3 (.d8 0x6c)).tail.length) = 3 + 1 from rfl, ha19] at hw
    rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 4 = 12 from rfl] at hw
    exact hw.trans ((show (Operand.reg 12 : Operand 32).read u19 = (Operand.reg 12 : Operand 32).read u0 from ((((((((((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).read (by simp)).trans q11)
  have ss20 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u20.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g19 hsp.stateStack (by decide) h).trans (ss19 off n h)
  have hsp20 : Space sp st input output size u20 := hsp19.transfer g19 (by simp)
  have G20 : AgreesExcept (changes sp st output size) u0 u20 :=
    (G19.trans (g19.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x6c - 0x40 + j, by omega, blk_addr st 0x6c j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs20 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u20.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g19 hy (by decide)).trans (fs19 y hy)
  have ha20 : AddrMode.addr (.base 3 (.d8 0x70)) u20 (0x101395 + BitVec.ofNat 64 (2 + 1)) = st + BitVec.ofNat 64 0x70 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u20 = (Operand.reg 3 : Operand 64).read u6 from (((((((((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).read (by simp)).trans b5) (by decide)
  obtain ⟨u21, a20, r21, c21, e20⟩ := step (boundary := boundary) (mov_m32_r32_low_effect_step 0x101395 1 (.base 3 (.d8 0x70)) (by decide) (by decide) (by decide))
    r20 c20 (MemoryRoutines.Machine.program_text_slice c20 0x1395 3 (by decide +kernel))
    ⟨i20, by rw [show (2 + (AddrMode.base 3 (.d8 0x70)).tail.length) = 2 + 1 from rfl, ha20]; exact writable_slice hsp20.state 0x70 4 (by decide), by
      rw [show (2 + (AddrMode.base 3 (.d8 0x70)).tail.length) = 2 + 1 from rfl, ha20]
      exact (hsp20.stateCode.slice 0x70 4 (by decide)).apart (text_in_program' 0x101395 0x1395 3 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x101398) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x70) (n := 4)
      (by simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x70)).tail.length) = 2 + 1 from rfl, ha20]) (hsp20.stateCode.slice 0x70 4 (by decide)))
  have g20 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x70) 4, .rip] u20 u21 := by
    have := e20.agrees
    simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x70)).tail.length) = 2 + 1 from rfl, ha20] at this
    exact this
  have i21 : u21.RIP = 0x101398 := e20.rip.trans rfl
  have w20 : memLoad u21.external (st + BitVec.ofNat 64 0x70) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[12].toBitVec := by
    have hw := e20.writes
    simp only [movM32R32LowEffect, storeEffect, Write.AllHold, show (2 + (AddrMode.base 3 (.d8 0x70)).tail.length) = 2 + 1 from rfl, ha20] at hw
    rw [show gprNumber 0 0 1 = 1 from rfl] at hw
    exact hw.trans ((show (Operand.reg 1 : Operand 32).read u20 = (Operand.reg 1 : Operand 32).read u0 from (((((((((((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).read (by simp)).trans q15)
  have ss21 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u21.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g20 hsp.stateStack (by decide) h).trans (ss20 off n h)
  have hsp21 : Space sp st input output size u21 := hsp20.transfer g20 (by simp)
  have G21 : AgreesExcept (changes sp st output size) u0 u21 :=
    (G20.trans (g20.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x70 - 0x40 + j, by omega, blk_addr st 0x70 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs21 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u21.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g20 hy (by decide)).trans (fs20 y hy)
  have ha21 : AddrMode.addr (.base 3 (.d8 0x74)) u21 (0x101398 + BitVec.ofNat 64 (2 + 1)) = st + BitVec.ofNat 64 0x74 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u21 = (Operand.reg 3 : Operand 64).read u6 from ((((((((((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).trans g20).read (by simp)).trans b5) (by decide)
  obtain ⟨u22, a21, r22, c22, e21⟩ := step (boundary := boundary) (mov_m32_r32_low_effect_step 0x101398 2 (.base 3 (.d8 0x74)) (by decide) (by decide) (by decide))
    r21 c21 (MemoryRoutines.Machine.program_text_slice c21 0x1398 3 (by decide +kernel))
    ⟨i21, by rw [show (2 + (AddrMode.base 3 (.d8 0x74)).tail.length) = 2 + 1 from rfl, ha21]; exact writable_slice hsp21.state 0x74 4 (by decide), by
      rw [show (2 + (AddrMode.base 3 (.d8 0x74)).tail.length) = 2 + 1 from rfl, ha21]
      exact (hsp21.stateCode.slice 0x74 4 (by decide)).apart (text_in_program' 0x101398 0x1398 3 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x10139b) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x74) (n := 4)
      (by simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x74)).tail.length) = 2 + 1 from rfl, ha21]) (hsp21.stateCode.slice 0x74 4 (by decide)))
  have g21 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x74) 4, .rip] u21 u22 := by
    have := e21.agrees
    simp only [movM32R32LowEffect, storeEffect_components, show (2 + (AddrMode.base 3 (.d8 0x74)).tail.length) = 2 + 1 from rfl, ha21] at this
    exact this
  have i22 : u22.RIP = 0x10139b := e21.rip.trans rfl
  have w21 : memLoad u22.external (st + BitVec.ofNat 64 0x74) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[13].toBitVec := by
    have hw := e21.writes
    simp only [movM32R32LowEffect, storeEffect, Write.AllHold, show (2 + (AddrMode.base 3 (.d8 0x74)).tail.length) = 2 + 1 from rfl, ha21] at hw
    rw [show gprNumber 0 0 2 = 2 from rfl] at hw
    exact hw.trans ((show (Operand.reg 2 : Operand 32).read u21 = (Operand.reg 2 : Operand 32).read u0 from ((((((((((((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).trans g20).read (by simp)).trans q12)
  have ss22 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u22.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g21 hsp.stateStack (by decide) h).trans (ss21 off n h)
  have hsp22 : Space sp st input output size u22 := hsp21.transfer g21 (by simp)
  have G22 : AgreesExcept (changes sp st output size) u0 u22 :=
    (G21.trans (g21.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x74 - 0x40 + j, by omega, blk_addr st 0x74 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs22 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u22.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g21 hy (by decide)).trans (fs21 y hy)
  have ha22 : AddrMode.addr (.base 3 (.d8 0x78)) u22 (0x10139b + BitVec.ofNat 64 (3 + 1)) = st + BitVec.ofNat 64 0x78 :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u22 = (Operand.reg 3 : Operand 64).read u6 from (((((((((((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).trans g20).trans g21).read (by simp)).trans b5) (by decide)
  obtain ⟨u23, a22, r23, c23, e22⟩ := step (boundary := boundary) (mov_m32_r32_effect_step 0x10139b 0x44 (by unfold RexNoWPrefix; decide) 0 (.base 3 (.d8 0x78)) (by decide) (by decide) (by decide))
    r22 c22 (MemoryRoutines.Machine.program_text_slice c22 0x139b 4 (by decide +kernel))
    ⟨i22, by simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x78)).tail.length) = 3 + 1 from rfl, ha22]; exact writable_slice hsp22.state 0x78 4 (by decide), by
      simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x78)).tail.length) = 3 + 1 from rfl, ha22]
      exact (hsp22.stateCode.slice 0x78 4 (by decide)).apart (text_in_program' 0x10139b 0x139b 4 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x10139f) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x78) (n := 4)
      (by simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x78)).tail.length) = 3 + 1 from rfl, ha22]) (hsp22.stateCode.slice 0x78 4 (by decide)))
  have g22 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x78) 4, .rip] u22 u23 := by
    have := e22.agrees
    simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x78)).tail.length) = 3 + 1 from rfl, ha22] at this
    exact this
  have i23 : u23.RIP = 0x10139f := e22.rip.trans rfl
  have w22 : memLoad u23.external (st + BitVec.ofNat 64 0x78) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[14].toBitVec := by
    have hw := e22.writes
    simp only [movM32R32Effect, storeEffect, storeAddrAt, Write.AllHold, show (3 + (AddrMode.base 3 (.d8 0x78)).tail.length) = 3 + 1 from rfl, ha22] at hw
    rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 0 = 8 from rfl] at hw
    exact hw.trans ((show (Operand.reg 8 : Operand 32).read u22 = (Operand.reg 8 : Operand 32).read u0 from (((((((((((((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).trans g20).trans g21).read (by simp)).trans q13)
  have ss23 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u23.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g22 hsp.stateStack (by decide) h).trans (ss22 off n h)
  have hsp23 : Space sp st input output size u23 := hsp22.transfer g22 (by simp)
  have G23 : AgreesExcept (changes sp st output size) u0 u23 :=
    (G22.trans (g22.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x78 - 0x40 + j, by omega, blk_addr st 0x78 j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs23 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u23.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g22 hy (by decide)).trans (fs22 y hy)
  have ha23 : AddrMode.addr (.base 3 (.d8 0x7c)) u23 (0x10139f + BitVec.ofNat 64 (3 + 1)) = st + BitVec.ofNat 64 0x7c :=
    storeAddr_base _ _ _ _ ((show (Operand.reg 3 : Operand 64).read u23 = (Operand.reg 3 : Operand 64).read u6 from ((((((((((((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).trans g20).trans g21).trans g22).read (by simp)).trans b5) (by decide)
  obtain ⟨u24, a23, r24, c24, e23⟩ := step (boundary := boundary) (mov_m32_r32_effect_step 0x10139f 0x44 (by unfold RexNoWPrefix; decide) 3 (.base 3 (.d8 0x7c)) (by decide) (by decide) (by decide))
    r23 c23 (MemoryRoutines.Machine.program_text_slice c23 0x139f 4 (by decide +kernel))
    ⟨i23, by simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x7c)).tail.length) = 3 + 1 from rfl, ha23]; exact writable_slice hsp23.state 0x7c 4 (by decide), by
      simp only [storeAddrAt]; rw [show (3 + (AddrMode.base 3 (.d8 0x7c)).tail.length) = 3 + 1 from rfl, ha23]
      exact (hsp23.stateCode.slice 0x7c 4 (by decide)).apart (text_in_program' 0x10139f 0x139f 4 (by decide) (by decide +kernel))⟩
    (by intro he; apply ne_boundary hb (p := 0x1013a3) (by decide) (by decide); rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x7c) (n := 4)
      (by simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x7c)).tail.length) = 3 + 1 from rfl, ha23]) (hsp23.stateCode.slice 0x7c 4 (by decide)))
  have g23 : AgreesExcept [.mem (st + BitVec.ofNat 64 0x7c) 4, .rip] u23 u24 := by
    have := e23.agrees
    simp only [movM32R32Effect, storeEffect_components, storeAddrAt, show (3 + (AddrMode.base 3 (.d8 0x7c)).tail.length) = 3 + 1 from rfl, ha23] at this
    exact this
  have i24 : u24.RIP = 0x1013a3 := e23.rip.trans rfl
  have w23 : memLoad u24.external (st + BitVec.ofNat 64 0x7c) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[15].toBitVec := by
    have hw := e23.writes
    simp only [movM32R32Effect, storeEffect, storeAddrAt, Write.AllHold, show (3 + (AddrMode.base 3 (.d8 0x7c)).tail.length) = 3 + 1 from rfl, ha23] at hw
    rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 3 = 11 from rfl] at hw
    exact hw.trans ((show (Operand.reg 11 : Operand 32).read u23 = (Operand.reg 11 : Operand 32).read u0 from ((((((((((((((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).trans g20).trans g21).trans g22).read (by simp)).trans q14)
  have ss24 : ∀ off n, off + n / 8 ≤ 0x170 → memLoad u24.external (sp + BitVec.ofNat 64 off) n = memLoad u0.external (sp + BitVec.ofNat 64 off) n := fun off n h ↦ (store_keeps_stack g23 hsp.stateStack (by decide) h).trans (ss23 off n h)
  have hsp24 : Space sp st input output size u24 := hsp23.transfer g23 (by simp)
  have G24 : AgreesExcept (changes sp st output size) u0 u24 :=
    (G23.trans (g23.widen (cs' := changes sp st output size) (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := hcv
        exact ⟨.mem (st + 0x40) 0x40, by simp [changes], 0x7c - 0x40 + j, by omega, blk_addr st 0x7c j (by decide)⟩
      · exact hcv.elim))).mono (by simp)
  have fs24 : ∀ y, (∀ j < 0x80, y ≠ st + BitVec.ofNat 64 j) → u24.external[y]? = u0.external[y]? :=
    fun y hy ↦ (store_keeps_far g23 hy (by decide)).trans (fs23 y hy)
  have W64 : memLoad u24.external (st + BitVec.ofNat 64 0x40) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[0].toBitVec := ((store_keeps_state (o := 0x40) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x68) g18 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x64) g17 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x60) g16 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx15] : memLoad u16.external (st + BitVec.ofNat 64 0x40) 32 = memLoad u15.external (st + BitVec.ofNat 64 0x40) 32).trans ((store_keeps_state (o := 0x40) (o' := 0x5c) g14 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x58) g13 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x54) g12 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx11] : memLoad u12.external (st + BitVec.ofNat 64 0x40) 32 = memLoad u11.external (st + BitVec.ofNat 64 0x40) 32).trans ((store_keeps_state (o := 0x40) (o' := 0x50) g10 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x4c) g9 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x48) g8 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x40) (o' := 0x44) g7 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx6] : memLoad u7.external (st + BitVec.ofNat 64 0x40) 32 = memLoad u6.external (st + BitVec.ofNat 64 0x40) 32).trans ((by rw [hx5] : memLoad u6.external (st + BitVec.ofNat 64 0x40) 32 = memLoad u5.external (st + BitVec.ofNat 64 0x40) 32).trans w4)))))))))))))))))))
  have W68 : memLoad u24.external (st + BitVec.ofNat 64 0x44) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[1].toBitVec := ((store_keeps_state (o := 0x44) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x68) g18 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x64) g17 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x60) g16 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx15] : memLoad u16.external (st + BitVec.ofNat 64 0x44) 32 = memLoad u15.external (st + BitVec.ofNat 64 0x44) 32).trans ((store_keeps_state (o := 0x44) (o' := 0x5c) g14 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x58) g13 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x54) g12 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx11] : memLoad u12.external (st + BitVec.ofNat 64 0x44) 32 = memLoad u11.external (st + BitVec.ofNat 64 0x44) 32).trans ((store_keeps_state (o := 0x44) (o' := 0x50) g10 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x4c) g9 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x44) (o' := 0x48) g8 hstl (by decide) (by decide) (by decide)).trans w7))))))))))))))))
  have W72 : memLoad u24.external (st + BitVec.ofNat 64 0x48) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[2].toBitVec := ((store_keeps_state (o := 0x48) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x48) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x48) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x48) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x48) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x48) (o' := 0x68) g18 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x48) (o' := 0x64) g17 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x48) (o' := 0x60) g16 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx15] : memLoad u16.external (st + BitVec.ofNat 64 0x48) 32 = memLoad u15.external (st + BitVec.ofNat 64 0x48) 32).trans ((store_keeps_state (o := 0x48) (o' := 0x5c) g14 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x48) (o' := 0x58) g13 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x48) (o' := 0x54) g12 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx11] : memLoad u12.external (st + BitVec.ofNat 64 0x48) 32 = memLoad u11.external (st + BitVec.ofNat 64 0x48) 32).trans ((store_keeps_state (o := 0x48) (o' := 0x50) g10 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x48) (o' := 0x4c) g9 hstl (by decide) (by decide) (by decide)).trans w8)))))))))))))))
  have W76 : memLoad u24.external (st + BitVec.ofNat 64 0x4c) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[3].toBitVec := ((store_keeps_state (o := 0x4c) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x4c) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x4c) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x4c) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x4c) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x4c) (o' := 0x68) g18 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x4c) (o' := 0x64) g17 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x4c) (o' := 0x60) g16 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx15] : memLoad u16.external (st + BitVec.ofNat 64 0x4c) 32 = memLoad u15.external (st + BitVec.ofNat 64 0x4c) 32).trans ((store_keeps_state (o := 0x4c) (o' := 0x5c) g14 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x4c) (o' := 0x58) g13 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x4c) (o' := 0x54) g12 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx11] : memLoad u12.external (st + BitVec.ofNat 64 0x4c) 32 = memLoad u11.external (st + BitVec.ofNat 64 0x4c) 32).trans ((store_keeps_state (o := 0x4c) (o' := 0x50) g10 hstl (by decide) (by decide) (by decide)).trans w9))))))))))))))
  have W80 : memLoad u24.external (st + BitVec.ofNat 64 0x50) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[4].toBitVec := ((store_keeps_state (o := 0x50) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x50) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x50) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x50) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x50) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x50) (o' := 0x68) g18 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x50) (o' := 0x64) g17 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x50) (o' := 0x60) g16 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx15] : memLoad u16.external (st + BitVec.ofNat 64 0x50) 32 = memLoad u15.external (st + BitVec.ofNat 64 0x50) 32).trans ((store_keeps_state (o := 0x50) (o' := 0x5c) g14 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x50) (o' := 0x58) g13 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x50) (o' := 0x54) g12 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx11] : memLoad u12.external (st + BitVec.ofNat 64 0x50) 32 = memLoad u11.external (st + BitVec.ofNat 64 0x50) 32).trans w10)))))))))))))
  have W84 : memLoad u24.external (st + BitVec.ofNat 64 0x54) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[5].toBitVec := ((store_keeps_state (o := 0x54) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x54) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x54) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x54) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x54) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x54) (o' := 0x68) g18 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x54) (o' := 0x64) g17 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x54) (o' := 0x60) g16 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx15] : memLoad u16.external (st + BitVec.ofNat 64 0x54) 32 = memLoad u15.external (st + BitVec.ofNat 64 0x54) 32).trans ((store_keeps_state (o := 0x54) (o' := 0x5c) g14 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x54) (o' := 0x58) g13 hstl (by decide) (by decide) (by decide)).trans w12)))))))))))
  have W88 : memLoad u24.external (st + BitVec.ofNat 64 0x58) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[6].toBitVec := ((store_keeps_state (o := 0x58) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x58) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x58) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x58) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x58) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x58) (o' := 0x68) g18 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x58) (o' := 0x64) g17 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x58) (o' := 0x60) g16 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx15] : memLoad u16.external (st + BitVec.ofNat 64 0x58) 32 = memLoad u15.external (st + BitVec.ofNat 64 0x58) 32).trans ((store_keeps_state (o := 0x58) (o' := 0x5c) g14 hstl (by decide) (by decide) (by decide)).trans w13))))))))))
  have W92 : memLoad u24.external (st + BitVec.ofNat 64 0x5c) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[7].toBitVec := ((store_keeps_state (o := 0x5c) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x5c) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x5c) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x5c) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x5c) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x5c) (o' := 0x68) g18 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x5c) (o' := 0x64) g17 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x5c) (o' := 0x60) g16 hstl (by decide) (by decide) (by decide)).trans ((by rw [hx15] : memLoad u16.external (st + BitVec.ofNat 64 0x5c) 32 = memLoad u15.external (st + BitVec.ofNat 64 0x5c) 32).trans w14)))))))))
  have W96 : memLoad u24.external (st + BitVec.ofNat 64 0x60) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[8].toBitVec := ((store_keeps_state (o := 0x60) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x60) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x60) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x60) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x60) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x60) (o' := 0x68) g18 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x60) (o' := 0x64) g17 hstl (by decide) (by decide) (by decide)).trans w16)))))))
  have W100 : memLoad u24.external (st + BitVec.ofNat 64 0x64) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[9].toBitVec := ((store_keeps_state (o := 0x64) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x64) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x64) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x64) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x64) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x64) (o' := 0x68) g18 hstl (by decide) (by decide) (by decide)).trans w17))))))
  have W104 : memLoad u24.external (st + BitVec.ofNat 64 0x68) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[10].toBitVec := ((store_keeps_state (o := 0x68) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x68) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x68) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x68) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x68) (o' := 0x6c) g19 hstl (by decide) (by decide) (by decide)).trans w18)))))
  have W108 : memLoad u24.external (st + BitVec.ofNat 64 0x6c) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[11].toBitVec := ((store_keeps_state (o := 0x6c) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x6c) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x6c) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x6c) (o' := 0x70) g20 hstl (by decide) (by decide) (by decide)).trans w19))))
  have W112 : memLoad u24.external (st + BitVec.ofNat 64 0x70) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[12].toBitVec := ((store_keeps_state (o := 0x70) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x70) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x70) (o' := 0x74) g21 hstl (by decide) (by decide) (by decide)).trans w20)))
  have W116 : memLoad u24.external (st + BitVec.ofNat 64 0x74) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[13].toBitVec := ((store_keeps_state (o := 0x74) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans ((store_keeps_state (o := 0x74) (o' := 0x78) g22 hstl (by decide) (by decide) (by decide)).trans w21))
  have W120 : memLoad u24.external (st + BitVec.ofNat 64 0x78) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[14].toBitVec := ((store_keeps_state (o := 0x78) (o' := 0x7c) g23 hstl (by decide) (by decide) (by decide)).trans w22)
  have W124 : memLoad u24.external (st + BitVec.ofNat 64 0x7c) 32 = (Vector.ofFn fun i : Fin 16 => (Nat.repeat doubleRound 10 x)[i] + x[i])[15].toBitVec := w23
  have hr9 : (Operand.reg 9 : Operand 64).read u24 = st := ((show (Operand.reg 9 : Operand 64).read u24 = (Operand.reg 9 : Operand 64).read u12 from (((((((((((g12.trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).trans g20).trans g21).trans g22).trans g23).read (by simp)).trans b11)
  have Gt : AgreesExcept (changes sp st output size) t u0 :=
    Gf.widen (by simp [feedScratch, Rounds.regScratch, changes, Component.isMem]) (fun y c hc hcv ↦ by
      obtain ⟨j, hj, rfl⟩ := (feedScratch_good sp).2 c hc y hcv
      exact ⟨.mem sp frameBytes, by simp [changes], j, by unfold frameBytes; omega, rfl⟩)
  refine ⟨_, u24, ((fa1.trans fa2).trans fa3).trans
    (by exact (((((((((((((((((((((((a0.trans a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16).trans a17).trans a18).trans a19).trans a20).trans a21).trans a22).trans a23)),
    r24, c24, (Gt.trans G24).mono (by simp), ?_⟩
  exact
    { rip := i24
      space := hsp24
      slots := ⟨(ss24 0x48 64 (by decide)).trans h48,
        (ss24 0x88 64 (by decide)).trans ((hfoff 0x88 (by decide) (by unfold RoundScratch; omega)).trans h.slots.output),
        (ss24 0x90 64 (by decide)).trans ((hfoff 0x90 (by decide) (by unfold RoundScratch; omega)).trans h.slots.input),
        (ss24 0x98 64 (by decide)).trans ((hfoff 0x98 (by decide) (by unfold RoundScratch; omega)).trans h.slots.head),
        (ss24 0xa0 64 (by decide)).trans ((hfoff 0xa0 (by decide) (by unfold RoundScratch; omega)).trans h.slots.tail),
        (ss24 0xa8 64 (by decide)).trans ((hfoff 0xa8 (by decide) (by unfold RoundScratch; omega)).trans h.slots.length)⟩
      block := words_block hsp24.state (fun i hi ↦ match i, hi with
    | 0, _ => by rw [getElem!_pos _ _ (by decide)]; exact W64
    | 1, _ => by rw [getElem!_pos _ _ (by decide)]; exact W68
    | 2, _ => by rw [getElem!_pos _ _ (by decide)]; exact W72
    | 3, _ => by rw [getElem!_pos _ _ (by decide)]; exact W76
    | 4, _ => by rw [getElem!_pos _ _ (by decide)]; exact W80
    | 5, _ => by rw [getElem!_pos _ _ (by decide)]; exact W84
    | 6, _ => by rw [getElem!_pos _ _ (by decide)]; exact W88
    | 7, _ => by rw [getElem!_pos _ _ (by decide)]; exact W92
    | 8, _ => by rw [getElem!_pos _ _ (by decide)]; exact W96
    | 9, _ => by rw [getElem!_pos _ _ (by decide)]; exact W100
    | 10, _ => by rw [getElem!_pos _ _ (by decide)]; exact W104
    | 11, _ => by rw [getElem!_pos _ _ (by decide)]; exact W108
    | 12, _ => by rw [getElem!_pos _ _ (by decide)]; exact W112
    | 13, _ => by rw [getElem!_pos _ _ (by decide)]; exact W116
    | 14, _ => by rw [getElem!_pos _ _ (by decide)]; exact W120
    | 15, _ => by rw [getElem!_pos _ _ (by decide)]; exact W124
    | n + 16, h => absurd h (by omega))
      state := hr9
      offset := (ss24 0x40 64 (by decide)).trans ((hfoff 0x40 (by decide) (by unfold RoundScratch; omega)).trans h.offset)
      nonzero := h.nonzero
      rest := fun i h1 h2 ↦ by
        have hbT := base_le size
        rw [fs24 _ (fun j hj ↦ by
          rw [in_addr input (size := size) h1]
          exact hsp.inState (i - base size) (by omega) j (by unfold stateBytes; omega)),
          Gf.byte (feed_scratch_nc fun o j _ _ ↦ by
            rw [in_addr input (size := size) h1, add_toNat]
            exact hsp.inStack (i - base size) (by omega) _ (by unfold frameBytes; omega))]
        exact h.rest i h1 h2 }

theorem rem_setup (h : Rem sp st input output size msg x t) :
    Reach boundary sp st output size t (Single sp st input output size msg x (quad size)) := by
  have hsp := h.space
  obtain ⟨u1, a1, r1, c1, e1, i1⟩ := rstep hb (q := 0x101470)
    (lea_r64_effect_step 0x10146c 0x4a (by unfold RexWPrefix; decide) 1 (.sib 6 (some 9) 0 .none)
      (by decide) (by decide) (by decide))
    hr hc (MemoryRoutines.Machine.program_text_slice hc 0x146c 4 (by decide +kernel)) h.rip rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4a)) 1 = 1 from rfl] at e1
  obtain ⟨u2, a2, r2, c2, e2, i2⟩ := rstep hb (q := 0x101474)
    (add_r64_imm8_effect_step 0x101470 0x48 0xc1 0x40 (by unfold RexWPrefix; decide) (by decide)
      (by decide))
    r1 c1 (MemoryRoutines.Machine.program_text_slice c1 0x1470 4 (by decide +kernel)) i1 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x48)) (modrmRm 0xc1) = 1 by decide] at e2
  obtain ⟨u3, a3, r3, c3, e3, i3⟩ := rstep hb (q := 0x101477)
    (add_r64_r64_effect_step 0x101474 0x49 0xf0 (by unfold RexWPrefix; decide) (by decide))
    r2 c2 (MemoryRoutines.Machine.program_text_slice c2 0x1474 3 (by decide +kernel)) i2 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x49)) (modrmRm 0xf0) = 8 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x49)) (modrmReg 0xf0) = 6 by decide] at e3
  obtain ⟨u4, a4, r4, c4, e4, i4⟩ := rstep hb (q := 0x10147a)
    (add_r64_r64_effect_step 0x101477 0x4d 0xf8 (by unfold RexWPrefix; decide) (by decide))
    r3 c3 (MemoryRoutines.Machine.program_text_slice c3 0x1477 3 (by decide +kernel)) i3 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x4d)) (modrmRm 0xf8) = 8 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x4d)) (modrmReg 0xf8) = 15 by decide] at e4
  obtain ⟨u5, a5, r5, c5, e5, i5⟩ := rstep hb (q := 0x10147d)
    (add_r64_r64_effect_step 0x10147a 0x4c 0xc3 (by unfold RexWPrefix; decide) (by decide))
    r4 c4 (MemoryRoutines.Machine.program_text_slice c4 0x147a 3 (by decide +kernel)) i4 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x4c)) (modrmRm 0xc3) = 3 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) (modrmReg 0xc3) = 8 by decide] at e5
  obtain ⟨u6, a6, r6, c6, e6, i6⟩ := rstep hb (q := 0x101480)
    (add_r64_r64_effect_step 0x10147d 0x4d 0xc3 (by unfold RexWPrefix; decide) (by decide))
    r5 c5 (MemoryRoutines.Machine.program_text_slice c5 0x147d 3 (by decide +kernel)) i5 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x4d)) (modrmRm 0xc3) = 11 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x4d)) (modrmReg 0xc3) = 8 by decide] at e6
  obtain ⟨u7, a7, r7, c7, e7, i7⟩ := rstep hb (q := 0x101482)
    (xor_r32_r32_effect_step 0x101480 0xd2 (by decide))
    r6 c6 (MemoryRoutines.Machine.program_text_slice c6 0x1480 2 (by decide +kernel)) i6 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 0 (modrmRm 0xd2) = 2 by decide,
    show gprNumber 0 0 (modrmReg 0xd2) = 2 by decide] at e7
  obtain ⟨w, a8, r8, c8, e8, i8⟩ := rstep hb (q := 0x101490)
    (nop_m_effect_step 0x101482 [0x66, 0x66, 0x66, 0x66, 0x66, 0x2e] (by decide) (by decide)
      (.sib 0 (some 0) 0 (.d32 0)) (by decide) (by decide) (by decide))
    r7 c7 (MemoryRoutines.Machine.program_text_slice c7 0x1482 14 (by decide +kernel)) i7 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  have g1 := e1.agrees
  have g2 := e2.agrees
  have g3 := e3.agrees
  have g4 := e4.agrees
  have g5 := e5.agrees
  have g6 := e6.agrees
  have g7 := e7.agrees
  have g8 := e8.agrees
  simp only [leaR64Effect_components] at g1
  simp only [addR64Imm8Effect_components] at g2
  simp only [addR64R64Effect_components] at g3 g4 g5 g6
  simp only [xorR32R32Effect_components] at g7
  simp only [nopEffect_components] at g8
  have hq4 := h.nonzero
  have hT : tail size < 64 := Nat.mod_lt _ (by decide)
  have hbT := base_le size
  have hinl := hsp.inLow
  have houl := hsp.outLow
  have hstl := hsp.state.low
  have v1 : (Operand.reg 1 : Operand 64).read u1 = BitVec.ofNat 64 (quad size) + st := by
    have hw := e1.writes
    simp only [leaR64Effect, Write.AllHold] at hw
    rw [hw]
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((6 : BitVec 4).setWidth 5) = 6 from rfl, show ((9 : BitVec 4).setWidth 5) = 9 from rfl,
      show (Operand.reg 6 : Operand 64).read t = _ from h.index,
      show (Operand.reg 9 : Operand 64).read t = _ from h.state,
      show BitVec.toNat (0 : BitVec 2) = 0 from rfl, BitVec.shiftLeft_zero]
    simp
  have v2 : (Operand.reg 1 : Operand 64).read u2 = BitVec.ofNat 64 (quad size) + st + 0x40 := by
    have hw := e2.writes
    simp only [addR64Imm8Effect, Write.AllHold] at hw
    rw [hw, v1]; rfl
  have v3 : (Operand.reg 8 : Operand 64).read u3 = BitVec.ofNat 64 (quad size) := by
    have hw := e3.writes
    simp only [addR64R64Effect, Write.AllHold] at hw
    rw [hw, (g1.trans g2).read (by simp), (g1.trans g2).read (by simp),
      show (Operand.reg 8 : Operand 64).read t = _ from h.head,
      show (Operand.reg 6 : Operand 64).read t = _ from h.index]
    simp
  have v4 : (Operand.reg 8 : Operand 64).read u4 =
      BitVec.ofNat 64 (quad size) + BitVec.ofNat 64 (base size) := by
    have hw := e4.writes
    simp only [addR64R64Effect, Write.AllHold] at hw
    rw [hw, v3, ((g1.trans g2).trans g3).read (by simp),
      show (Operand.reg 15 : Operand 64).read t = _ from h.offset]
  have v5 : (Operand.reg 3 : Operand 64).read u5 =
      output + (BitVec.ofNat 64 (quad size) + BitVec.ofNat 64 (base size)) := by
    have hw := e5.writes
    simp only [addR64R64Effect, Write.AllHold] at hw
    rw [hw, v4, show (Operand.reg 3 : Operand 64).read u4 = (Operand.reg 3 : Operand 64).read t from
      (((g1.trans g2).trans g3).trans g4).read (by simp),
      show (Operand.reg 3 : Operand 64).read t = _ from h.outPtr]
  have v6 : (Operand.reg 11 : Operand 64).read u6 =
      input + (BitVec.ofNat 64 (quad size) + BitVec.ofNat 64 (base size)) := by
    have hw := e6.writes
    simp only [addR64R64Effect, Write.AllHold] at hw
    rw [hw, show (Operand.reg 8 : Operand 64).read u5 = (Operand.reg 8 : Operand 64).read u4 from
      g5.read (by simp), v4,
      show (Operand.reg 11 : Operand 64).read u5 = (Operand.reg 11 : Operand 64).read t from
      ((((g1.trans g2).trans g3).trans g4).trans g5).read (by simp),
      show (Operand.reg 11 : Operand 64).read t = _ from h.inPtr]
  have v7 : (Operand.reg 2 : Operand 64).read u7 = 0 := by
    have hw := e7.writes
    simp only [xorR32R32Effect, Write.AllHold] at hw
    rw [hw]; simp
  have G := (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8)
  have hx : w.external = t.external := G.external (by simp [Component.Covers])
  refine ⟨1 + 1 + 1 + 1 + 1 + 1 + 1 + 1, w,
    (((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8),
    r8, c8, G.mono (by simp [changes]), ?_⟩
  exact
    { rip := i8
      space := hsp.transfer G (by simp)
      block := fun i ↦ by rw [hx]; exact h.block i
      ge := Nat.le_refl _
      lt := by unfold quad; omega
      state := (G.read (by simp)).trans h.state
      index := by
        rw [show reg64 w 2 = _ from (g8.read (by simp)), v7, Nat.sub_self]; rfl
      src := by
        rw [show reg64 w 1 = _ from (((((g3.trans g4).trans g5).trans g6).trans g7).trans g8).read
          (by simp), v2]
        bv_omega
      inPtr := by
        rw [show reg64 w 11 = _ from ((g7.trans g8).read (by simp)), v6]
        unfold inTail; bv_omega
      outPtr := by
        rw [show reg64 w 3 = _ from (((g6.trans g7).trans g8).read (by simp)), v5]
        unfold outTail; bv_omega
      rem := (G.read (by simp)).trans h.rem
      tail := (G.read (by simp)).trans h.tail
      rest := fun i h1 h2 ↦ by rw [hx]; exact h.rest i h1 h2
      wrote := fun i h1 h2 ↦ by rw [hx]; exact h.wrote i h1 h2 }

theorem keyed_head (h : Keyed sp st input output size msg x t) :
    Reach boundary sp st output size t (Branched sp st input output size msg x) := by
  have hsp := h.space
  have houl := hsp.outLow
  have hT : tail size < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨u1, a1, r1, c1, g1, i1, v1⟩ := load_slot hb hr hc hsp 0x1013a3 0x1013ab 0x4c
    (by unfold RexWPrefix; decide) 2 (.d32 0xa8) 0xa8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (MemoryRoutines.Machine.program_text_slice hc 0x13a3 8 (by decide +kernel))
    h.rip (by decide) (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 2 = 10 from rfl, h.slots.length] at v1
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 2 = 10 from rfl] at g1
  obtain ⟨u2, a2, r2, c2, e2, i2⟩ := rstep hb (q := 0x1013ae)
    (mov_r32_r32_rex_effect_step 0x1013ab 0x44 0xd0 (by unfold RexNoWPrefix; decide) (by decide))
    r1 c1 (MemoryRoutines.Machine.program_text_slice c1 0x13ab 3 (by decide +kernel)) i1 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x44)) (modrmRm 0xd0) = 0 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) (modrmReg 0xd0) = 10 by decide] at e2
  obtain ⟨u3, a3, r3, c3, e3, i3⟩ := rstep hb (q := 0x1013b1)
    (and_r32_imm8_effect_step 0x1013ae 0xe0 3 (by decide) (by decide))
    r2 c2 (MemoryRoutines.Machine.program_text_slice c2 0x13ae 3 (by decide +kernel)) i2 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 0 (modrmRm 0xe0) = 0 by decide] at e3
  have g2 := e2.agrees
  have g3 := e3.agrees
  simp only [movR32R32Effect_components] at g2
  simp only [andR32Imm8Effect_components] at g3
  have hx3 : u3.external = t.external :=
    ((g1.trans g2).trans g3).external (by simp [Component.Covers])
  obtain ⟨u4, a4, r4, c4, g4, i4, v4⟩ := load_slot hb r3 c3 (hsp.transfer ((g1.trans g2).trans g3)
      (by simp)) 0x1013b1 0x1013b9 0x4c
    (by unfold RexWPrefix; decide) 6 (.d32 0xa0) 0xa0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (MemoryRoutines.Machine.program_text_slice c3 0x13b1 8 (by decide +kernel))
    i3 (by decide) (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 6 = 14 from rfl, slot_ext hx3,
    h.slots.tail] at v4
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 6 = 14 from rfl] at g4
  obtain ⟨u5, a5, r5, c5, e5, i5⟩ := rstep hb (q := 0x1013bd)
    (cmp_r32_imm8_rex_effect_step 0x1013b9 0x41 0xfe 4 (by unfold RexNoWPrefix; decide) (by decide)
      (by decide))
    r4 c4 (MemoryRoutines.Machine.program_text_slice c4 0x13b9 4 (by decide +kernel)) i4 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x41)) (modrmRm 0xfe) = 14 by decide] at e5
  have g5 := e5.agrees
  simp only [cmpR32Imm8Effect_components] at g5
  have hCF : (StatusFlags.ofRFLAGS u5.RFLAGS).CF = decide (tail size < 4) := by
    obtain ⟨hC, -⟩ := e5.flags
    change _ = (cmpSpec _ _).CF at hC
    rw [hC]
    have h32 : (Operand.reg 14 : Operand 32).read u4 = BitVec.ofNat 32 (tail size) := by
      have := congrArg (BitVec.setWidth 32) v4
      simpa [Operand.read, BitVec.setWidth_setWidth_of_le] using this
    rw [h32, show BitVec.signExtend 32 (4 : BitVec 8) = 4 from by decide]
    simp only [cmpSpec, subSpec, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl
  have hj : (jccEffect 0x1013bd 2 3 ((0x24 : BitVec 8).signExtend 64) u5).rip =
      if tail size < 4 then 0x1013bf else 0x1013e3 := by
    simp only [jccEffect, branchEffect, condHolds_3, hCF]
    by_cases he : tail size < 4 <;> simp [he] <;> rfl
  obtain ⟨w, a6, r6, c6, e6⟩ := step (boundary := boundary)
    (jcc_rel8_effect_step 0x1013bd 3 0x24)
    r5 c5 (MemoryRoutines.Machine.program_text_slice c5 0x13bd 2 (by decide +kernel))
    ⟨i5, fun _ ↦ by decide⟩
    (by rw [hj]; exact ne_boundary hb (by split <;> decide) (by split <;> decide))
    (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _)
  have g6 := e6.agrees
  simp only [jccEffect, branchEffect_components] at g6
  have G := (((((g1.trans g2).trans g3).trans g4).trans g5).trans g6)
  have hx : w.external = t.external := G.external (by simp [Component.Covers])
  have v3 : (Operand.reg 0 : Operand 64).read u3 = BitVec.ofNat 64 (tail size % 4) := by
    have hw3 := e3.writes
    have hw2 := e2.writes
    simp only [andR32Imm8Effect, Write.AllHold] at hw3
    simp only [movR32R32Effect, Write.AllHold] at hw2
    rw [hw3]
    have h0 : (Operand.reg 0 : Operand 32).read u2 = BitVec.ofNat 32 size := by
      have e0 : (Operand.reg 0 : Operand 32).read u2 =
          ((Operand.reg 0 : Operand 64).read u2).setWidth 32 := by simp [Operand.read]
      have e10 : (Operand.reg 10 : Operand 32).read u1 =
          ((Operand.reg 10 : Operand 64).read u1).setWidth 32 := by simp [Operand.read]
      rw [e0, hw2, e10, v1]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    rw [h0, show BitVec.signExtend 32 (3 : BitVec 8) = 3 from by decide]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (3 : BitVec 32).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    unfold tail
    omega
  refine ⟨_, w, ((((a1.trans a2).trans a3).trans a4).trans a5).trans a6, r6, c6,
    G.mono (by simp [changes]), ?_⟩
  have hreg (r : BitVec 5) (h0 : r ≠ 0) (h10 : r ≠ 10) (h14 : r ≠ 14) :
      (Operand.reg r : Operand 64).read w = (Operand.reg r : Operand 64).read t :=
    G.read (by simp; exact ⟨h10, h0, h14⟩)
  exact
    { rip := e6.rip.trans hj
      space := hsp.transfer G (by simp)
      slots := h.slots.ext hx
      block := fun i ↦ by rw [hx]; exact h.block i
      state := (hreg 9 (by decide) (by decide) (by decide)).trans h.state
      offset := (slot_ext hx _ _).trans h.offset
      nonzero := h.nonzero
      rest := fun i h1 h2 ↦ by rw [hx]; exact h.rest i h1 h2
      length := by
        rw [show reg64 w 10 = _ from ((((g2.trans g3).trans g4).trans g5).trans g6).read
          (by simp)]
        exact v1
      rem := by
        rw [show reg64 w 0 = _ from (((g4.trans g5).trans g6).read (by simp))]
        exact v3
      tail := by
        rw [show reg64 w 14 = _ from ((g5.trans g6).read (by simp))]
        exact v4 }

theorem keyed_quad (h : Keyed sp st input output size msg x t) (hq : 4 ≤ tail size) :
    Reach boundary sp st output size t (Quad sp st input output size msg x 0) := by
  refine (keyed_head boundary hb hr hc h).trans fun u ru cu hu ↦ ?_
  have hsp := hu.space
  have houl := hsp.outLow
  have hs32 : size < 2 ^ 32 := by unfold tail at hq; omega
  have hip : u.RIP = 0x1013e3 := by rw [hu.rip]; simp [show ¬ tail size < 4 by omega]
  obtain ⟨u1, a1, r1, c1, e1, i1⟩ := rstep hb (q := 0x1013e7)
    (and_r32_imm8_rex_effect_step 0x1013e3 0x41 0xe2 0x3c (by unfold RexNoWPrefix; decide)
      (by decide) (by decide))
    ru cu (MemoryRoutines.Machine.program_text_slice cu 0x13e3 4 (by decide +kernel)) hip rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x41)) (modrmRm 0xe2) = 10 by decide] at e1
  have g1 := e1.agrees
  simp only [andR32Imm8Effect_components] at g1
  have v1 : (Operand.reg 10 : Operand 64).read u1 = BitVec.ofNat 64 (quad size) := by
    have hw := e1.writes
    simp only [andR32Imm8Effect, Write.AllHold] at hw
    rw [hw]
    have e10 : (Operand.reg 10 : Operand 32).read u =
        ((Operand.reg 10 : Operand 64).read u).setWidth 32 := by simp [Operand.read]
    rw [e10, show (Operand.reg 10 : Operand 64).read u = _ from hu.length,
      show BitVec.signExtend 32 (0x3c : BitVec 8) = 0x3c from by decide]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (0x3c : BitVec 32).toNat = 60 from rfl, Nat.mod_eq_of_lt (a := size) (by omega),
      Nat.mod_eq_of_lt (a := size) (by omega), Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left
        (by omega)), and60]
    unfold quad tail
    have : size % 64 - size % 64 % 4 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this]
  have hx1 : u1.external = u.external := g1.external (by simp [Component.Covers])
  obtain ⟨u2, a2, r2, c2, g2, i2, v2⟩ := load_slot hb r1 c1 (hsp.transfer g1 (by simp)) 0x1013e7
    0x1013ef 0x4c (by unfold RexWPrefix; decide) 0 (.d32 0x98) 0x98 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (MemoryRoutines.Machine.program_text_slice c1 0x13e7 8 (by decide +kernel)) i1 (by decide)
    (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 0 = 8 from rfl, slot_ext hx1,
    hu.slots.head] at v2
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 0 = 8 from rfl] at g2
  have hx2 : u2.external = u.external := (g2.external (by simp [Component.Covers])).trans hx1
  obtain ⟨u3, a3, r3, c3, g3, i3, v3⟩ := load_slot hb r2 c2
    (hsp.transfer (g1.trans g2) (by simp)) 0x1013ef
    0x1013f4 0x4c (by unfold RexWPrefix; decide) 7 (.d8 0x40) 0x40 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (MemoryRoutines.Machine.program_text_slice c2 0x13ef 5 (by decide +kernel)) i2 (by decide)
    (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 7 = 15 from rfl, slot_ext hx2,
    hu.offset] at v3
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 7 = 15 from rfl] at g3
  have hx3 : u3.external = u.external := (g3.external (by simp [Component.Covers])).trans hx2
  obtain ⟨u4, a4, r4, c4, e4, i4⟩ := rstep hb (q := 0x1013f8)
    (lea_r64_effect_step 0x1013f4 0x4b (by unfold RexWPrefix; decide) 2 (.sib 8 (some 15) 0 .none)
      (by decide) (by decide) (by decide))
    r3 c3 (MemoryRoutines.Machine.program_text_slice c3 0x13f4 4 (by decide +kernel)) i3 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4b)) 2 = 2 from rfl] at e4
  have g4 := e4.agrees
  simp only [leaR64Effect_components] at g4
  have v4 : (Operand.reg 2 : Operand 64).read u4 = BitVec.ofNat 64 (base size) := by
    have hw := e4.writes
    simp only [leaR64Effect, Write.AllHold] at hw
    rw [hw]
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((8 : BitVec 4).setWidth 5) = 8 from rfl, show ((15 : BitVec 4).setWidth 5) = 15 from rfl,
      show (Operand.reg 8 : Operand 64).read u3 = _ from (g3.read (by simp)).trans v2, v3,
      show BitVec.toNat (0 : BitVec 2) = 0 from rfl, BitVec.shiftLeft_zero]
    simp
  have hx4 : u4.external = u.external := (g4.external (by simp [Component.Covers])).trans hx3
  obtain ⟨u5, a5, r5, c5, g5, i5, v5⟩ := load_slot hb r4 c4
    (hsp.transfer (((g1.trans g2).trans g3).trans g4) (by simp)) 0x1013f8
    0x101400 0x4c (by unfold RexWPrefix; decide) 3 (.d32 0x90) 0x90 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (MemoryRoutines.Machine.program_text_slice c4 0x13f8 8 (by decide +kernel)) i4 (by decide)
    (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 3 = 11 from rfl, slot_ext hx4,
    hu.slots.input] at v5
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 3 = 11 from rfl] at g5
  have hx5 : u5.external = u.external := (g5.external (by simp [Component.Covers])).trans hx4
  obtain ⟨u6, a6, r6, c6, e6, i6⟩ := rstep hb (q := 0x101404)
    (lea_r64_effect_step 0x101400 0x49 (by unfold RexWPrefix; decide) 1 (.sib 11 (some 2) 0 .none)
      (by decide) (by decide) (by decide))
    r5 c5 (MemoryRoutines.Machine.program_text_slice c5 0x1400 4 (by decide +kernel)) i5 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x49)) 1 = 1 from rfl] at e6
  have g6 := e6.agrees
  simp only [leaR64Effect_components] at g6
  have v6 : (Operand.reg 1 : Operand 64).read u6 = input + BitVec.ofNat 64 (base size) := by
    have hw := e6.writes
    simp only [leaR64Effect, Write.AllHold] at hw
    rw [hw]
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((11 : BitVec 4).setWidth 5) = 11 from rfl, show ((2 : BitVec 4).setWidth 5) = 2 from rfl,
      v5, show (Operand.reg 2 : Operand 64).read u5 = _ from (g5.read (by simp)).trans v4,
      show BitVec.toNat (0 : BitVec 2) = 0 from rfl, BitVec.shiftLeft_zero]
    simp
  obtain ⟨u7, a7, r7, c7, e7, i7⟩ := rstep hb (q := 0x101408)
    (add_r64_imm8_effect_step 0x101404 0x48 0xc1 0x03 (by unfold RexWPrefix; decide) (by decide)
      (by decide))
    r6 c6 (MemoryRoutines.Machine.program_text_slice c6 0x1404 4 (by decide +kernel)) i6 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x48)) (modrmRm 0xc1) = 1 by decide] at e7
  have g7 := e7.agrees
  simp only [addR64Imm8Effect_components] at g7
  have v7 : (Operand.reg 1 : Operand 64).read u7 = inTail input size + 3 := by
    have hw := e7.writes
    simp only [addR64Imm8Effect, Write.AllHold] at hw
    rw [hw, v6, show BitVec.signExtend 64 (0x03 : BitVec 8) = 3 from by decide]
    rfl
  have hx7 : u7.external = u.external :=
    ((g6.trans g7).external (by simp [Component.Covers])).trans hx5
  obtain ⟨u8, a8, r8, c8, g8, i8, v8⟩ := load_slot hb r7 c7
    (hsp.transfer (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7))
      (by simp)) 0x101408
    0x101410 0x48 (by unfold RexWPrefix; decide) 3 (.d32 0x88) 0x88 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (MemoryRoutines.Machine.program_text_slice c7 0x1408 8 (by decide +kernel)) i7 (by decide)
    (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x48)) 3 = 3 from rfl, slot_ext hx7,
    hu.slots.output] at v8
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x48)) 3 = 3 from rfl] at g8
  obtain ⟨u9, a9, r9, c9, e9, i9⟩ := rstep hb (q := 0x101413)
    (add_r64_r64_effect_step 0x101410 0x48 0xda (by unfold RexWPrefix; decide) (by decide))
    r8 c8 (MemoryRoutines.Machine.program_text_slice c8 0x1410 3 (by decide +kernel)) i8 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x48)) (modrmRm 0xda) = 2 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (modrmReg 0xda) = 3 by decide] at e9
  have g9 := e9.agrees
  simp only [addR64R64Effect_components] at g9
  have v9 : (Operand.reg 2 : Operand 64).read u9 = outTail output size := by
    have hw := e9.writes
    simp only [addR64R64Effect, Write.AllHold] at hw
    rw [hw, v8, show (Operand.reg 2 : Operand 64).read u8 = _ from
      ((((g5.trans g6).trans g7).trans g8).read (by simp)).trans v4]
    unfold outTail
    exact BitVec.add_comm _ _
  obtain ⟨u10, a10, r10, c10, e10, i10⟩ := rstep hb (q := 0x101417)
    (add_r64_imm8_effect_step 0x101413 0x48 0xc2 0x03 (by unfold RexWPrefix; decide) (by decide)
      (by decide))
    r9 c9 (MemoryRoutines.Machine.program_text_slice c9 0x1413 4 (by decide +kernel)) i9 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x48)) (modrmRm 0xc2) = 2 by decide] at e10
  have g10 := e10.agrees
  simp only [addR64Imm8Effect_components] at g10
  have v10 : (Operand.reg 2 : Operand 64).read u10 = outTail output size + 3 := by
    have hw := e10.writes
    simp only [addR64Imm8Effect, Write.AllHold] at hw
    rw [hw, v9, show BitVec.signExtend 64 (0x03 : BitVec 8) = 3 from by decide]
  obtain ⟨u11, a11, r11, c11, e11, i11⟩ := rstep hb (q := 0x101419)
    (xor_r32_r32_effect_step 0x101417 0xf6 (by decide))
    r10 c10 (MemoryRoutines.Machine.program_text_slice c10 0x1417 2 (by decide +kernel)) i10 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 0 (modrmRm 0xf6) = 6 by decide,
    show gprNumber 0 0 (modrmReg 0xf6) = 6 by decide] at e11
  have g11 := e11.agrees
  simp only [xorR32R32Effect_components] at g11
  obtain ⟨w, a12, r12, c12, e12, i12⟩ := rstep hb (q := 0x101420)
    (nop_m_effect_step 0x101419 [] (by decide) (by decide) (.base 0 (.d32 0)) (by decide) (by decide)
      (by decide))
    r11 c11 (MemoryRoutines.Machine.program_text_slice c11 0x1419 7 (by decide +kernel)) i11 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  have g12 := e12.agrees
  simp only [nopEffect_components] at g12
  have G := ((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans
    g9).trans g10).trans g11).trans g12
  have hx : w.external = u.external := G.external (by simp [Component.Covers])
  refine ⟨_, w, ((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans
    a8).trans a9).trans a10).trans a11).trans a12, r12, c12, G.mono (by simp [changes]), ?_⟩
  have hreg (r : BitVec 5) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h6 : r ≠ 6) (h8 : r ≠ 8)
      (h10 : r ≠ 10) (h11 : r ≠ 11) (h15 : r ≠ 15) :
      (Operand.reg r : Operand 64).read w = (Operand.reg r : Operand 64).read u :=
    G.read (by simp; (repeat' apply And.intro) <;> assumption)
  exact
    { rip := i12
      space := hsp.transfer G (by simp)
      block := fun i ↦ by rw [hx]; exact hu.block i
      aligned := rfl
      lt := by unfold quad; omega
      state := (hreg 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hu.state
      index := by
        have hw := e11.writes
        simp only [xorR32R32Effect, Write.AllHold] at hw
        rw [show reg64 w 6 = _ from g12.read (by simp), hw]; simp
      src := by
        rw [show reg64 w 1 = _ from (((((g8.trans g9).trans g10).trans g11).trans g12).read
          (by simp)), v7]
      dst := by rw [show reg64 w 2 = _ from ((g11.trans g12).read (by simp)), v10]
      bound := by
        rw [show reg64 w 10 = _ from
          ((((((((((g2.trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans
            g10).trans g11).trans g12).read (by simp), v1]
      rem := (hreg 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hu.rem
      tail := (hreg 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hu.tail
      head := by
        rw [show reg64 w 8 = _ from
          (((((((((g3.trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans
            g11).trans g12).read (by simp), v2]
      offset := by
        rw [show reg64 w 15 = _ from
          ((((((((g4.trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans
            g12).read (by simp), v3]
      inPtr := by
        rw [show reg64 w 11 = _ from
          ((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (by simp), v5]
      outPtr := by
        rw [show reg64 w 3 = _ from ((((g9.trans g10).trans g11).trans g12).read (by simp)), v8]
      rest := fun i h1 h2 ↦ by rw [hx]; exact hu.rest i (by omega) h2
      wrote := fun i h1 h2 ↦ by omega }

theorem keyed_short (h : Keyed sp st input output size msg x t) (hq : tail size < 4) :
    Reach boundary sp st output size t (Single sp st input output size msg x 0) := by
  have hq0 : quad size = 0 := by unfold quad; omega
  refine (keyed_head boundary hb hr hc h).trans fun u ru cu hu ↦ ?_
  have hsp := hu.space
  have hip : u.RIP = 0x1013bf := by rw [hu.rip]; simp [hq]
  obtain ⟨u1, a1, r1, c1, e1, i1⟩ := rstep hb (q := 0x1013c1)
    (xor_r32_r32_effect_step 0x1013bf 0xf6 (by decide))
    ru cu (MemoryRoutines.Machine.program_text_slice cu 0x13bf 2 (by decide +kernel)) hip rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 0 (modrmRm 0xf6) = 6 by decide,
    show gprNumber 0 0 (modrmReg 0xf6) = 6 by decide] at e1
  have g1 := e1.agrees
  simp only [xorR32R32Effect_components] at g1
  have hx1 : u1.external = u.external := g1.external (by simp [Component.Covers])
  obtain ⟨u2, a2, r2, c2, g2, i2, v2⟩ := load_slot hb r1 c1 (hsp.transfer g1 (by simp)) 0x1013c1
    0x1013c9 0x4c (by unfold RexWPrefix; decide) 0 (.d32 0x98) 0x98 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (MemoryRoutines.Machine.program_text_slice c1 0x13c1 8 (by decide +kernel)) i1 (by decide)
    (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 0 = 8 from rfl] at v2 g2
  have hx2 : u2.external = u.external := (g2.external (by simp [Component.Covers])).trans hx1
  obtain ⟨u3, a3, r3, c3, g3, i3, v3⟩ := load_slot hb r2 c2
    (hsp.transfer (g1.trans g2) (by simp)) 0x1013c9
    0x1013d1 0x4c (by unfold RexWPrefix; decide) 3 (.d32 0x90) 0x90 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (MemoryRoutines.Machine.program_text_slice c2 0x13c9 8 (by decide +kernel)) i2 (by decide)
    (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 3 = 11 from rfl] at v3 g3
  have hx3 : u3.external = u.external := (g3.external (by simp [Component.Covers])).trans hx2
  obtain ⟨u4, a4, r4, c4, g4, i4, v4⟩ := load_slot hb r3 c3
    (hsp.transfer ((g1.trans g2).trans g3) (by simp)) 0x1013d1
    0x1013d9 0x48 (by unfold RexWPrefix; decide) 3 (.d32 0x88) 0x88 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (MemoryRoutines.Machine.program_text_slice c3 0x13d1 8 (by decide +kernel)) i3 (by decide)
    (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x48)) 3 = 3 from rfl] at v4 g4
  have hx4 : u4.external = u.external := (g4.external (by simp [Component.Covers])).trans hx3
  obtain ⟨u5, a5, r5, c5, g5, i5, v5⟩ := load_slot hb r4 c4
    (hsp.transfer (((g1.trans g2).trans g3).trans g4) (by simp)) 0x1013d9
    0x1013de 0x4c (by unfold RexWPrefix; decide) 7 (.d8 0x40) 0x40 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (MemoryRoutines.Machine.program_text_slice c4 0x13d9 5 (by decide +kernel)) i4 (by decide)
    (by decide) (by decide)
  rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 7 = 15 from rfl] at v5 g5
  have hx5 : u5.external = u.external := (g5.external (by simp [Component.Covers])).trans hx4
  obtain ⟨w, a6, r6, c6, e6, i6⟩ := rstep hb (q := 0x10146c)
    (jmp_rel32_effect_step 0x1013de 0x89 (by decide))
    r5 c5 (MemoryRoutines.Machine.program_text_slice c5 0x13de 5 (by decide +kernel)) i5 rfl
    (by decide) (by decide) (by simp [jmpEffect_components, Component.isMem])
  have g6 := e6.agrees
  simp only [jmpEffect_components] at g6
  have hx : w.external = u.external := (g6.external (by simp [Component.Covers])).trans hx5
  have G := ((((g1.trans g2).trans g3).trans g4).trans g5).trans g6
  refine Reach.trans (P := Rem sp st input output size msg x)
    ⟨_, w, ((((a1.trans a2).trans a3).trans a4).trans a5).trans a6, r6, c6,
      G.mono (by simp [changes]), ?_⟩
    fun v rv cv hv ↦ by rw [← hq0]; exact rem_setup boundary hb rv cv hv
  have hreg (r : BitVec 5) (h6 : r ≠ 6) (h8 : r ≠ 8) (h11 : r ≠ 11) (h3 : r ≠ 3) (h15 : r ≠ 15) :
      (Operand.reg r : Operand 64).read w = (Operand.reg r : Operand 64).read u :=
    G.read (by simp; exact ⟨h6, h8, h11, h3, h15⟩)
  have hT : tail size ≠ 0 := hu.nonzero
  exact
    { rip := i6
      space := hsp.transfer G (by simp)
      block := fun i ↦ by rw [hx]; exact hu.block i
      nonzero := by omega
      state := (hreg 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hu.state
      index := by
        rw [hq0, show reg64 w 6 = _ from (((((g2.trans g3).trans g4).trans g5).trans g6).read
          (by simp))]
        have hw := e1.writes
        simp only [xorR32R32Effect, Write.AllHold] at hw
        rw [hw]; simp
      head := by
        rw [show reg64 w 8 = _ from ((((g3.trans g4).trans g5).trans g6).read (by simp)), v2,
          slot_ext hx1, hu.slots.head]
      offset := by
        rw [show reg64 w 15 = _ from (g6.read (by simp)), v5, slot_ext hx4, hu.offset]
      inPtr := by
        rw [show reg64 w 11 = _ from (((g4.trans g5).trans g6).read (by simp)), v3,
          slot_ext hx2, hu.slots.input]
      outPtr := by
        rw [show reg64 w 3 = _ from ((g5.trans g6).read (by simp)), v4, slot_ext hx3,
          hu.slots.output]
      rem := (hreg 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hu.rem
      tail := (hreg 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hu.tail
      rest := fun i h1 h2 ↦ by rw [hx]; exact hu.rest i (by omega) h2
      wrote := fun i h1 h2 ↦ by omega }

set_option maxHeartbeats 2000000 in
theorem quad_body {j : Nat} (h : Quad sp st input output size msg x j t) :
    Reach boundary sp st output size t (QuadNext sp st input output size msg x (j + 4)) := by
  have hsp := h.space
  have hT : tail size < 64 := Nat.mod_lt _ (by decide)
  have hbT := base_le size
  have hq4 : quad size % 4 = 0 := by unfold quad; omega
  have hqT : quad size ≤ tail size := by unfold quad; omega
  have hj4 : j + 4 ≤ quad size := by have := h.lt; have := h.aligned; omega
  have hinl := hsp.inLow
  have houl := hsp.outLow
  have hstl := hsp.state.low
  have hst : stateBytes = 0x80 := rfl
  have hAL0 : AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x40)) t 0x101426 =
      st + BitVec.ofNat 64 (0x40 + (j + 0)) := by
    rw [sib_val (b := 9) (d := (.d8 0x40)) _ (show (Operand.reg 9 : Operand 64).read t = _ from h.state) (show (Operand.reg 6 : Operand 64).read t = _ from h.index)]
    simp only [Disp.value]
    rw [show BitVec.signExtend 64 (0x40 : BitVec 8) = BitVec.ofNat 64 0x40 from by decide,
      addL, show 0x40 + j = 0x40 + (j + 0) by omega]
  have hAX0 : AddrMode.addr (.sib 1 (some 6) 0 (.d8 0xfd)) t 0x10142b =
      input + BitVec.ofNat 64 (base size + (j + 0)) := by
    rw [sib_val (b := 1) (d := (.d8 0xfd)) _ (show (Operand.reg 1 : Operand 64).read t = _ from h.src) (show (Operand.reg 6 : Operand 64).read t = _ from h.index)]
    simp only [Disp.value]
    rw [show BitVec.signExtend 64 (0xfd : BitVec 8) = BitVec.ofNat 64 (2 ^ 64 - 3 + 0) from by decide, addX _ _ 0]
    unfold inTail
    rw [tail_add]
  have hAS0 : AddrMode.addr (.sib 2 (some 6) 0 (.d8 0xfd)) t 0x101430 =
      output + BitVec.ofNat 64 (base size + (j + 0)) := by
    rw [sib_val (b := 2) (d := (.d8 0xfd)) _ (show (Operand.reg 2 : Operand 64).read t = _ from h.dst) (show (Operand.reg 6 : Operand 64).read t = _ from h.index)]
    simp only [Disp.value]
    rw [show BitVec.signExtend 64 (0xfd : BitVec 8) = BitVec.ofNat 64 (2 ^ 64 - 3 + 0) from by decide, addX _ _ 0]
    unfold outTail
    rw [tail_add]
  have hkb0 : t.external[st + BitVec.ofNat 64 (0x40 + (j + 0))]? =
      some (stream x)[j + 0] := by
    have := h.block ⟨j + 0, by omega⟩
    rwa [addB] at this
  have hmb0 : t.external[input + BitVec.ofNat 64 (base size + (j + 0))]? =
      some (msg (base size + (j + 0))) := by
    exact h.rest _ (by omega) (by omega)
  have hoa0 : output + BitVec.ofNat 64 (base size + (j + 0)) =
      outTail output size + BitVec.ofNat 64 (j + 0) := by
    rw [out_addr output (size := size) (i := base size + (j + 0)) (by omega),
      Nat.add_sub_cancel_left]
  obtain ⟨t1, a0, r1, c1, g0, i1, w0⟩ := xor_byte (boundary := boundary)
    hr hc 0x101420 0x101426 0x10142b 0x101430 9 1 2 (.d8 0x40) (.d8 0xfd) (.d8 0xfd)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun u cu ↦ ⟨MemoryRoutines.Machine.program_text_slice cu 0x1420 6 (by decide +kernel),
      MemoryRoutines.Machine.program_text_slice cu 0x1426 5 (by decide +kernel),
      MemoryRoutines.Machine.program_text_slice cu 0x142b 5 (by decide +kernel)⟩)
    (ne_boundary hb (by decide) (by decide)) (ne_boundary hb (by decide) (by decide))
    (ne_boundary hb (by decide) (by decide)) 5 rfl
    (text_in_program' 0x10142b 0x142b 5 (by decide) (by decide +kernel))
    h.rip hAL0 hAX0 hAS0 hkb0 hmb0
    (by rw [toNat_add_ofNat (by omega)]; rw [hst] at hstl; omega)
    (by rw [toNat_add_ofNat (by omega)]; omega)
    (by rw [hoa0]; exact writable_grow (writable_slice (hsp.out (by omega)) (j + 0) 1 (by omega)) (AgreesExcept.refl [] t))
    (by rw [hoa0]; exact hsp.outCode.slice (j + 0) 1 (by omega))
  have G1 : AgreesExcept [.reg 7, .flags, .rip, .mem (output + BitVec.ofNat 64 (base size + (j + 0))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 1))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 2))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 3))) 1] t t1 := g0.mono (by simp)
  have hAL1 : AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x41)) t1 0x101436 =
      st + BitVec.ofNat 64 (0x40 + (j + 1)) := by
    rw [sib_val (b := 9) (d := (.d8 0x41)) _ ((show (Operand.reg 9 : Operand 64).read t1 = (Operand.reg 9 : Operand 64).read t from G1.read (by simp)).trans h.state) ((show (Operand.reg 6 : Operand 64).read t1 = (Operand.reg 6 : Operand 64).read t from G1.read (by simp)).trans h.index)]
    simp only [Disp.value]
    rw [show BitVec.signExtend 64 (0x41 : BitVec 8) = BitVec.ofNat 64 0x41 from by decide,
      addL, show 0x41 + j = 0x40 + (j + 1) by omega]
  have hAX1 : AddrMode.addr (.sib 1 (some 6) 0 (.d8 0xfe)) t1 0x10143b =
      input + BitVec.ofNat 64 (base size + (j + 1)) := by
    rw [sib_val (b := 1) (d := (.d8 0xfe)) _ ((show (Operand.reg 1 : Operand 64).read t1 = (Operand.reg 1 : Operand 64).read t from G1.read (by simp)).trans h.src) ((show (Operand.reg 6 : Operand 64).read t1 = (Operand.reg 6 : Operand 64).read t from G1.read (by simp)).trans h.index)]
    simp only [Disp.value]
    rw [show BitVec.signExtend 64 (0xfe : BitVec 8) = BitVec.ofNat 64 (2 ^ 64 - 3 + 1) from by decide, addX _ _ 1]
    unfold inTail
    rw [tail_add]
  have hAS1 : AddrMode.addr (.sib 2 (some 6) 0 (.d8 0xfe)) t1 0x101440 =
      output + BitVec.ofNat 64 (base size + (j + 1)) := by
    rw [sib_val (b := 2) (d := (.d8 0xfe)) _ ((show (Operand.reg 2 : Operand 64).read t1 = (Operand.reg 2 : Operand 64).read t from G1.read (by simp)).trans h.dst) ((show (Operand.reg 6 : Operand 64).read t1 = (Operand.reg 6 : Operand 64).read t from G1.read (by simp)).trans h.index)]
    simp only [Disp.value]
    rw [show BitVec.signExtend 64 (0xfe : BitVec 8) = BitVec.ofNat 64 (2 ^ 64 - 3 + 1) from by decide, addX _ _ 1]
    unfold outTail
    rw [tail_add]
  have hkb1 : t1.external[st + BitVec.ofNat 64 (0x40 + (j + 1))]? =
      some (stream x)[j + 1] := by
    rw [keep7 g0
      (hsp.state_out_ne (by rw [hst]; omega) (by omega) (by omega))]
    have := h.block ⟨j + 1, by omega⟩
    rwa [addB] at this
  have hmb1 : t1.external[input + BitVec.ofNat 64 (base size + (j + 1))]? =
      some (msg (base size + (j + 1))) := by
    rw [keep7 g0
      (hsp.in_out_ne (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact h.rest _ (by omega) (by omega)
  have hoa1 : output + BitVec.ofNat 64 (base size + (j + 1)) =
      outTail output size + BitVec.ofNat 64 (j + 1) := by
    rw [out_addr output (size := size) (i := base size + (j + 1)) (by omega),
      Nat.add_sub_cancel_left]
  obtain ⟨t2, a1, r2, c2, g1, i2, w1⟩ := xor_byte (boundary := boundary)
    r1 c1 0x101430 0x101436 0x10143b 0x101440 9 1 2 (.d8 0x41) (.d8 0xfe) (.d8 0xfe)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun u cu ↦ ⟨MemoryRoutines.Machine.program_text_slice cu 0x1430 6 (by decide +kernel),
      MemoryRoutines.Machine.program_text_slice cu 0x1436 5 (by decide +kernel),
      MemoryRoutines.Machine.program_text_slice cu 0x143b 5 (by decide +kernel)⟩)
    (ne_boundary hb (by decide) (by decide)) (ne_boundary hb (by decide) (by decide))
    (ne_boundary hb (by decide) (by decide)) 5 rfl
    (text_in_program' 0x10143b 0x143b 5 (by decide) (by decide +kernel))
    i1 hAL1 hAX1 hAS1 hkb1 hmb1
    (by rw [toNat_add_ofNat (by omega)]; rw [hst] at hstl; omega)
    (by rw [toNat_add_ofNat (by omega)]; omega)
    (by rw [hoa1]; exact writable_grow (writable_slice (hsp.out (by omega)) (j + 1) 1 (by omega)) G1)
    (by rw [hoa1]; exact hsp.outCode.slice (j + 1) 1 (by omega))
  have G2 : AgreesExcept [.reg 7, .flags, .rip, .mem (output + BitVec.ofNat 64 (base size + (j + 0))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 1))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 2))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 3))) 1] t t2 := (G1.trans g1).mono (by simp)
  have hAL2 : AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x42)) t2 0x101446 =
      st + BitVec.ofNat 64 (0x40 + (j + 2)) := by
    rw [sib_val (b := 9) (d := (.d8 0x42)) _ ((show (Operand.reg 9 : Operand 64).read t2 = (Operand.reg 9 : Operand 64).read t from G2.read (by simp)).trans h.state) ((show (Operand.reg 6 : Operand 64).read t2 = (Operand.reg 6 : Operand 64).read t from G2.read (by simp)).trans h.index)]
    simp only [Disp.value]
    rw [show BitVec.signExtend 64 (0x42 : BitVec 8) = BitVec.ofNat 64 0x42 from by decide,
      addL, show 0x42 + j = 0x40 + (j + 2) by omega]
  have hAX2 : AddrMode.addr (.sib 1 (some 6) 0 (.d8 0xff)) t2 0x10144b =
      input + BitVec.ofNat 64 (base size + (j + 2)) := by
    rw [sib_val (b := 1) (d := (.d8 0xff)) _ ((show (Operand.reg 1 : Operand 64).read t2 = (Operand.reg 1 : Operand 64).read t from G2.read (by simp)).trans h.src) ((show (Operand.reg 6 : Operand 64).read t2 = (Operand.reg 6 : Operand 64).read t from G2.read (by simp)).trans h.index)]
    simp only [Disp.value]
    rw [show BitVec.signExtend 64 (0xff : BitVec 8) = BitVec.ofNat 64 (2 ^ 64 - 3 + 2) from by decide, addX _ _ 2]
    unfold inTail
    rw [tail_add]
  have hAS2 : AddrMode.addr (.sib 2 (some 6) 0 (.d8 0xff)) t2 0x101450 =
      output + BitVec.ofNat 64 (base size + (j + 2)) := by
    rw [sib_val (b := 2) (d := (.d8 0xff)) _ ((show (Operand.reg 2 : Operand 64).read t2 = (Operand.reg 2 : Operand 64).read t from G2.read (by simp)).trans h.dst) ((show (Operand.reg 6 : Operand 64).read t2 = (Operand.reg 6 : Operand 64).read t from G2.read (by simp)).trans h.index)]
    simp only [Disp.value]
    rw [show BitVec.signExtend 64 (0xff : BitVec 8) = BitVec.ofNat 64 (2 ^ 64 - 3 + 2) from by decide, addX _ _ 2]
    unfold outTail
    rw [tail_add]
  have hkb2 : t2.external[st + BitVec.ofNat 64 (0x40 + (j + 2))]? =
      some (stream x)[j + 2] := by
    rw [keep7 g1
      (hsp.state_out_ne (by rw [hst]; omega) (by omega) (by omega))]
    rw [keep7 g0
      (hsp.state_out_ne (by rw [hst]; omega) (by omega) (by omega))]
    have := h.block ⟨j + 2, by omega⟩
    rwa [addB] at this
  have hmb2 : t2.external[input + BitVec.ofNat 64 (base size + (j + 2))]? =
      some (msg (base size + (j + 2))) := by
    rw [keep7 g1
      (hsp.in_out_ne (by omega) (by omega) (by omega) (by omega) (by omega))]
    rw [keep7 g0
      (hsp.in_out_ne (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact h.rest _ (by omega) (by omega)
  have hoa2 : output + BitVec.ofNat 64 (base size + (j + 2)) =
      outTail output size + BitVec.ofNat 64 (j + 2) := by
    rw [out_addr output (size := size) (i := base size + (j + 2)) (by omega),
      Nat.add_sub_cancel_left]
  obtain ⟨t3, a2, r3, c3, g2, i3, w2⟩ := xor_byte (boundary := boundary)
    r2 c2 0x101440 0x101446 0x10144b 0x101450 9 1 2 (.d8 0x42) (.d8 0xff) (.d8 0xff)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun u cu ↦ ⟨MemoryRoutines.Machine.program_text_slice cu 0x1440 6 (by decide +kernel),
      MemoryRoutines.Machine.program_text_slice cu 0x1446 5 (by decide +kernel),
      MemoryRoutines.Machine.program_text_slice cu 0x144b 5 (by decide +kernel)⟩)
    (ne_boundary hb (by decide) (by decide)) (ne_boundary hb (by decide) (by decide))
    (ne_boundary hb (by decide) (by decide)) 5 rfl
    (text_in_program' 0x10144b 0x144b 5 (by decide) (by decide +kernel))
    i2 hAL2 hAX2 hAS2 hkb2 hmb2
    (by rw [toNat_add_ofNat (by omega)]; rw [hst] at hstl; omega)
    (by rw [toNat_add_ofNat (by omega)]; omega)
    (by rw [hoa2]; exact writable_grow (writable_slice (hsp.out (by omega)) (j + 2) 1 (by omega)) G2)
    (by rw [hoa2]; exact hsp.outCode.slice (j + 2) 1 (by omega))
  have G3 : AgreesExcept [.reg 7, .flags, .rip, .mem (output + BitVec.ofNat 64 (base size + (j + 0))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 1))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 2))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 3))) 1] t t3 := (G2.trans g2).mono (by simp)
  have hAL3 : AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x43)) t3 0x101456 =
      st + BitVec.ofNat 64 (0x40 + (j + 3)) := by
    rw [sib_val (b := 9) (d := (.d8 0x43)) _ ((show (Operand.reg 9 : Operand 64).read t3 = (Operand.reg 9 : Operand 64).read t from G3.read (by simp)).trans h.state) ((show (Operand.reg 6 : Operand 64).read t3 = (Operand.reg 6 : Operand 64).read t from G3.read (by simp)).trans h.index)]
    simp only [Disp.value]
    rw [show BitVec.signExtend 64 (0x43 : BitVec 8) = BitVec.ofNat 64 0x43 from by decide,
      addL, show 0x43 + j = 0x40 + (j + 3) by omega]
  have hAX3 : AddrMode.addr (.sib 1 (some 6) 0 .none) t3 0x10145a =
      input + BitVec.ofNat 64 (base size + (j + 3)) := by
    rw [sib_val (b := 1) (d := .none) _ ((show (Operand.reg 1 : Operand 64).read t3 = (Operand.reg 1 : Operand 64).read t from G3.read (by simp)).trans h.src) ((show (Operand.reg 6 : Operand 64).read t3 = (Operand.reg 6 : Operand 64).read t from G3.read (by simp)).trans h.index)]
    simp only [Disp.value]
    rw [addX3]
    unfold inTail
    rw [tail_add]
  have hAS3 : AddrMode.addr (.sib 2 (some 6) 0 .none) t3 0x10145e =
      output + BitVec.ofNat 64 (base size + (j + 3)) := by
    rw [sib_val (b := 2) (d := .none) _ ((show (Operand.reg 2 : Operand 64).read t3 = (Operand.reg 2 : Operand 64).read t from G3.read (by simp)).trans h.dst) ((show (Operand.reg 6 : Operand 64).read t3 = (Operand.reg 6 : Operand 64).read t from G3.read (by simp)).trans h.index)]
    simp only [Disp.value]
    rw [addX3]
    unfold outTail
    rw [tail_add]
  have hkb3 : t3.external[st + BitVec.ofNat 64 (0x40 + (j + 3))]? =
      some (stream x)[j + 3] := by
    rw [keep7 g2
      (hsp.state_out_ne (by rw [hst]; omega) (by omega) (by omega))]
    rw [keep7 g1
      (hsp.state_out_ne (by rw [hst]; omega) (by omega) (by omega))]
    rw [keep7 g0
      (hsp.state_out_ne (by rw [hst]; omega) (by omega) (by omega))]
    have := h.block ⟨j + 3, by omega⟩
    rwa [addB] at this
  have hmb3 : t3.external[input + BitVec.ofNat 64 (base size + (j + 3))]? =
      some (msg (base size + (j + 3))) := by
    rw [keep7 g2
      (hsp.in_out_ne (by omega) (by omega) (by omega) (by omega) (by omega))]
    rw [keep7 g1
      (hsp.in_out_ne (by omega) (by omega) (by omega) (by omega) (by omega))]
    rw [keep7 g0
      (hsp.in_out_ne (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact h.rest _ (by omega) (by omega)
  have hoa3 : output + BitVec.ofNat 64 (base size + (j + 3)) =
      outTail output size + BitVec.ofNat 64 (j + 3) := by
    rw [out_addr output (size := size) (i := base size + (j + 3)) (by omega),
      Nat.add_sub_cancel_left]
  obtain ⟨t4, a3, r4, c4, g3, i4, w3⟩ := xor_byte (boundary := boundary)
    r3 c3 0x101450 0x101456 0x10145a 0x10145e 9 1 2 (.d8 0x43) .none .none
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun u cu ↦ ⟨MemoryRoutines.Machine.program_text_slice cu 0x1450 6 (by decide +kernel),
      MemoryRoutines.Machine.program_text_slice cu 0x1456 4 (by decide +kernel),
      MemoryRoutines.Machine.program_text_slice cu 0x145a 4 (by decide +kernel)⟩)
    (ne_boundary hb (by decide) (by decide)) (ne_boundary hb (by decide) (by decide))
    (ne_boundary hb (by decide) (by decide)) 4 rfl
    (text_in_program' 0x10145a 0x145a 4 (by decide) (by decide +kernel))
    i3 hAL3 hAX3 hAS3 hkb3 hmb3
    (by rw [toNat_add_ofNat (by omega)]; rw [hst] at hstl; omega)
    (by rw [toNat_add_ofNat (by omega)]; omega)
    (by rw [hoa3]; exact writable_grow (writable_slice (hsp.out (by omega)) (j + 3) 1 (by omega)) G3)
    (by rw [hoa3]; exact hsp.outCode.slice (j + 3) 1 (by omega))
  have G4 : AgreesExcept [.reg 7, .flags, .rip, .mem (output + BitVec.ofNat 64 (base size + (j + 0))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 1))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 2))) 1,
      .mem (output + BitVec.ofNat 64 (base size + (j + 3))) 1] t t4 := (G3.trans g3).mono (by simp)
  obtain ⟨u5, a5, r5, c5, e5, i5⟩ := rstep hb (q := 0x101462)
    (add_r64_imm8_effect_step 0x10145e 0x48 0xc6 0x04 (by unfold RexWPrefix; decide) (by decide)
      (by decide))
    r4 c4 (MemoryRoutines.Machine.program_text_slice c4 0x145e 4 (by decide +kernel)) i4 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x48)) (modrmRm 0xc6) = 6 by decide] at e5
  have g5 := e5.agrees
  simp only [addR64Imm8Effect_components] at g5
  have G4' := G4
  have v5 : (Operand.reg 6 : Operand 64).read u5 = BitVec.ofNat 64 (j + 4) := by
    have hw := e5.writes
    simp only [addR64Imm8Effect, Write.AllHold] at hw
    rw [hw, show (Operand.reg 6 : Operand 64).read t4 = (Operand.reg 6 : Operand 64).read t from
      G4'.read (by simp), show (Operand.reg 6 : Operand 64).read t = _ from h.index,
      show BitVec.signExtend 64 (0x04 : BitVec 8) = BitVec.ofNat 64 4 from by decide,
      ← BitVec.ofNat_add]
  obtain ⟨u6, a6, r6, c6, e6, i6⟩ := rstep hb (q := 0x101465)
    (cmp_r64_r64_effect_step 0x101462 0x49 0xf2 (by unfold RexWPrefix; decide) (by decide))
    r5 c5 (MemoryRoutines.Machine.program_text_slice c5 0x1462 3 (by decide +kernel)) i5 rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x49)) (modrmRm 0xf2) = 10 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x49)) (modrmReg 0xf2) = 6 by decide] at e6
  have g6 := e6.agrees
  simp only [cmpR64R64Effect_components] at g6
  have hZF : (StatusFlags.ofRFLAGS u6.RFLAGS).ZF = decide (j + 4 = quad size) := by
    obtain ⟨-, -, -, hZ, -⟩ := e6.flags
    change _ = (cmpSpec _ _).ZF at hZ
    rw [hZ, cmpSpec_ZF, v5, show (Operand.reg 10 : Operand 64).read u5 =
      (Operand.reg 10 : Operand 64).read t from (G4'.trans g5).read (by simp),
      show (Operand.reg 10 : Operand 64).read t = _ from h.bound]
    by_cases he : j + 4 = quad size
    · simp [he]
    · simp only [he, decide_false]
      rw [beq_eq_false_iff_ne]
      intro hv
      have := congrArg BitVec.toNat hv
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at this
      omega
  have hjq : j + 4 < quad size ↔ ¬ (j + 4 = quad size) := by omega
  have hj7 : (jccEffect 0x101465 2 5 ((0xb9 : BitVec 8).signExtend 64) u6).rip =
      if j + 4 < quad size then 0x101420 else 0x101467 := by
    simp only [jccEffect, branchEffect, condHolds_5, hZF]
    by_cases he : j + 4 = quad size <;> simp [he, hjq] <;> rfl
  obtain ⟨w, a7, r7, c7, e7⟩ := step (boundary := boundary)
    (jcc_rel8_effect_step 0x101465 5 0xb9)
    r6 c6 (MemoryRoutines.Machine.program_text_slice c6 0x1465 2 (by decide +kernel))
    ⟨i6, fun _ ↦ by decide⟩
    (by rw [hj7]; exact ne_boundary hb (by split <;> decide) (by split <;> decide))
    (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _)
  have i7 := e7.rip.trans hj7
  have g7 := e7.agrees
  simp only [jccEffect, branchEffect_components] at g7
  have g567 := (g5.trans g6).trans g7
  have hx4 : w.external = t4.external := g567.external (by simp [Component.Covers])
  have Gw := G4.trans g567
  have hreg (r : BitVec 5) (hr7 : r ≠ 7) (hr6 : r ≠ 6) :
      (Operand.reg r : Operand 64).read w = (Operand.reg r : Operand 64).read t :=
    Gw.read (by simp; exact ⟨hr7, hr6⟩)
  have hback (y : BitVec 64) (h0 : y ≠ output + BitVec.ofNat 64 (base size + (j + 0)))
      (h1 : y ≠ output + BitVec.ofNat 64 (base size + (j + 1)))
      (h2 : y ≠ output + BitVec.ofNat 64 (base size + (j + 2)))
      (h3 : y ≠ output + BitVec.ofNat 64 (base size + (j + 3))) :
      w.external[y]? = t.external[y]? := by
    rw [hx4, keep7 g3 h3, keep7 g2 h2, keep7 g1 h1, keep7 g0 h0]
  have hmem (y : BitVec 64) (k : Nat) (hk : k < 4)
      (hy : y = output + BitVec.ofNat 64 (base size + (j + k))) :
      ∃ c' ∈ changes sp st output size, c'.Covers y :=
    ⟨.mem (outTail output size) (tail size), by simp [changes], j + k, by omega, by
      rw [hy, out_addr output (size := size) (i := base size + (j + k)) (by omega),
        Nat.add_sub_cancel_left]⟩
  have G4c : AgreesExcept (changes sp st output size) t t4 := by
    refine G4.widen (by simp [changes, Component.isMem]) (fun y c hc hcv ↦ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc | hc | hc | hc | hc <;> subst hc <;>
      simp only [Component.Covers] at hcv
    · obtain ⟨k, hk, rfl⟩ := hcv; exact hmem _ 0 (by omega) (by rw [show k = 0 by omega, BitVec.add_zero])
    · obtain ⟨k, hk, rfl⟩ := hcv; exact hmem _ 1 (by omega) (by rw [show k = 0 by omega, BitVec.add_zero])
    · obtain ⟨k, hk, rfl⟩ := hcv; exact hmem _ 2 (by omega) (by rw [show k = 0 by omega, BitVec.add_zero])
    · obtain ⟨k, hk, rfl⟩ := hcv; exact hmem _ 3 (by omega) (by rw [show k = 0 by omega, BitVec.add_zero])
  have g567c : AgreesExcept (changes sp st output size) t4 w := g567.mono (by simp [changes])
  have hchg : AgreesExcept (changes sp st output size) t w := (G4c.trans g567c).mono (by simp)
  refine ⟨_, w, ((((((a0.trans a1).trans a2).trans a3).trans a5).trans a6).trans a7), r7, c7,
    hchg, ?_⟩
  have hO (i k : Nat) (hi : base size ≤ i) (hi' : i < size) (hk : k < 4) (hne : i ≠ base size + (j + k)) :
      output + BitVec.ofNat 64 i ≠ output + BitVec.ofNat 64 (base size + (j + k)) :=
    hsp.out_ne hi' (by omega) hne
  exact
    { rip := i7
      space := hsp.transfer Gw (by simp)
      block := fun i ↦ by
        rw [addB, hback _ (hsp.state_out_ne (by rw [hst]; omega) (by omega) (by omega))
          (hsp.state_out_ne (by rw [hst]; omega) (by omega) (by omega))
          (hsp.state_out_ne (by rw [hst]; omega) (by omega) (by omega))
          (hsp.state_out_ne (by rw [hst]; omega) (by omega) (by omega)), ← addB]
        exact h.block i
      aligned := by have := h.aligned; omega
      le := hj4
      state := (hreg 9 (by decide) (by decide)).trans h.state
      index := by
        have : (Operand.reg 6 : Operand 64).read w = (Operand.reg 6 : Operand 64).read u5 :=
          (g6.trans g7).read (by simp)
        exact this.trans v5
      src := (hreg 1 (by decide) (by decide)).trans h.src
      dst := (hreg 2 (by decide) (by decide)).trans h.dst
      bound := (hreg 10 (by decide) (by decide)).trans h.bound
      rem := (hreg 0 (by decide) (by decide)).trans h.rem
      tail := (hreg 14 (by decide) (by decide)).trans h.tail
      head := (hreg 8 (by decide) (by decide)).trans h.head
      offset := (hreg 15 (by decide) (by decide)).trans h.offset
      inPtr := (hreg 11 (by decide) (by decide)).trans h.inPtr
      outPtr := (hreg 3 (by decide) (by decide)).trans h.outPtr
      rest := fun i hi1 hi2 ↦ by
        rw [hback _ (hsp.in_out_ne (by omega) hi2 (by omega) (by omega) (by omega))
          (hsp.in_out_ne (by omega) hi2 (by omega) (by omega) (by omega))
          (hsp.in_out_ne (by omega) hi2 (by omega) (by omega) (by omega))
          (hsp.in_out_ne (by omega) hi2 (by omega) (by omega) (by omega))]
        exact h.rest i (by omega) hi2
      wrote := fun i hi1 hi2 ↦ by
        by_cases hlt : i < base size + j
        · rw [hback _ (hO i 0 hi1 (by omega) (by omega) (by omega))
            (hO i 1 hi1 (by omega) (by omega) (by omega)) (hO i 2 hi1 (by omega) (by omega) (by omega))
            (hO i 3 hi1 (by omega) (by omega) (by omega))]
          exact h.wrote i hi1 hlt
        · have hc4 : i = base size + (j + 0) ∨ i = base size + (j + 1) ∨ i = base size + (j + 2) ∨
              i = base size + (j + 3) := by omega
          rcases hc4 with rfl | rfl | rfl | rfl
          · rw [hx4, keep7 g3 (hO _ 3 hi1 (by omega) (by omega) (by omega)), keep7 g2 (hO _ 2 hi1 (by omega) (by omega) (by omega)),
              keep7 g1 (hO _ 1 hi1 (by omega) (by omega) (by omega)), w0, Nat.add_sub_cancel_left,
              getElem!_pos (stream x) _ (by omega)]
          · rw [hx4, keep7 g3 (hO _ 3 hi1 (by omega) (by omega) (by omega)), keep7 g2 (hO _ 2 hi1 (by omega) (by omega) (by omega)),
              w1, Nat.add_sub_cancel_left, getElem!_pos (stream x) _ (by omega)]
          · rw [hx4, keep7 g3 (hO _ 3 hi1 (by omega) (by omega) (by omega)), w2, Nat.add_sub_cancel_left,
              getElem!_pos (stream x) _ (by omega)]
          · rw [hx4, w3, Nat.add_sub_cancel_left, getElem!_pos (stream x) _ (by omega)] }

theorem quad_exit (h : QuadNext sp st input output size msg x (quad size) t)
    (hip : t.RIP = 0x101467) :
    Reach boundary sp st output size t fun u ↦
      if tail size % 4 = 0 then Done sp st input output size msg x u
      else Single sp st input output size msg x (quad size) u := by
  have hsp := h.space
  have hbT := base_le size
  obtain ⟨u1, a1, r1, c1, e1, i1⟩ := rstep hb (q := 0x10146a)
    (test_r64_r64_effect_step 0x101467 0x48 0xc0 (by unfold RexWPrefix; decide) (by decide))
    hr hc (MemoryRoutines.Machine.program_text_slice hc 0x1467 3 (by decide +kernel)) hip rfl
    (by decide) (by decide) (by simp [Component.isMem])
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x48)) (modrmRm 0xc0) = 0 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (modrmReg 0xc0) = 0 by decide] at e1
  have g1 := e1.agrees
  simp only [testR64R64Effect_components] at g1
  have hZF : (StatusFlags.ofRFLAGS u1.RFLAGS).ZF = decide (tail size % 4 = 0) := by
    obtain ⟨-, -, -, hZ, -⟩ := e1.flags
    have h0 : (Operand.reg 0 : Operand 64).read t = BitVec.ofNat 64 (tail size % 4) := h.rem
    simp only [testFlags, FlagAllows, h0, BitVec.and_self] at hZ
    rw [hZ]
    by_cases he : tail size % 4 = 0
    · simp [he]
    · simp only [he, decide_false]
      rw [beq_eq_false_iff_ne]
      intro hv
      have := congrArg BitVec.toNat hv
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact he this
  have hj : (jccEffect 0x10146a 2 4 ((0x38 : BitVec 8).signExtend 64) u1).rip =
      if tail size % 4 = 0 then 0x1014a4 else 0x10146c := by
    simp only [jccEffect, branchEffect, condHolds_4, hZF]
    by_cases he : tail size % 4 = 0 <;> simp [he] <;> rfl
  obtain ⟨w, a2, r2, c2, e2⟩ := step (boundary := boundary)
    (jcc_rel8_effect_step 0x10146a 4 0x38)
    r1 c1 (MemoryRoutines.Machine.program_text_slice c1 0x146a 2 (by decide +kernel))
    ⟨i1, fun _ ↦ by decide⟩
    (by rw [hj]; exact ne_boundary hb (by split <;> decide) (by split <;> decide))
    (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _)
  have g2 := e2.agrees
  simp only [jccEffect, branchEffect_components] at g2
  have G := g1.trans g2
  have hx : w.external = t.external := G.external (by simp [Component.Covers])
  have hreg (r : BitVec 5) : (Operand.reg r : Operand 64).read w = (Operand.reg r : Operand 64).read t :=
    G.read (by simp)
  have hip2 := e2.rip.trans hj
  by_cases he : tail size % 4 = 0
  · simp only [he, ↓reduceIte] at hip2 ⊢
    refine ⟨_, w, a1.trans a2, r2, c2, G.mono (by simp [changes]), ?_⟩
    have hq : base size + quad size = size := by unfold quad; omega
    exact
      { rip := hip2
        space := hsp.transfer G (by simp)
        state := (hreg 9).trans h.state
        tail := (hreg 14).trans h.tail
        wrote := fun i h1 h2 ↦ by rw [hx]; exact h.wrote i h1 (by omega) }
  · simp only [he, ↓reduceIte] at hip2 ⊢
    refine Reach.trans (P := Rem sp st input output size msg x)
      ⟨_, w, a1.trans a2, r2, c2, G.mono (by simp [changes]), ?_⟩
      fun u ru cu hu ↦ rem_setup boundary hb ru cu hu
    exact
      { rip := hip2
        space := hsp.transfer G (by simp)
        block := fun i ↦ by rw [hx]; exact h.block i
        nonzero := he
        state := (hreg 9).trans h.state
        index := (hreg 6).trans h.index
        head := (hreg 8).trans h.head
        offset := (hreg 15).trans h.offset
        inPtr := (hreg 11).trans h.inPtr
        outPtr := (hreg 3).trans h.outPtr
        rem := (hreg 0).trans h.rem
        tail := (hreg 14).trans h.tail
        rest := fun i h1 h2 ↦ by rw [hx]; exact h.rest i h1 h2
        wrote := fun i h1 h2 ↦ by rw [hx]; exact h.wrote i h1 h2 }

theorem quad_step {j : Nat} (h : Quad sp st input output size msg x j t) :
    Reach boundary sp st output size t fun u ↦
      if j + 4 < quad size then Quad sp st input output size msg x (j + 4) u
      else if tail size % 4 = 0 then Done sp st input output size msg x u
      else Single sp st input output size msg x (j + 4) u := by
  have hlt := h.lt
  refine (quad_body boundary hb hr hc h).trans fun u ru cu hu ↦ ?_
  by_cases hj : j + 4 < quad size
  · simp only [hj, ↓reduceIte]
    refine reach_refl ru cu
      { rip := by rw [hu.rip]; simp [hj]
        space := hu.space, block := hu.block, aligned := hu.aligned, lt := hj, state := hu.state
        index := hu.index, src := hu.src, dst := hu.dst, bound := hu.bound, rem := hu.rem
        tail := hu.tail, head := hu.head, offset := hu.offset, inPtr := hu.inPtr
        outPtr := hu.outPtr, rest := hu.rest, wrote := hu.wrote }
  · simp only [hj, ↓reduceIte]
    have hq : j + 4 = quad size := by have := hu.le; omega
    rw [hq] at hu ⊢
    exact quad_exit boundary hb ru cu hu (by rw [hu.rip]; simp)

theorem single_step {j : Nat} (h : Single sp st input output size msg x j t) :
    Reach boundary sp st output size t fun u ↦
      if j + 1 < tail size then Single sp st input output size msg x (j + 1) u
      else Done sp st input output size msg x u := by
  have hsp := h.space
  have hT : tail size < 64 := Nat.mod_lt _ (by decide)
  have hjT := h.lt
  have hqj := h.ge
  have hbT := base_le size
  have hstl := hsp.state.low
  have houl := hsp.outLow
  have hinl := hsp.inLow
  have hA1 : AddrMode.addr (.sib 1 (some 2) 0 .none) t (0x101490 + BitVec.ofNat 64 (3 + 1)) =
      st + BitVec.ofNat 64 (0x40 + j) := by
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((1 : BitVec 4).setWidth 5) = 1 from rfl, show ((2 : BitVec 4).setWidth 5) = 2 from rfl,
      show (Operand.reg 1 : Operand 64).read t = _ from h.src,
      show (Operand.reg 2 : Operand 64).read t = _ from h.index]
    rw [show BitVec.toNat (0 : BitVec 2) = 0 from rfl, BitVec.shiftLeft_zero]
    bv_omega
  have hks : t.external[st + BitVec.ofNat 64 (0x40 + j)]? = some (stream x)[j] := by
    have := h.block ⟨j, by omega⟩
    have he : st + 0x40 + BitVec.ofNat 64 j = st + BitVec.ofNat 64 (0x40 + j) := by bv_omega
    rwa [he] at this
  have hlen1 : (AddrMode.sib 1 (some 2) 0 .none).tail.length = 1 := rfl
  obtain ⟨u1, a1, r1, c1, e1⟩ := step (boundary := boundary)
    (movzx_r32_m8_effect_step 0x101490 6 (.sib 1 (some 2) 0 .none) (by decide) (by decide)
      (by decide))
    hr hc (MemoryRoutines.Machine.program_text_slice hc 0x1490 4 (by decide +kernel))
    ⟨h.rip, by
      rw [hlen1, hA1]
      exact readable_of_get hks (by unfold stateBytes at hstl; rw [toNat_add_ofNat (by omega)]; omega)⟩
    (by
      intro he
      apply ne_boundary hb (p := 0x101494) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  rw [hlen1, show gprNumber 0 0 6 = 6 from rfl] at e1
  have g1 := e1.agrees
  simp only [movzxR32M8Effect_components] at g1
  have v1 : (Operand.reg 6 : Operand 64).read u1 = ((stream x)[j]).toBitVec.setWidth 64 := by
    have hw := e1.writes
    simp only [movzxR32M8Effect, Write.AllHold] at hw
    rw [hw, hA1]
    change (memLoad t.external _ 8).setWidth 64 = _
    rw [load8_of_get hks]
  have hrin := h.rest (base size + j) (by omega) (by omega)
  have hlen2 : (AddrMode.sib 11 (some 2) 0 .none).tail.length = 1 := rfl
  have hA2 : AddrMode.addr (.sib 11 (some 2) 0 .none) u1 (0x101494 + BitVec.ofNat 64 (3 + 1)) =
      input + BitVec.ofNat 64 (base size + j) := by
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((11 : BitVec 4).setWidth 5) = 11 from rfl,
      show ((2 : BitVec 4).setWidth 5) = 2 from rfl, g1.read (by simp), g1.read (by simp),
      show (Operand.reg 11 : Operand 64).read t = _ from h.inPtr,
      show (Operand.reg 2 : Operand 64).read t = _ from h.index,
      show BitVec.toNat (0 : BitVec 2) = 0 from rfl, BitVec.shiftLeft_zero]
    unfold inTail
    bv_omega
  have hx1 : u1.external = t.external := g1.external (by simp [Component.Covers])
  have hrin1 : u1.external[input + BitVec.ofNat 64 (base size + j)]? = some (msg (base size + j)) := by
    rw [hx1]; exact hrin
  obtain ⟨u2, a2, r2, c2, e2⟩ := step (boundary := boundary)
    (xor_r8_m8_rex_effect_step 0x101494 0x41 (by unfold RexPrefix; decide) 6
      (.sib 11 (some 2) 0 .none) (by decide) (by decide) (by decide))
    r1 c1 (MemoryRoutines.Machine.program_text_slice c1 0x1494 4 (by decide +kernel))
    ⟨e1.rip.trans rfl, by
      rw [hlen2, hA2]
      exact readable_of_get hrin1 (by rw [toNat_add_ofNat (by omega)]; omega)⟩
    (by
      intro he
      apply ne_boundary hb (p := 0x101498) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  rw [hlen2, show gprNumber 0 (rexR (UInt8.toBitVec 0x41)) 6 = 6 from rfl] at e2
  have g2 := e2.agrees
  simp only [xorR8M8Effect_components] at g2
  have hbyte : (stream x)[j] ^^^ msg (base size + j) = msg (base size + j) ^^^ (stream x)[j] :=
    UInt8.xor_comm _ _
  have v2 : (Operand.reg 6 : Operand 8).read u2 =
      (msg (base size + j) ^^^ (stream x)[j]).toBitVec := by
    have hw := e2.writes
    simp only [xorR8M8Effect, Write.AllHold] at hw
    rw [reg8_eq, hw, mergeGPR8_low, hA2, reg8_eq, v1]
    change _ ^^^ memLoad u1.external _ 8 = _
    rw [load8_of_get hrin1, ← hbyte]
    simp [BitVec.setWidth_setWidth_of_le]
  have g12 := g1.trans g2
  have hlen3 : (AddrMode.sib 3 (some 2) 0 .none).tail.length = 1 := rfl
  have hA3 : AddrMode.addr (.sib 3 (some 2) 0 .none) u2 (0x101498 + BitVec.ofNat 64 (3 + 1)) =
      output + BitVec.ofNat 64 (base size + j) := by
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((3 : BitVec 4).setWidth 5) = 3 from rfl,
      show ((2 : BitVec 4).setWidth 5) = 2 from rfl, g12.read (by simp), g12.read (by simp),
      show (Operand.reg 3 : Operand 64).read t = _ from h.outPtr,
      show (Operand.reg 2 : Operand 64).read t = _ from h.index,
      show BitVec.toNat (0 : BitVec 2) = 0 from rfl, BitVec.shiftLeft_zero]
    unfold outTail
    bv_omega
  have hoa : output + BitVec.ofNat 64 (base size + j) = outTail output size + BitVec.ofNat 64 j := by
    rw [out_addr output (size := size) (i := base size + j) (by omega), Nat.add_sub_cancel_left]
  have hnc3 : NotCode (output + BitVec.ofNat 64 (base size + j)) 1 := by
    rw [hoa]; exact hsp.outCode.slice j 1 (by omega)
  obtain ⟨u3, a3, r3, c3, e3⟩ := step (boundary := boundary)
    (mov_m8_r8_rex_effect_step 0x101498 0x40 (by unfold RexPrefix; decide) 6
      (.sib 3 (some 2) 0 .none) (by decide) (by decide) (by decide))
    r2 c2 (MemoryRoutines.Machine.program_text_slice c2 0x1498 4 (by decide +kernel))
    ⟨e2.rip.trans rfl, by
      rw [hlen3, hA3, hoa]
      exact writable_slice (writable_grow (hsp.out (by omega)) g12) j 1 (by omega), by
      rw [hlen3, hA3]
      exact hnc3.apart (text_in_program 0x1498 4 (by decide +kernel))⟩
    (by
      intro he
      apply ne_boundary hb (p := 0x10149c) (by decide) (by decide)
      rw [← he]; rfl)
    (store_avoids (a := output + BitVec.ofNat 64 (base size + j)) (n := 1)
      (by simp only [movM8R8Effect, storeEffect_components, hlen3, hA3]) hnc3)
  have hc3 : (movM8R8Effect 0x101498 (3 + (AddrMode.sib 3 (some 2) 0 .none).tail.length)
      (gprNumber 0 (rexR (UInt8.toBitVec 0x40)) 6) (.sib 3 (some 2) 0 .none) u2).components =
      [.mem (output + BitVec.ofNat 64 (base size + j)) 1, .rip] := by
    simp only [movM8R8Effect, storeEffect_components, hlen3, hA3]
  have g3 := e3.agrees
  rw [hc3] at g3
  have v3 : u3.external[output + BitVec.ofNat 64 (base size + j)]? =
      some (msg (base size + j) ^^^ (stream x)[j]) := by
    have hw := e3.writes
    simp only [movM8R8Effect, storeEffect, Write.AllHold, hlen3, hA3] at hw
    rw [show gprNumber 0 (rexR (UInt8.toBitVec 0x40)) 6 = 6 from rfl, v2] at hw
    have hs := (writable_slice (writable_grow (hsp.out (by omega)) (g12.trans g3)) j 1 (by omega)).mem 0
      (by decide)
    rw [BitVec.add_zero, ← hoa] at hs
    rw [get_of_load8 hs hw]
  obtain ⟨u4, a4, r4, c4, e4⟩ := step (boundary := boundary)
    (inc_r64_effect_step 0x10149c 0x48 0xc2 (by unfold RexWPrefix; decide) (by decide) (by decide))
    r3 c3 (MemoryRoutines.Machine.program_text_slice c3 0x149c 3 (by decide +kernel))
    (e3.rip.trans rfl)
    (by
      intro he
      apply ne_boundary hb (p := 0x10149f) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x48)) (modrmRm 0xc2) = 2 by decide] at e4
  have g4 := e4.agrees
  simp only [incR64Effect_components] at g4
  have g123 := g12.trans g3
  have v4 : (Operand.reg 2 : Operand 64).read u4 = BitVec.ofNat 64 (j + 1 - quad size) := by
    have hw := e4.writes
    simp only [incR64Effect, Write.AllHold] at hw
    rw [hw, g123.read (by simp), show (Operand.reg 2 : Operand 64).read t = _ from h.index]
    bv_omega
  obtain ⟨u5, a5, r5, c5, e5⟩ := step (boundary := boundary)
    (cmp_r64_r64_effect_step 0x10149f 0x48 0xd0 (by unfold RexWPrefix; decide) (by decide))
    r4 c4 (MemoryRoutines.Machine.program_text_slice c4 0x149f 3 (by decide +kernel))
    (e4.rip.trans rfl)
    (by
      intro he
      apply ne_boundary hb (p := 0x1014a2) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  rw [show gprNumber 0 (rexB (UInt8.toBitVec 0x48)) (modrmRm 0xd0) = 0 by decide,
    show gprNumber 0 (rexR (UInt8.toBitVec 0x48)) (modrmReg 0xd0) = 2 by decide] at e5
  have g5 := e5.agrees
  simp only [cmpR64R64Effect_components] at g5
  have hZF : (StatusFlags.ofRFLAGS u5.RFLAGS).ZF = decide (j + 1 = tail size) := by
    obtain ⟨-, -, -, hZ, -⟩ := e5.flags
    change _ = (cmpSpec _ _).ZF at hZ
    rw [hZ, cmpSpec_ZF, v4, (g123.trans g4).read (by simp),
      show (Operand.reg 0 : Operand 64).read t = _ from h.rem]
    have hq : quad size = tail size - tail size % 4 := rfl
    by_cases he : j + 1 = tail size
    · simp only [he, decide_true]
      rw [show tail size - quad size = tail size % 4 by omega]
      simp
    · simp only [he, decide_false]
      rw [beq_eq_false_iff_ne]
      intro hv
      have := congrArg BitVec.toNat hv
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at this
      omega
  obtain ⟨w, a6, r6, c6, e6⟩ := step (boundary := boundary)
    (jcc_rel8_effect_step 0x1014a2 5 0xec)
    r5 c5 (MemoryRoutines.Machine.program_text_slice c5 0x14a2 2 (by decide +kernel))
    ⟨e5.rip.trans rfl, fun _ ↦ by decide⟩
    (by
      intro he
      apply ne_boundary hb (p := if j + 1 = tail size then 0x1014a4 else 0x101490)
        (by split <;> decide) (by split <;> decide)
      rw [← he]
      simp only [jccEffect, branchEffect, condHolds_5, hZF]
      split <;> simp_all <;> rfl)
    (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _)
  have g6 := e6.agrees
  simp only [jccEffect, branchEffect_components] at g6
  have hrip : w.RIP = if j + 1 = tail size then 0x1014a4 else 0x101490 := by
    rw [e6.rip]
    simp only [jccEffect, branchEffect, condHolds_5, hZF]
    split <;> simp_all <;> rfl
  have G := ((g123.trans g4).trans g5).trans g6
  have g456 := (g4.trans g5).trans g6
  have hx46 : w.external = u3.external := g456.external (by simp [Component.Covers])
  have hL : ∀ c ∈ [Component.reg 6, Component.rip] ++ [Component.reg 6, Component.flags, Component.rip] ++
        [Component.mem (output + BitVec.ofNat 64 (base size + j)) 1, Component.rip] ++
        [Component.reg 2, Component.flags, Component.rip] ++ [Component.flags, Component.rip] ++
        [Component.rip], c = .mem (output + BitVec.ofNat 64 (base size + j)) 1 ∨ c.isMem = false := by
    simp [Component.isMem]
  have hcov (y : BitVec 64) (hy : y ≠ output + BitVec.ofNat 64 (base size + j)) :=
    not_covers_of hL (y := y) fun k hk ↦ by rw [show k = 0 by omega, BitVec.add_zero]; exact hy
  have hsp' : Space sp st input output size w := hsp.transfer G (by simp)
  have hblock : BytesAt (st + 0x40) (stream x) w := h.block.transfer G fun i hi ↦ hcov _ (by
    rw [hoa]
    intro he
    have he' : st + 0x40 + BitVec.ofNat 64 i = st + BitVec.ofNat 64 (0x40 + i) := by bv_omega
    rw [he'] at he
    exact hsp.outState j (by omega) (0x40 + i) (by unfold stateBytes; omega) he.symm)
  have hrest : Rest input size msg (base size + (j + 1)) w := by
    intro i hi1 hi2
    rw [G.byte (hcov _ ?_)]
    · exact h.rest i (by omega) hi2
    · rcases hsp.alias with he | hap
      · subst he
        exact add_ofNat_ne (by omega) (by omega) (by omega)
      · rw [in_addr input (size := size) (i := i) (by omega), hoa]
        exact hap (i - base size) (by omega) j (by omega)
  have hwrote : Wrote output size msg (stream x) (base size + (j + 1)) w := by
    intro i hi1 hi2
    by_cases hij : i = base size + j
    · subst hij
      rw [hx46, v3, Nat.add_sub_cancel_left, getElem!_pos (stream x) j (by omega)]
    · rw [G.byte (hcov _ (add_ofNat_ne (by omega) (by omega) hij))]
      exact h.wrote i hi1 (by omega)
  refine ⟨6, w, ((((a1.trans a2).trans a3).trans a4).trans a5).trans a6, r6, c6, ?_, ?_⟩
  · refine G.widen (by simp [changes, Component.isMem]) (covered_of hL fun k hk ↦ ?_)
    refine ⟨.mem (outTail output size) (tail size), by simp [changes], j, by omega, ?_⟩
    rw [show k = 0 by omega, BitVec.add_zero, hoa]
  · have r9 : reg64 w 9 = st := (G.read (by simp)).trans h.state
    have r14 : reg64 w 14 = _ := (G.read (by simp)).trans h.tail
    split
    · rename_i hlt
      exact
        { rip := by rw [hrip]; simp [show j + 1 ≠ tail size by omega]
          space := hsp'
          block := hblock
          ge := by omega
          lt := hlt
          state := r9
          index := by
            rw [show reg64 w 2 = _ from (g5.trans g6).read (by simp), v4]
          src := (G.read (by simp)).trans h.src
          inPtr := (G.read (by simp)).trans h.inPtr
          outPtr := (G.read (by simp)).trans h.outPtr
          rem := (G.read (by simp)).trans h.rem
          tail := r14
          rest := by simpa [Nat.add_assoc] using hrest
          wrote := by simpa [Nat.add_assoc] using hwrote }
    · rename_i hge
      exact
        { rip := by rw [hrip]; simp [show j + 1 = tail size by omega]
          space := hsp'
          state := r9
          tail := r14
          wrote := by
            have : base size + (j + 1) = size := by omega
            rw [this] at hwrote; exact hwrote }

theorem finish (h : Done sp st input output size msg x t) :
    Reach boundary sp st output size t (Final output size msg x) := by
  have hsp := h.space
  have haddr : AddrMode.addr (.base 9 (.d8 0x40)) t (0x1014a4 + BitVec.ofNat 64 (3 + 1)) =
      st + BitVec.ofNat 64 0x40 := by
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((9 : BitVec 4).setWidth 5) = 9 from rfl]
    rw [show (Operand.reg 9 : Operand 64).read t = st from h.state]
    rfl
  have hlen : (AddrMode.base 9 (Disp.d8 64)).tail.length = 1 := rfl
  have hw : MemWritable t (st + BitVec.ofNat 64 0x40) 1 :=
    writable_slice hsp.state 0x40 1 (by decide)
  have hnc : NotCode (st + BitVec.ofNat 64 0x40) 1 := hsp.stateCode.slice 0x40 1 (by decide)
  obtain ⟨u, a1, r1, c1, e1⟩ := step (boundary := boundary)
    (mov_m8_r8_rex_effect_step 0x1014a4 0x45 (by unfold RexPrefix; decide) 6
      (.base 9 (.d8 0x40)) (by decide) (by decide) (by decide))
    hr hc (MemoryRoutines.Machine.program_text_slice hc 0x14a4 4 (by decide +kernel))
    ⟨h.rip, by rw [hlen, haddr]; exact hw, by
      rw [hlen, haddr]
      exact hnc.apart (text_in_program 0x14a4 4 (by decide +kernel))⟩
    (by
      intro he
      apply ne_boundary hb (p := 0x1014a8) (by decide) (by decide)
      rw [← he]; rfl)
    (store_avoids (a := st + BitVec.ofNat 64 0x40) (n := 1)
      (by simp only [movM8R8Effect, storeEffect_components, hlen, haddr]) hnc)
  have hc1 : (movM8R8Effect 0x1014a4 (3 + (AddrMode.base 9 (Disp.d8 64)).tail.length)
      (gprNumber 0 (rexR (UInt8.toBitVec 0x45)) 6) (.base 9 (.d8 0x40)) t).components =
      [.mem (st + BitVec.ofNat 64 0x40) 1, .rip] := by
    simp only [movM8R8Effect, storeEffect_components, hlen, haddr]
  obtain ⟨v, a2, r2, c2, e2⟩ := step (boundary := boundary)
    (xor_r32_r32_effect_step 0x1014a8 0xc0 (by decide))
    r1 c1 (MemoryRoutines.Machine.program_text_slice c1 0x14a8 2 (by decide +kernel))
    (e1.rip.trans rfl)
    (by
      intro he
      apply ne_boundary hb (p := 0x1014aa) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  have hg0 : gprNumber 0 0 (modrmRm 192) = 0 := by decide
  have hg0' : gprNumber 0 0 (modrmReg 192) = 0 := by decide
  rw [hg0, hg0'] at e2
  have g1 := e1.agrees
  rw [hc1] at g1
  have g2 := e2.agrees
  simp only [xorR32R32Effect_components] at g2
  refine ⟨1 + 1, v, a1.trans a2, r2, c2, ?_, ⟨e2.rip, ?_, ?_⟩⟩
  · refine (g1.trans g2).widen (fun c hc hm ↦ ?_) (fun y c hc hcov ↦ ?_)
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl) | (rfl | rfl | rfl) <;> simp_all [changes, Component.isMem]
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl) | (rfl | rfl | rfl) <;> simp only [Component.Covers] at hcov
      obtain ⟨k, hk, rfl⟩ := hcov
      exact ⟨.mem (st + 0x40) 0x40, by simp [changes], k, by omega, rfl⟩
  · have hw := e2.writes
    simp only [xorR32R32Effect, Write.AllHold] at hw
    rw [show rax = (Operand.reg 0 : Operand 64) from rfl, hw]
    simp
  · intro i hi1 hi2
    have hx := h.wrote i hi1 hi2
    have hmem2 : v.external = u.external :=
      g2.external (by intro c hc y; simp at hc; rcases hc with rfl | rfl | rfl <;> simp [Component.Covers])
    rw [hmem2, g1.byte, hx]
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨k, hk, he⟩ := hcov
      rw [out_addr output hi1, show k = 0 by omega, BitVec.add_zero] at he
      have := base_le size
      exact hsp.outState (i - base size) (by omega) 0x40 (by unfold stateBytes; omega) he
    · exact hcov

end Stubs

section Composition

variable [Bindings] (boundary : ReturnBoundary)
  (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat)
  {sp st input output : BitVec 64} {size : Nat} {msg : Nat → UInt8} {x : Vector UInt32 16}

include hb

theorem rounds_from (n : Nat) {t : RamState} (hn : n ≤ 10) (hr : ReadyToStep t)
    (hc : CodeIn Extracted.programImage t)
    (h : Rounds sp st input output size msg x (10 - n) t) :
    Reach boundary sp st output size t (Rounds sp st input output size msg x 10) := by
  induction n generalizing t with
  | zero => exact reach_refl hr hc h
  | succ n ih =>
    refine (round_step boundary hb hr hc h (by omega)).trans fun u hr' hc' hu ↦ ?_
    have he : 10 - (n + 1) + 1 = 10 - n := by omega
    rw [he] at hu
    exact ih (by omega) hr' hc' hu

theorem single_from (n : Nat) {j : Nat} {t : RamState} (hn : j + n = tail size)
    (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (h : Single sp st input output size msg x j t) :
    Reach boundary sp st output size t (Done sp st input output size msg x) := by
  induction n generalizing t j with
  | zero => exact absurd h.lt (by omega)
  | succ n ih =>
    refine (single_step boundary hb hr hc h).trans fun u hr' hc' hu ↦ ?_
    split at hu
    · exact ih (j := j + 1) (by omega) hr' hc' hu
    · exact reach_refl hr' hc' hu

theorem quad_from (n : Nat) {j : Nat} {t : RamState} (hn : j + 4 * n = quad size)
    (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (h : Quad sp st input output size msg x j t) :
    Reach boundary sp st output size t (Done sp st input output size msg x) := by
  induction n generalizing t j with
  | zero => exact absurd h.lt (by omega)
  | succ n ih =>
    refine (quad_step boundary hb hr hc h).trans fun u hr' hc' hu ↦ ?_
    split at hu
    · exact ih (j := j + 4) (by omega) hr' hc' hu
    · split at hu
      · exact reach_refl hr' hc' hu
      · exact single_from boundary hb (tail size - (j + 4)) (by have := hu.lt; omega) hr' hc' hu

theorem keyed_run {t : RamState} (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (h : Keyed sp st input output size msg x t) :
    Reach boundary sp st output size t (Done sp st input output size msg x) := by
  have hq4 : quad size % 4 = 0 := by unfold quad; omega
  by_cases hq : 4 ≤ tail size
  · refine (keyed_quad boundary hb hr hc h hq).trans fun u hr' hc' hu ↦ ?_
    exact quad_from boundary hb (quad size / 4) (j := 0) (by unfold quad at *; omega) hr' hc' hu
  · refine (keyed_short boundary hb hr hc h (by omega)).trans fun u hr' hc' hu ↦ ?_
    exact single_from boundary hb (tail size) (j := 0) (by omega) hr' hc' hu

theorem tail_run {t : RamState} (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (h : TailCut sp st input output size msg x t) :
    Reach boundary sp st output size t (Final output size msg x) := by
  by_cases hz : tail size = 0
  · exact tail_empty boundary hb hr hc h hz
  · refine (tail_setup boundary hb hr hc h hz).trans fun u₁ r₁ c₁ h₁ ↦ ?_
    refine (rounds_from boundary hb 10 (by decide) r₁ c₁ h₁).trans fun u₂ r₂ c₂ h₂ ↦ ?_
    refine (tail_feed boundary hb r₂ c₂ h₂).trans fun u₃ r₃ c₃ h₃ ↦ ?_
    refine (keyed_run boundary hb r₃ c₃ h₃).trans fun u₄ r₄ c₄ h₄ ↦ ?_
    exact finish boundary hb r₄ c₄ h₄

end Composition

end ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Tail

