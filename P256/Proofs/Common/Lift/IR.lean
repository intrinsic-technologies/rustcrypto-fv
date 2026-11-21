import P256.Proofs.Common.Lift.Reg
import P256.Proofs.Common.CFG.Machine

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG

def CodeAt (code : CodeMap) (a : BitVec 64) : Prop := ∃ b, (a, b) ∈ code

def entriesOf (rs : List Reg) (s : RamState) : List (Reg × Value) := rs.map fun r => (r, r.read s)

def ReadsOnly (p : BitVec 64) (e : RamState → Effect) (R : List Reg) : Prop :=
  ∀ s, e s = e (stateOf p (entriesOf R s) s.external)

def FlagsAgree (F : List StatusFlag) (t t' : RamState) : Prop :=
  ∀ f ∈ F, (StatusFlags.ofRFLAGS t.RFLAGS).get f = (StatusFlags.ofRFLAGS t'.RFLAGS).get f

structure LocalWith (F : List StatusFlag) (e : RamState → Effect) : Prop where
  rip : ∀ t t', Obs t t' → FlagsAgree F t t' → (e t).rip = (e t').rip
  writes : ∀ t t', Obs t t' → FlagsAgree F t t' → (e t).writes = (e t').writes
  flagsSome : ∀ t t', Obs t t' → FlagsAgree F t t' → (e t).flags.isSome = (e t').flags.isSome
  flag : ∀ t t', Obs t t' → FlagsAgree F t t' → ∀ i,
    (StatusFlags.ofRFLAGS t.RFLAGS).get i = (StatusFlags.ofRFLAGS t'.RFLAGS).get i →
      (e t).flag t i = (e t').flag t' i
  full : ∀ t, ∀ w ∈ (e t).writes, w.Full

def atFlags {α : Type} (f : StatusFlags → α) (e : α → RamState → Effect) (s : RamState) : Effect :=
  e (f (StatusFlags.ofRFLAGS s.RFLAGS)) s

def FlagFresh (F : List StatusFlag) (e : RamState → Effect) (f : StatusFlag) : Prop :=
  ∀ t t', Obs t t' → FlagsAgree F t t' → (e t).flag t f = (e t').flag t' f

def WritesPresent (e : Effect) (mem : Ram) : Prop :=
  ∀ c ∈ e.components, ∀ x, c.Covers x → (mem[x]?).isSome

inductive Op : Nat → Type where

  | const (v : Value) : Op 0

  | pure {n : Nat} (f : Vector Value n → Value) : Op n

  | out (p : BitVec 64) (e : RamState → Effect) (reads : List Reg) (o : EffectPart) :
      Op reads.length

  | exec (p : BitVec 64) (pre : RamState → Prop) (e : RamState → Effect) (reads : List Reg) :
      Op reads.length

  | expect (v : Value) : Op 1

  | cut (p : BitVec 64) : Op 0

def Op.state (p : BitVec 64) (reads : List Reg) {n : Nat} (args : Values Value n) (mem : Ram) :
    RamState :=
  stateOf p (reads.zip args.toList) mem

def Guard (code : CodeMap) (pre : RamState → Prop) (e : RamState → Effect) (t : RamState)
    (mem : Ram) : Prop :=
  pre t ∧ (e t).Avoids code ∧ WritesPresent (e t) mem

structure LoadOk (mem : Ram) (a : BitVec 64) (len : Nat) : Prop where
  low : a.toNat + len ≤ 2^32
  present : ∀ i < len, (mem[a + BitVec.ofNat 64 i]?).isSome

structure StoreOk (code : CodeMap) (mem : Ram) (a : BitVec 64) (len : Nat) (p : BitVec 64)
    (codeLen : Nat) : Prop where
  low : a.toNat + len ≤ 2^32
  present : ∀ i < len, (mem[a + BitVec.ofNat 64 i]?).isSome
  tables : PageTableEntriesApart a.toNat len
  apart : RangeApart a len p codeLen
  notCode : ∀ x ∈ code, ∀ i < len, x.1 ≠ a + BitVec.ofNat 64 i

structure RepMovsOk (code : CodeMap) (mem : Ram) (df : BitVec 1) (src dst count : BitVec 64)
    (size : Nat) (p : BitVec 64) (codeLen : Nat) : Prop where
  df : df = 0
  srcLow : src.toNat + size * count.toNat ≤ 2^32
  dstLow : dst.toNat + size * count.toNat ≤ 2^32
  srcMem : ∀ i < size * count.toNat, (mem[src + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < size * count.toNat, (mem[dst + BitVec.ofNat 64 i]?).isSome
  disjoint : src.toNat + size * count.toNat ≤ dst.toNat ∨ dst.toNat + size * count.toNat ≤ src.toNat
  dstTables : PageTableEntriesApart dst.toNat (size * count.toNat)
  dstCode : RangeApart dst (size * count.toNat) p codeLen
  notCode : ∀ x ∈ code, ∀ i < size * count.toNat, x.1 ≠ dst + BitVec.ofNat 64 i

structure RepStosOk (code : CodeMap) (mem : Ram) (df : BitVec 1) (dst count : BitVec 64)
    (size : Nat) (p : BitVec 64) (codeLen : Nat) : Prop where
  df : df = 0
  dstLow : dst.toNat + size * count.toNat ≤ 2^32
  dstMem : ∀ i < size * count.toNat, (mem[dst + BitVec.ofNat 64 i]?).isSome
  dstTables : PageTableEntriesApart dst.toNat (size * count.toNat)
  dstCode : RangeApart dst (size * count.toNat) p codeLen
  notCode : ∀ x ∈ code, ∀ i < size * count.toNat, x.1 ≠ dst + BitVec.ofNat 64 i

instance (code : CodeMap) (mem : Ram) (df : BitVec 1) (src dst count : BitVec 64) (size : Nat)
    (p : BitVec 64) (codeLen : Nat) :
    Decidable (RepMovsOk code mem df src dst count size p codeLen) :=
  let n := size * count.toNat
  decidable_of_iff (df = 0 ∧ src.toNat + n ≤ 2^32 ∧ dst.toNat + n ≤ 2^32 ∧
      (∀ i < n, (mem[src + BitVec.ofNat 64 i]?).isSome) ∧
      (∀ i < n, (mem[dst + BitVec.ofNat 64 i]?).isSome) ∧
      (src.toNat + n ≤ dst.toNat ∨ dst.toNat + n ≤ src.toNat) ∧
      PageTableEntriesApart dst.toNat n ∧
      (∀ i < n, ∀ j < codeLen, dst + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j) ∧
      ∀ x ∈ code, ∀ i < n, x.1 ≠ dst + BitVec.ofNat 64 i)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩,
      fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩⟩

instance (code : CodeMap) (mem : Ram) (df : BitVec 1) (dst count : BitVec 64) (size : Nat)
    (p : BitVec 64) (codeLen : Nat) : Decidable (RepStosOk code mem df dst count size p codeLen) :=
  let n := size * count.toNat
  decidable_of_iff (df = 0 ∧ dst.toNat + n ≤ 2^32 ∧
      (∀ i < n, (mem[dst + BitVec.ofNat 64 i]?).isSome) ∧
      PageTableEntriesApart dst.toNat n ∧
      (∀ i < n, ∀ j < codeLen, dst + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j) ∧
      ∀ x ∈ code, ∀ i < n, x.1 ≠ dst + BitVec.ofNat 64 i)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
      fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩⟩

instance (mem : Ram) (a : BitVec 64) (len : Nat) : Decidable (LoadOk mem a len) :=
  decidable_of_iff (a.toNat + len ≤ 2^32 ∧ ∀ i < len, (mem[a + BitVec.ofNat 64 i]?).isSome)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

instance (code : CodeMap) (mem : Ram) (a : BitVec 64) (len : Nat) (p : BitVec 64) (codeLen : Nat) :
    Decidable (StoreOk code mem a len p codeLen) :=
  decidable_of_iff (a.toNat + len ≤ 2^32 ∧
      (∀ i < len, (mem[a + BitVec.ofNat 64 i]?).isSome) ∧
      PageTableEntriesApart a.toNat len ∧
      (∀ i < len, ∀ j < codeLen, a + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j) ∧
      ∀ x ∈ code, ∀ i < len, x.1 ≠ a + BitVec.ofNat 64 i)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
      fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩⟩

open Classical in

noncomputable def Op.eval (code : CodeMap) : {n : Nat} → Op n → Values Value n → Ram →
    Option (Value × Ram)
  | _, .const v, _, mem => some (v, mem)
  | _, .pure f, args, mem => some (f args, mem)
  | _, .out p e reads o, args, mem =>
      let t := Op.state p reads args mem
      some (o.value (e t) t, mem)
  | _, .exec p pre e reads, args, mem =>
      let t := Op.state p reads args mem
      if Guard code pre e t mem then some (⟨1, 0⟩, (applyWrites t (e t).writes).external) else none
  | _, .expect v, args, mem => if args[0] = v then some (⟨1, 0⟩, mem) else none
  | _, .cut _, _, _ => none

noncomputable def dialect (code : CodeMap) : Dialect Op Value Ram where
  eval op args mem := op.eval code args mem
  truth := Value.truth
  accepts guard tag := decide (guard = tag)

abbrev signature {Label : Type} : Label → Nat := fun _ => Reg.count

def cutBlock {Label : Type} {n : Nat} (p : BitVec 64) : Block Op Label signature Reg.count n :=
  .letOp (.cut p) #v[] (.terminate (.ret (Vector.replicate Reg.count (Fin.last n))))

structure Lifted where
  Label : Type
  address : Label → BitVec 64
  live : Label → Nat
  retLive : Nat
  program : Program Op Label signature Reg.count

namespace Lifted

variable (P : Lifted)

abbrev Location := CFG.Location Value Ram P.Label signature

abbrev State := CFG.State Value Ram P.Label signature Reg.count

abbrev StackFrame := CFG.StackFrame Value P.Label signature Reg.count

def FrameOk (fr : P.StackFrame) : Prop :=
  fr.size = 0 ∧ fr.guard = some ⟨64, P.address fr.target⟩ ∧
    ∀ i < Reg.count, (P.live fr.target).testBit i = true → P.retLive.testBit i = true

end Lifted

abbrev Live (m i : Nat) : Prop := m.testBit i = true

structure Rel [Bindings] (code : CodeMap) (P : Lifted) (st : P.State) (s : RamState) : Prop where
  rip : s.RIP = P.address st.location.label
  regs : ∀ i (h : i < Reg.count), Live (P.live st.location.label) i →
    st.location.arguments[i] = (Reg.ofIndex i).read s
  store : st.location.store = s.external
  frames : ∀ fr ∈ st.stack, P.FrameOk fr
  ready : ReadyToStep s
  sse : Prelude.SupportedSSE Bindings.processor s
  code : CodeIn code s

structure RetRel [Bindings] (code : CodeMap) (P : Lifted) (o : Output Value Ram Reg.count)
    (t : RamState) : Prop where
  rip : o.tag = some ⟨64, t.RIP⟩
  regs : ∀ i (h : i < Reg.count), Live P.retLive i → o.values[i] = (Reg.ofIndex i).read t
  store : o.store = t.external
  ready : ReadyToStep t
  sse : Prelude.SupportedSSE Bindings.processor t
  code : CodeIn code t

end P256.Proofs.Lift
