import AesGcm.Proofs.Machine.CTR.BatchXorEvaluation
import X86Proofs.Program.ReadWrite.Bytes

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem batchXorWords {before after : Ram} {src dst key : BitVec 64}
    (bytes : ∀ j : Fin 64,
      memLoad after (dst + BitVec.ofNat 64 j.val) 8 =
        memLoad before (key + BitVec.ofNat 64 j.val) 8 ^^^
        memLoad before (src + BitVec.ofNat 64 j.val) 8) (i : Fin 8) :
    memLoad after (dst + BitVec.ofNat 64 (8 * i.val)) 64 =
      memLoad before (src + BitVec.ofNat 64 (8 * i.val)) 64 ^^^
      memLoad before (key + BitVec.ofNat 64 (8 * i.val)) 64 := by
  apply memLoad_eq_of_memByte (by decide)
  intro j hj
  have hi := i.isLt
  have h := congrArg UInt8.ofBitVec (bytes ⟨8 * i.val + j, by change j < 8 at hj; omega⟩)
  rw [storedByte_xor, storedByte_memLoad _ _ _ hj, storedByte_memLoad _ _ _ hj]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
  simpa only [memLoad_8, UInt8.ofBitVec_xor, UInt8.ofBitVec_toBitVec, UInt8.xor_comm] using h

private inductive BatchBase where
  | stack | src | dst
  deriving DecidableEq

private def batchStart : BatchBase → Nat
  | .stack => 72
  | _ => 0

private def batchSize : BatchBase → Nat
  | .stack => 264
  | _ => 64

private structure BatchLayout where
  variant : Bool
  base : BatchBase → BitVec 64
  low (b) : (base b + BitVec.ofNat 64 (batchStart b)).toNat + batchSize b ≤ 2 ^ 32
  apart (b c) (hc : b ≠ c) (hs : b = .stack ∨ c = .stack) :
    (base b + BitVec.ofNat 64 (batchStart b)).toNat + batchSize b ≤
      (base c + BitVec.ofNat 64 (batchStart c)).toNat ∨
    (base c + BitVec.ofNat 64 (batchStart c)).toNat + batchSize c ≤
      (base b + BitVec.ofNat 64 (batchStart b)).toNat

private structure BatchAddr where
  bank : BatchBase
  off : BitVec 64
  deriving DecidableEq

private def BatchAddr.addr (a : BatchAddr) (l : BatchLayout) := l.base a.bank + a.off

private def BatchAddr.apart (a b : BatchAddr) (n k : Nat) : Bool :=
  if a.bank = b.bank then decide (n ≤ (b.off - a.off).toNat ∧ k ≤ (a.off - b.off).toNat)
  else decide ((a.bank = .stack ∨ b.bank = .stack) ∧
    (a.off - BitVec.ofNat 64 (batchStart a.bank)).toNat + n ≤ batchSize a.bank ∧
    (b.off - BitVec.ofNat 64 (batchStart b.bank)).toNat + k ≤ batchSize b.bank)

private theorem BatchAddr.apart_sound {a b : BatchAddr} {l : BatchLayout} {n k : Nat}
    (h : a.apart b n k = true) : RangeApart (a.addr l) n (b.addr l) k := by
  rcases a with ⟨ba, ao⟩
  rcases b with ⟨bb, bo⟩
  simp only [apart] at h
  split at h
  · rename_i he
    subst bb
    exact RangeApart.of_offsets rfl rfl (of_decide_eq_true h)
  · have h := of_decide_eq_true h
    exact RangeApart.of_regions rfl rfl rfl rfl (l.low ba) (l.low bb)
      (l.apart ba bb (by assumption) h.1) h.2

private def batchBase (sp src dst : BitVec 64) : BatchBase → BitVec 64
  | .stack => sp
  | .src => src
  | .dst => dst

private def batchLayout (use256 : Bool) {code : CodeMap} {mem : Ram} {sp src dst : BitVec 64}
    (hs : Writable code mem (sp + 72) 264) (hr : Readable mem src 64)
    (hd : Writable code mem dst 64)
    (hdApart : dst.toNat + 64 ≤ (sp + 72).toNat ∨ (sp + 72).toNat + 264 ≤ dst.toNat)
    (hsApart : src.toNat + 64 ≤ (sp + 72).toNat ∨ (sp + 72).toNat + 264 ≤ src.toNat) :
    BatchLayout where
  variant := use256
  base := batchBase sp src dst
  low := by
    intro b
    cases b <;> simp only [batchBase, batchStart, batchSize, BitVec.add_zero]
    all_goals first | exact hs.readable.low | exact hr.low | exact hd.readable.low
  apart := by
    intro b c hn ht
    cases b <;> cases c <;> try exact False.elim (hn rfl)
    all_goals simp [batchBase, batchStart, batchSize] at ht ⊢
    all_goals first | exact hsApart.symm | exact hdApart.symm | exact hsApart | exact hdApart

private def batchScratch (v : Bool) (i : Nat) : Nat :=
  if i < 13 then 119 - i
  else if i = 13 then (if v then 128 else 136)
  else if i = 14 then (if v then 120 else 128)
  else if i = 15 then (if v then 136 else 120)
  else if i = 16 then 144
  else 123 - i

private def batchKeyByte (l : BatchLayout) (mem : Ram) (i : Nat) : BitVec 8 :=
  memLoad mem ((⟨.stack, BitVec.ofNat 64 (152 + i)⟩ : BatchAddr).addr l) 8

private def batchXorByte (l : BatchLayout) (mem : Ram) (i : Nat) : BitVec 8 :=
  batchKeyByte l mem i ^^^ memLoad mem ((⟨.src, BitVec.ofNat 64 i⟩ : BatchAddr).addr l) 8

private def batchWriteAddr (v : Bool) (i : Nat) : BatchAddr :=
  if i < 4 then ⟨.stack, BitVec.ofNat 64 (batchScratch v (13 + i))⟩
  else if i < 56 then ⟨.stack, BitVec.ofNat 64 (batchScratch v (i - 4))⟩
  else if i < 120 then ⟨.dst, BitVec.ofNat 64 (i - 56)⟩
  else ⟨.stack, 224⟩

private inductive BatchPayload where
  | key (i : Nat)
  | xor (i : Nat)
  | count

private def batchPayload (i : Nat) : BatchPayload :=
  if i < 4 then .key (13 + i)
  else if i < 56 then .xor (i - 4)
  else if i < 120 then .xor (i - 56)
  else .count

private def batchWidth (i : Nat) := if i < 120 then 8 else 64

private def BatchPayload.get (p : BatchPayload) (l : BatchLayout) (mem : Ram) (ct : BitVec 64)
    (w : Nat) : BitVec w :=
  match p with
  | .key i => (batchKeyByte l mem i).setWidth w
  | .xor i => (batchXorByte l mem i).setWidth w
  | .count => (ct + 1).setWidth w

private def batchValue (l : BatchLayout) (mem : Ram) (count : BitVec 64) (i : Nat) :=
  (batchPayload i).get l mem count (batchWidth i)

private theorem batchValueAs {l : BatchLayout} {mem : Ram} {ct : BitVec 64} (i w : Nat)
    (p : BatchPayload) (hp : batchPayload i = p) (hw : batchWidth i = w) :
    (batchValue l mem ct i).setWidth w = p.get l mem ct w := by
  rw [batchValue, hp, hw, BitVec.setWidth_eq]

private def batchState (l : BatchLayout) (mem : Ram) (count : BitVec 64) : Nat → Ram
  | 0 => mem
  | i + 1 => memStore (batchState l mem count i) ((batchWriteAddr l.variant i).addr l)
      (batchValue l mem count i)

private def batchReadsFrom (v : Bool) (a : BatchAddr) (w : Nat) (origin : Option Nat) : Nat → Bool
  | 0 => origin.isNone
  | i + 1 =>
    let loc := batchWriteAddr v i
    let k := batchWidth i
    if a = loc ∧ w = k ∧ w % 8 = 0 ∧ w ≤ 128 then origin == some i
    else loc.apart a (k / 8) (w / 8) && batchReadsFrom v a w origin i

private def batchLoaded (l : BatchLayout) (mem : Ram) (count : BitVec 64)
    (a : BatchAddr) (w : Nat) : Option Nat → BitVec w
  | none => memLoad mem (a.addr l) w
  | some j => (batchValue l mem count j).setWidth w

private theorem batchLoadAt {l : BatchLayout} {mem actual : Ram} {count : BitVec 64} {i : Nat}
    (h : actual = batchState l mem count i) (a : BatchAddr) (w : Nat) (origin : Option Nat)
    {addr : BitVec 64} (ha : addr = a.addr l) (hr : batchReadsFrom l.variant a w origin i = true) :
    memLoad actual addr w = batchLoaded l mem count a w origin := by
  subst actual addr
  induction i with
  | zero => cases origin <;> first | rfl | contradiction
  | succ i ih =>
    simp only [batchReadsFrom] at hr
    split at hr
    · obtain rfl := beq_iff_eq.mp hr
      obtain ⟨rfl, rfl, hm, hw⟩ := ‹_ ∧ _ ∧ _ ∧ _›
      simp only [batchLoaded, batchState, BitVec.setWidth_eq]
      exact memLoad_memStore_same _ _ _ hm hw
    · obtain ⟨ha, hr⟩ := Bool.and_eq_true_iff.mp hr
      rw [batchState, memLoad_memStore_of_rangeApart _ _ _ _ _ (BatchAddr.apart_sound ha)]
      exact ih hr

private theorem batchReadKnown {l : BatchLayout} {v : Bool} (hv : l.variant = v)
    {mem actual : Ram} {count : BitVec 64} {i : Nat} (h : actual = batchState l mem count i)
    (a : BatchAddr) (w : Nat) (origin : Option Nat) {addr : BitVec 64} (ha : addr = a.addr l)
    (hr : batchReadsFrom v a w origin i = true) :
    memLoad actual addr w = batchLoaded l mem count a w origin :=
  batchLoadAt h a w origin ha (hv.symm ▸ hr)

private theorem batchNext {l : BatchLayout} {mem actual : Ram} {count : BitVec 64} {i : Nat}
    (h : actual = batchState l mem count i) (j : Nat) (hj : i + 1 = j) {addr : BitVec 64}
    (ha : addr = (batchWriteAddr l.variant i).addr l)
    {w : Nat} {v : BitVec w} (hw : w = batchWidth i)
    (hv : v = (batchValue l mem count i).setWidth w) :
    memStore actual addr v = batchState l mem count j := by
  subst actual addr w v j
  rw [BitVec.setWidth_eq]
  rfl

private theorem batchFrameIn {r b a : BitVec 64} {len n : Nat} {x y : BitVec 64}
    (ha : a = b + x) (hr : r = b + y) (hl : r.toNat + len ≤ 2 ^ 32)
    (hin : (x - y).toNat + n ≤ len) : InRegion (span r len) a n := by
  have he := toNat_of_offsets ha hr hl hin
  change _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _
  unfold span
  simp only at *
  omega

private def batchRegions (l : BatchLayout) :=
  [span (l.base .stack + 72) 80, span (l.base .stack + 224) 8, span (l.base .dst) 64]

private theorem batchWrite_frame (l : BatchLayout)
    (hs : (l.base .stack + 72).toNat + 264 ≤ 2 ^ 32)
    (hd : (l.base .dst).toNat + 64 ≤ 2 ^ 32)
    (mem : Ram) (count : BitVec 64) (i : Nat) :
    RamWriteFrame mem (batchState l mem count i) (batchRegions l) := by
  induction i with
  | zero => exact RamWriteFrame.refl ..
  | succ i ih =>
    apply RamWriteFrame.memStore ih
    change InRegions (batchRegions l) ((batchWriteAddr l.variant i).addr l) (batchWidth i / 8)
    unfold batchWriteAddr
    split
    · refine ⟨_, List.Mem.head _, batchFrameIn rfl rfl (by omega) ?_⟩
      have hh : ∀ k : Fin 4, ((BitVec.ofNat 64 (batchScratch l.variant (13 + k.val)) - 72).toNat) + 1 ≤ 80 := by cases l.variant <;> decide +kernel
      simpa only [batchWidth, ite_eq_left (show i < 120 by omega), Nat.reduceDiv] using hh ⟨i, by assumption⟩
    · split
      · refine ⟨_, List.Mem.head _, batchFrameIn rfl rfl (by omega) ?_⟩
        have hh : ∀ k : Fin 56, ((BitVec.ofNat 64 (batchScratch l.variant (k.val - 4)) - 72).toNat) + 1 ≤ 80 := by cases l.variant <;> decide +kernel
        simpa only [batchWidth, ite_eq_left (show i < 120 by omega), Nat.reduceDiv] using hh ⟨i, by assumption⟩
      · split
        · refine ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
            batchFrameIn rfl (BitVec.add_zero _).symm hd ?_⟩
          simp only [batchWidth, ite_eq_left (show i < 120 by omega), Nat.reduceDiv, BitVec.sub_zero, BitVec.toNat_ofNat]
          omega
        · have hslot := toNat_of_offsets (a := l.base .stack + 224) rfl rfl hs
              (show ((224#64) - 72).toNat + 8 ≤ 264 by decide)
          change (l.base .stack + 224).toNat = (l.base .stack + 72).toNat + 152 at hslot
          refine ⟨_, List.Mem.tail _ (List.Mem.head _), batchFrameIn rfl rfl (by omega) ?_⟩
          simp only [batchWidth, ite_eq_right (show ¬ i < 120 by omega), Nat.reduceDiv, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]

private theorem batchFrame_load {l : BatchLayout} {mem actual : Ram} {count : BitVec 64} {i : Nat}
    (h : actual = batchState l mem count i) {a : BitVec 64} {n : Nat}
    (hr : Readable mem a n) : Readable actual a n := by
  subst actual
  induction i with
  | zero => exact hr
  | succ i ih => exact ih.memStore _ _

private theorem batchFrame_store {l : BatchLayout} {mem actual : Ram} {count : BitVec 64} {i : Nat}
    (h : actual = batchState l mem count i) {code : CodeMap} {a : BitVec 64} {n : Nat}
    (hw : Writable code mem a n) : Writable code actual a n := by
  subst actual
  induction i with
  | zero => exact hw
  | succ i ih => exact ih.memStore _ _

private theorem batchCmp (a b : BitVec 64) : ((cmpSpec a b).ZF = true) = (b = a) := by
  change ((a - b == 0) = true) = _
  rw [beq_iff_eq]
  apply propext
  constructor <;> intro h <;> bv_omega


private theorem batchOutputWords {l : BatchLayout} {mem m : Ram} {count : BitVec 64}
    (h : m = batchState l mem count 121) (i : Fin 8) :
    memLoad m (l.base .dst + BitVec.ofNat 64 (8 * i.val)) 64 =
      memLoad mem (l.base .src + BitVec.ofNat 64 (8 * i.val)) 64 ^^^
      memLoad mem (l.base .stack + 152 + BitVec.ofNat 64 (8 * i.val)) 64 := by
  refine batchXorWords (before := mem) (after := m) (dst := l.base .dst) (src := l.base .src)
    (key := l.base .stack + 152) ?_ i
  intro j
  have allReads : ∀ (v : Bool) (k : Fin 64),
      batchReadsFrom v ⟨.dst, BitVec.ofNat 64 k.val⟩ 8 (some (56 + k.val)) 121 = true := by
    decide +kernel
  have hj := j.isLt
  have hr := batchLoadAt h ⟨.dst, BitVec.ofNat 64 j.val⟩ 8 (some (56 + j.val)) rfl
    (allReads l.variant j)
  have hwide : 8 ≤ batchWidth (56 + j.val) := by simp [batchWidth, show 56 + j.val < 120 by omega]
  simp only [batchLoaded, batchValue, batchPayload, BatchPayload.get, BitVec.setWidth_setWidth_of_le _ hwide, ite_eq_right (show ¬ 56 + j.val < 4 by omega),
    ite_eq_right (show ¬ 56 + j.val < 56 by omega), ite_eq_left (show 56 + j.val < 120 by omega),
    Nat.add_sub_cancel_left, BitVec.setWidth_eq, batchXorByte, batchKeyByte, BatchAddr.addr,
    BitVec.ofNat_add, BitVec.add_assoc] at hr ⊢
  exact hr

private theorem batchLoadGuard {l : BatchLayout} {mem m : Ram} {count : BitVec 64} {i : Nat}
    (h : m = batchState l mem count i) {r base : BitVec 64} {len : Nat} (hr : Readable mem r len)
    {a off start : BitVec 64} (ha : a = base + off) (hb : r = base + start)
    (n : Nat) (hin : decide ((off - start).toNat + n ≤ len) = true) : LoadOk m a n :=
  LoadOk.of_offsets (batchFrame_load h hr) ha hb (of_decide_eq_true hin)

private theorem batchStoreGuard {l : BatchLayout} {mem m : Ram} {count : BitVec 64} {i : Nat}
    (h : m = batchState l mem count i) {code : CodeMap} {r base : BitVec 64} {len : Nat}
    (hr : Writable code mem r len) {a off start : BitVec 64} (ha : a = base + off)
    (hb : r = base + start) (n : Nat) (hin : decide ((off - start).toNat + n ≤ len) = true)
    {entry : BitVec 64} (cover : ∀ {m : Ram} {a : BitVec 64} {n : Nat}, Writable code m a n →
      RangeApart a n entry 1779) (pcOff bytes : Nat) (fit : decide (pcOff + bytes ≤ 1779) = true) :
    StoreOk code m a n (entry + BitVec.ofNat 64 pcOff) bytes := by
  have hw := Writable.of_offsets (batchFrame_store h hr) ha hb (of_decide_eq_true hin)
  exact storeOk_of_writable hw (RangeApart.right_sub (cover hw) (of_decide_eq_true fit))

private structure BatchGuard (α : Type) where
  test : Prop
  dec : Decidable test
  valid : test
  failure : α

private inductive BatchChecks (α : Type) where
  | one : BatchGuard α → BatchChecks α
  | seq : BatchChecks α → BatchChecks α → BatchChecks α

private def BatchChecks.run {α : Type} (gs : BatchChecks α) (out : α) : α :=
  match gs with
  | .one g => @ite α g.test g.dec out g.failure
  | .seq a b => a.run (b.run out)

private theorem BatchChecks.run_eq {α : Type} (gs : BatchChecks α) (out : α) :
    gs.run out = out := by
  induction gs generalizing out with
  | one g => exact ite_eq_left g.valid
  | seq a b ha hb => rw [run, ha, hb]

private theorem batchJump (p q : Prop) [Decidable p] [Decidable q] (hp : p = q)
    (yes no : LIR.Label) (vs : Values Value Reg.count) (m : Ram) :
    (if p then Transfer.jump (results := Reg.count) ⟨yes, vs, m⟩ else .jump ⟨no, vs, m⟩) =
      (Transfer.jump ⟨if q then yes else no, vs, m⟩ : Transfer Value Ram LIR.Label signature Reg.count) := by
  by_cases h : q
  · rw [ite_eq_left (hp.mpr h)]
    exact congrArg (fun t => Transfer.jump (results := Reg.count) (⟨t, vs, m⟩ : LIR.lifted.Location))
      (ite_eq_left h).symm
  · rw [ite_eq_right (fun v => h (hp.mp v))]
    exact congrArg (fun t => Transfer.jump (results := Reg.count) (⟨t, vs, m⟩ : LIR.lifted.Location))
      (ite_eq_right h).symm

open Lean Meta Elab Tactic

private def batchLocal (n : Name) : MetaM Expr := do
  return (← getLocalDeclFromUserName n).toExpr

private def batchAddrExpr (b : Name) (off : Nat) : MetaM Expr := do
  mkAppM ``BatchAddr.mk #[mkConst b, toExpr (BitVec.ofNat 64 off)]

private def batchMemoryIndex (states : Array Expr) (m : Expr) : MetaM Nat := do
  let some i := states.idxOf? m | throwError "unrecognized batch memory"
  return i

private def batchAddress (e : Expr) : MetaM (Name × Refine.Tactic.Addr) := do
  let addr ← Refine.Tactic.addrOf e
  if addr.base == (← batchLocal `sp) then return (``BatchBase.stack, addr)
  if addr.base.isAppOfArity ``HAdd.hAdd 6 && addr.base.getArg! 5 == (← batchLocal `offset) then
    let base := addr.base.getArg! 4
    if base == (← batchLocal `source) then return (``BatchBase.src, addr)
    if base == (← batchLocal `destination) then return (``BatchBase.dst, addr)
  throwError "unrecognized batch address {e}"

private def batchSimpContext (hyps : Array Expr) : MetaM Simp.Context := do
  let mut lemmas : SimpTheorems := {}
  lemmas ← lemmas.addConst ``setWidth_mergeGPR8
  for h in hyps do
    lemmas ← lemmas.add (.fvar h.fvarId!) #[] h
  Simp.mkContext (config := {zeta := false, zetaDelta := false, dsimp := false})
    (simpTheorems := #[lemmas]) (congrTheorems := ← getSimpCongrTheorems)

private structure BatchReplay where
  layout : Expr
  mem : Expr
  count : Expr
  variant : Bool
  states : Array Expr
  simpCtx : Simp.Context

private def batchBank : Name → BatchBase
  | ``BatchBase.stack => .stack
  | ``BatchBase.src => .src
  | _ => .dst

private def batchPayloadExpr : BatchPayload → Expr
  | .key i => mkApp (mkConst ``BatchPayload.key) (mkNatLit i)
  | .xor i => mkApp (mkConst ``BatchPayload.xor) (mkNatLit i)
  | .count => mkConst ``BatchPayload.count

private def batchPayloadValue (s : BatchReplay) (i w : Nat) : MetaM (Expr × Expr) := do
  let p := batchPayload i
  let ix := mkNatLit i
  let width := mkNatLit w
  let pe := batchPayloadExpr p
  let eq := mkAppN (mkConst ``batchValueAs) #[s.layout, s.mem, s.count, ix, width, pe,
    ← mkEqRefl pe, ← mkEqRefl width]
  let rhs ← match p with
    | .key j => mkAppM ``batchKeyByte #[s.layout, s.mem, mkNatLit j]
    | .xor j => mkAppM ``batchXorByte #[s.layout, s.mem, mkNatLit j]
    | .count => mkAppM ``HAdd.hAdd #[s.count, toExpr (1#64)]
  return (rhs, mkExpectedPropHint eq (← mkEq (← inferType eq).eq?.get!.2.1 rhs))

private def batchNormalizedRead (s : BatchReplay) (e : Expr) : MetaM Simp.Result := do
  let m := e.getArg! 2
  let addr := e.getArg! 3
  let wn := e.getArg! 4
  let some w ← (Lean.Meta.evalNat wn).run | throwError "nonliteral batch read width"
  let idx ← batchMemoryIndex s.states m
  let (b, parsed) ← batchAddress addr
  let off := parsed.val
  let ptrName := if idx == 4 && off == 240 then `batchSourcePtr
    else if idx == 56 && off == 216 then `batchDestPtr else Name.anonymous
  if w == 64 && b == ``BatchBase.stack && !ptrName.isAnonymous then
    if let some d := (← getLCtx).findFromUserName? ptrName then
      return {expr := d.type.eq?.get!.2.2, proof? := some d.toExpr}
  let a ← batchAddrExpr b off
  let location := BatchAddr.mk (batchBank b) (BitVec.ofNat 64 off)
  let mut origin : Option Nat := none
  for i in [:idx] do
    if location == batchWriteAddr s.variant i && w == batchWidth i then origin := some i
  let tested := mkAppN (mkConst ``batchReadsFrom) #[toExpr s.variant, a, wn, toExpr origin, mkNatLit idx]
  let cert := mkExpectedPropHint (← mkEqRefl (toExpr true)) (← mkEq tested (toExpr true))
  let read := mkAppN (mkConst ``batchReadKnown) #[s.layout, toExpr s.variant, ← mkEqRefl (toExpr s.variant),
    s.mem, m, s.count, mkNatLit idx,
    ← mkEqRefl m, a, wn, toExpr origin, addr, parsed.eq, cert]
  let slot := if b == ``BatchBase.stack && w == 64 && origin.isNone then
    [(240, `hSourceWord), (216, `hDestWord), (224, `hCount), (328, `hBatches), (248, `hCounter)].lookup off
    else none
  if let some h := slot then
    let h ← batchLocal h
    let rhs := (← inferType h).eq?.get!.2.2
    return { expr := rhs, proof? := some (← mkEqTrans read h) }
  if let some j := origin then
    let (v, hv) ← batchPayloadValue s j w
    return {expr := v, proof? := some (← mkEqTrans read hv)}
  if b == ``BatchBase.stack && w == 8 && 152 ≤ off && off < 216 then
    let v ← mkAppM ``batchKeyByte #[s.layout, s.mem, mkNatLit (off - 152)]
    return {expr := v, proof? := some (mkExpectedPropHint read (← mkEq e v))}
  let rhs ← mkAppM ``batchLoaded #[s.layout, s.mem, s.count, a, wn, toExpr origin]
  return { expr := rhs, proof? := some read }

private def batchSimplify (s : BatchReplay) (e : Expr) : MetaM Simp.Result := do
  let methods := Simp.mkDefaultMethodsCore #[]
  let methods := { methods with post := fun x => do
    if x.isAppOfArity ``memLoad 5 then
      return .done (← batchNormalizedRead s x)
    else methods.post x }
  return (← Simp.main e s.simpCtx (methods := methods)).1

private def batchStepProof (s : BatchReplay) (write : Expr) : MetaM (Expr × Expr) := do
  let i := s.states.size - 1
  let args := write.getAppArgs
  let ha ← batchSimplify s args[3]!
  let hv ← batchSimplify s args[5]!
  let addr ← Refine.Tactic.addrOf ha.expr
  let addrEq ← mkEqTrans (← ha.getProof' args[3]!) addr.eq
  let some w ← (Lean.Meta.evalNat args[4]!).run | throwError "expected batch write width"
  let (value, fromModel) ← batchPayloadValue s i w
  let valProof := mkExpectedPropHint (← hv.getProof' args[5]!) (← mkEq args[5]! value)
  let toModel ← mkEqTrans valProof (← mkEqSymm fromModel)
  let p := mkAppN (mkConst ``batchNext) #[s.layout, s.mem, args[2]!, s.count, mkNatLit i,
    ← mkEqRefl s.states.back!, mkNatLit (i + 1), ← mkEqRefl (mkNatLit (i + 1)), args[3]!, addrEq, args[4]!, args[5]!,
    ← mkEqRefl args[4]!, toModel]
  let ty ← mkEq write (← mkAppM ``batchState #[s.layout, s.mem, s.count, mkNatLit (i + 1)])
  return (p, ty)

private def batchGuard (s : BatchReplay) (cond : Expr) : MetaM Expr := do
  let store := cond.isAppOfArity ``StoreOk 6
  let k := if store then 1 else 0
  let m := cond.getArg! k
  let original := cond.getArg! (k + 1)
  let bytes := cond.getArg! (k + 2)
  let ha ← batchSimplify s original
  let (bank, addr) ← batchAddress ha.expr
  let stack := bank == ``BatchBase.stack
  let region ← batchLocal (if stack then `hStack else if store then `hDestination else `hSource)
  let regionAddr := (← inferType region).getAppArgs[(if stack || store then 2 else 1)]!
  let start ← Refine.Tactic.addrOf regionAddr
  let addrEq ← mkEqTrans (← ha.getProof' original) addr.eq
  let i ← batchMemoryIndex s.states m
  let common := #[s.layout, s.mem, m, s.count, mkNatLit i, ← mkEqRefl m]
  let bounds := #[original, addr.off, start.off, addrEq, start.eq, bytes, ← mkEqRefl (toExpr true)]
  let regionArgs := #[regionAddr, addr.base, mkNatLit (if stack then 264 else 64)]
  if !store then
    let hr ← if stack then mkAppM ``Writable.readable #[region] else pure region
    return mkAppN (mkConst ``batchLoadGuard) (common ++ regionArgs ++ #[hr] ++ bounds)
  let pc := cond.getArg! 4
  let some p ← Refine.Tactic.bvLit? pc | throwError "nonliteral batch PC"
  let entry := if s.variant then 0x1087a5 else 0x107315
  return mkAppN (mkConst ``batchStoreGuard) (common ++ #[cond.getArg! 0] ++ regionArgs ++
    #[region] ++ bounds ++ #[toExpr (BitVec.ofNat 64 entry), ← batchLocal `hRange,
      mkNatLit (p - entry), cond.getArg! 5, ← mkEqRefl (toExpr true)])

private partial def batchChecksTree (ty : Expr) (xs : Array Expr) : Expr :=
  if xs.size == 1 then mkApp2 (mkConst ``BatchChecks.one) ty xs[0]!
  else
    let k := xs.size / 2
    mkApp3 (mkConst ``BatchChecks.seq) ty (batchChecksTree ty (xs.extract 0 k))
      (batchChecksTree ty (xs.extract k xs.size))

private def batchTransfer (s : BatchReplay) (ev : Expr) : MetaM (Expr × Expr) := do
  let some (ty, lhs, rhs) := (← inferType ev).eq? | throwError "expected a block equation"
  let mut rhs := rhs
  let mut guards := #[]
  while rhs.isAppOfArity ``ite 5 do
    let args := rhs.getAppArgs
    if !args[1]!.isAppOf ``LoadOk && !args[1]!.isAppOf ``StoreOk then break
    let valid ← batchGuard s args[1]!
    guards := guards.push (mkAppN (mkConst ``BatchGuard.mk)
      #[ty, args[1]!, args[2]!, valid, args[4]!])
    rhs := args[3]!
  if guards.isEmpty then throwError "expected batch memory access guards"
  let gs := batchChecksTree ty guards
  let reduced := mkAppN (mkConst ``BatchChecks.run_eq) #[ty, gs, rhs]
  return (← mkEqTrans ev reduced, ← mkEq lhs rhs)

private theorem batchAtModel {α β : Type} (p : β → Prop) (x y : α) (f : α → β)
    (h : x = y) (more : p (f y)) : p (f x) := h.symm ▸ more

private theorem batchEvalOf {α : Type} (p : α → Prop) {a b : α} (h : a = b) (hb : p b) :
    p a := h.symm ▸ hb

elab "batch_xor_eval " th:ident : tactic => withMainContext do
  let g ← getMainGoal
  let lemma ← realizeGlobalConstNoOverloadWithInfo th
  let ev := mkAppN (mkConst lemma) #[← batchLocal `code, ← batchLocal `args, ← batchLocal `mem]
  let some (ty, lhs, rhs) := (← inferType ev).eq? | throwError "expected evaluated block"
  let goal ← g.getType
  let pred ← withLocalDeclD `out ty fun x => do
    let ex ← whnf goal
    let body := ex.getArg! 1
    lambdaTelescope body fun vs full => do
      let conj ← whnf full
      let eq := conj.getArg! 0
      let some (_, _, expected) := eq.eq? | throwError "expected transfer"
      let changed ← mkAppM ``And #[← mkEq x expected, conj.getArg! 1]
      let pb ← mkLambdaFVars vs changed
      let tgt := mkApp2 (mkConst ``Exists [Level.succ .zero]) (ex.getArg! 0) pb
      mkLambdaFVars #[x] tgt
  let sub ← mkFreshExprSyntheticOpaqueMVar (mkApp pred rhs)
  g.assign (mkAppN (mkConst ``batchEvalOf) #[ty, pred, lhs, rhs, ev, sub])
  let mut g := sub.mvarId!
  let ctx ← batchSimpContext #[← batchLocal `hsp, ← batchLocal `hoffset]
  let layout ← batchLocal `layout
  let variant ← whnf (← mkAppM ``BatchLayout.variant #[layout])
  let mem ← batchLocal `mem
  let count ← batchLocal `count
  let mut s := BatchReplay.mk layout mem count (variant.isConstOf ``Bool.true)
    #[mem] ctx
  let mut e := rhs
  let mut i := 0
  while e.isLet do
    let dom := e.letType!
    let write := e.letValue!
    let f := mkLambda e.letName! .default dom e.letBody!
    let state ← g.withContext do mkAppM ``batchState #[layout, mem, count, mkNatLit (i + 1)]
    let (step, stepTy) ← g.withContext (batchStepProof s write)
    let step := mkExpectedPropHint step stepTy
    let body := e.letBody!.instantiate1 state
    let next ← g.withContext do mkFreshExprSyntheticOpaqueMVar (mkApp pred body)
    g.assign (mkAppN (mkConst ``batchAtModel) #[dom, ty, pred, write, state, f, step, next])
    g := next.mvarId!
    s := { s with states := s.states.push state }
    if i == 3 || i == 55 then
      let off := if i == 3 then 240 else 216
      let n := if i == 3 then `batchSourcePtr else `batchDestPtr
      let (pr, t) ← g.withContext do
        let ptr ← mkAppM ``HAdd.hAdd #[← batchLocal `sp, toExpr (BitVec.ofNat 64 off)]
        let load ← mkAppM ``memLoad #[state, ptr, mkNatLit 64]
        let r ← batchNormalizedRead s load
        return (← r.getProof' load, ← mkEq load r.expr)
      let (_, g') ← g.note n pr t
      g := g'
    e := body
    i := i + 1
  unless i == 121 do throwError "expected 121 stores in the batch XOR block"
  let (p, ty) ← g.withContext do batchTransfer s (← mkEqRefl e)
  let rhs := ty.eq?.get!.2.2
  let cond := rhs.getArg! 1
  let hc ← g.withContext (batchSimplify s cond)
  let (jump, next) ← g.withContext do
    let count1 ← mkAppM ``HAdd.hAdd #[s.count, toExpr (1#64)]
    let batches ← batchLocal `batches
    let q ← mkEq count1 batches
    let dec ← synthInstance (mkApp (mkConst ``Decidable) q)
    let hq ← mkEqTrans (← hc.getProof' cond) (← mkAppM ``batchCmp #[batches, count1])
    let yes := (rhs.getArg! 3).getAppArgs.back!
    let no := (rhs.getArg! 4).getAppArgs.back!
    let args := yes.getAppArgs
    let branch := mkAppN (mkConst ``batchJump) #[cond, q, rhs.getArg! 2, dec, hq,
      args[4]!, no.getArg! 4, args[5]!, args[6]!]
    let next := ((← inferType branch).eq?.get!.2.2).getAppArgs.back!
    return (← mkEqTrans p branch, next)
  for (slot, off, name) in [(56, 216, `hFinalDest), (120, 224, `hPriorCount), (121, 248, `hFinalCtr),
      (121, 224, `hFinalCount)] do
    let orig ← g.withContext do
      let base ← if name == `hFinalCount then batchLocal `sp
        else do pure (← inferType (← batchLocal `hsp)).eq?.get!.2.1
      mkAppM ``memLoad #[s.states[slot]!, ← mkAppM ``HAdd.hAdd #[base, toExpr (BitVec.ofNat 64 off)], mkNatLit 64]
    let result ← g.withContext (batchSimplify s orig)
    let (p, ty) ← g.withContext do
      let rhs ← if name == `hFinalCount then mkAppM ``HAdd.hAdd #[s.count, toExpr (1#64)]
        else pure result.expr
      return (← result.getProof' orig, ← mkEq orig rhs)
    let (_, g') ← g.note name p ty
    g := g'
  let tail ← g.withContext do
    let ex ← whnf (← g.getType)
    unless ex.isAppOfArity ``Exists 2 do throwError "expected batch existential, got {ex.getAppFn}"
    let body := ex.getArg! 1
    let facts ← whnf (body.beta #[next])
    unless facts.isAppOfArity ``And 2 do throwError "expected batch conjunction, got {facts.getAppFn}"
    let tail ← mkFreshExprSyntheticOpaqueMVar (facts.getArg! 1)
    let both := mkAppN (mkConst ``And.intro) #[facts.getArg! 0, facts.getArg! 1, jump, tail]
    g.assign (mkAppN (mkConst ``Exists.intro [Level.succ .zero])
      #[ex.getArg! 0, body, next, both])
    return tail.mvarId!
  replaceMainGoal [tail]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem batch_xor (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (sp source destination offset count batches counter : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hoffset : args[5].get 64 = offset)
    (hStack : Writable code mem (sp + 72) 264)
    (hSource : Readable mem (source + offset) 64)
    (hDestination : Writable code mem (destination + offset) 64)
    (hDestApart : (destination + offset).toNat + 64 ≤ (sp + 72).toNat ∨
      (sp + 72).toNat + 264 ≤ (destination + offset).toNat)
    (hSrcApart : (source + offset).toNat + 64 ≤ (sp + 72).toNat ∨
      (sp + 72).toNat + 264 ≤ (source + offset).toNat)
    (hSourceWord : memLoad mem (sp + 240) 64 = source)
    (hDestWord : memLoad mem (sp + 216) 64 = destination)
    (hCount : memLoad mem (sp + 224) 64 = count)
    (hBatches : memLoad mem (sp + 328) 64 = batches)
    (hCounter : memLoad mem (sp + 248) 64 = counter) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1087a5 else .l107315), args, mem⟩ = .jump next ∧
      next.label = (if count + 1 = batches then
        (if use256 then .l109509 else .l10805f) else
        (if use256 then .l108e98 else .l107a08)) ∧
      next.arguments[1]'(by change 1 < 53; decide) = ⟨64, count + 1⟩ ∧
      next.arguments[2]'(by change 2 < 53; decide) = ⟨64, destination⟩ ∧
      next.arguments[9]'(by change 9 < 53; decide) = ⟨64, counter⟩ ∧
      memLoad next.store (sp + 224) 64 = count + 1 ∧
      (∀ i : Fin 8,
        memLoad next.store (destination + offset + BitVec.ofNat 64 (8 * i.val)) 64 =
          memLoad mem (source + offset + BitVec.ofNat 64 (8 * i.val)) 64 ^^^
            memLoad mem (sp + 152 + BitVec.ofNat 64 (8 * i.val)) 64) ∧
      (∀ r : Fin 53, r.val ∈ [4, 5, 22, 39, 50, 51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store
        [span (sp + 72) 80, span (sp + 224) 8, span (destination + offset) 64] := by
  let layout := batchLayout use256 hStack hSource hDestination hDestApart hSrcApart
  have hRange {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x1087a5 else 0x107315) 1779 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107315 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1087a5 x hx))).apart
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hRange ⊢
  case' false => batch_xor_eval batchXor128_eval
  case' true => batch_xor_eval batchXor256_eval
  all_goals
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg (fun x => Value.mk 64 (x + 1)) hPriorCount
    · exact congrArg (Value.mk 64) hFinalDest
    · exact congrArg (Value.mk 64) hFinalCtr
    · exact hFinalCount
    · exact @batchOutputWords layout mem _ count rfl
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · exact batchWrite_frame layout hStack.readable.low hDestination.readable.low mem count 121

end AesGcm.Proofs.Machine.CTR
