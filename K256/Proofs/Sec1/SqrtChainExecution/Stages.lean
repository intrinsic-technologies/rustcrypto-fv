import K256.Proofs.Common.Field.Multiply
import K256.Proofs.Sec1.Sqrt.Entry
import K256.Proofs.Sec1.Sqrt.Finish
import K256.Proofs.Sec1.Parser.Control

namespace K256.Proofs.Sec1.SqrtChainExecution

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine Common.Field

def productPC : Vector LIR.Label 14 := #v[
  .l1159a4, .l115e4d, .l116316, .l1167bf, .l116c14, .l117297, .l117bde,
  .l118081, .l118511, .l118991, .l118e1a, .l119780, .l119cc0, .l11a14c]

def squarePC : Vector LIR.Label 13 := #v[
  .l115e4d, .l11629e, .l116747, .l116bd8, .l11703f, .l1176f2,
  .l118040, .l1184d0, .l118950, .l118da2, .l119258, .l119b94, .l11a110]

def squareCount : Vector Nat 13 := #v[1,3,3,2,11,22,44,88,44,3,23,6,2]

def factorIndex : Vector Nat 13 := #v[0,0,2,2,1,5,6,7,8,7,2,6,1]

def chainWord {α : Type} (sq : α → α) (mul : α → α → α) (a : α) (i : Nat) : α :=
  (SqrtChain.run sq mul a SqrtChain.chain).getD i a

private theorem run_suffix {α : Type} (sq : α → α) (mul : α → α → α) (a : α)
    (ss : List SqrtChain.Step) (vs : List α) :
    ∃ tail, SqrtChain.runFrom sq mul a vs ss = vs ++ tail ∧ tail.length = ss.length := by
  induction ss generalizing vs with
  | nil => exact ⟨[], (List.append_nil _).symm, rfl⟩
  | cons s ss ih =>
    obtain ⟨t, he, ht⟩ := ih (vs ++ [s.apply sq mul a vs])
    exact ⟨_ :: t, he.trans (List.append_assoc ..), congrArg Nat.succ ht⟩

private theorem run_join {α : Type} (sq : α → α) (mul : α → α → α) (a : α)
    (ss ts : List SqrtChain.Step) (vs : List α) :
    SqrtChain.runFrom sq mul a vs (ss ++ ts) =
      SqrtChain.runFrom sq mul a (SqrtChain.runFrom sq mul a vs ss) ts := by
  induction ss generalizing vs with
  | nil => rfl
  | cons _ _ ih => exact ih _

private theorem computedStep {α : Type} (sq : α → α) (mul : α → α → α) (a : α)
    (n : Nat) (s : SqrtChain.Step) (ok : SqrtChain.chain[n]? = some s)
    (deps : match s with | .sqr i _ => i ≤ n | .mul i j => i ≤ n ∧ j ≤ n) :
    chainWord sq mul a (n+1) = s.apply sq mul a (SqrtChain.run sq mul a SqrtChain.chain) := by
  obtain ⟨hn, idx⟩ := List.getElem?_eq_some_iff.mp ok
  have he := List.drop_eq_getElem_cons hn
  rw [idx] at he
  have hsplit := List.take_append_drop n SqrtChain.chain
  rw [he] at hsplit
  let v := SqrtChain.runFrom sq mul a [a] (SqrtChain.chain.take n)
  have len : v.length = n+1 := by
    obtain ⟨t,h,ht⟩ := run_suffix sq mul a (SqrtChain.chain.take n) [a]
    simp only [v, h, List.length_append, List.length_cons, List.length_nil, ht, List.length_take]
    omega
  have total : ∃ t, SqrtChain.run sq mul a SqrtChain.chain = v ++ s.apply sq mul a v :: t := by
    obtain ⟨t,h,_⟩ := run_suffix sq mul a (SqrtChain.chain.drop (n+1)) (v ++ [s.apply sq mul a v])
    refine ⟨t, (congrArg (SqrtChain.run sq mul a) hsplit.symm).trans ?_⟩
    rw [SqrtChain.run, run_join, SqrtChain.runFrom]
    exact h.trans (List.append_assoc ..)
  obtain ⟨t,h⟩ := total
  have keep (i : Nat) (hi : i ≤ n) : (SqrtChain.run sq mul a SqrtChain.chain).getD i a = v.getD i a := by
    rw [h, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  have atn : chainWord sq mul a (n+1) = s.apply sq mul a v := by
    rw [chainWord, h, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), len, Nat.sub_self]
    rfl
  rw [atn]
  cases s with
  | sqr i k => simp only [SqrtChain.Step.apply, keep i deps]
  | mul i j => simp only [SqrtChain.Step.apply, keep i deps.1, keep j deps.2]

theorem chainWord_step {α : Type} (sq : α → α) (mul : α → α → α) (a : α) (i : Fin 13) :
    let atWord := chainWord sq mul a
    atWord (2 * (i.val + 1)) = mul (atWord (2 * factorIndex[i])) (atWord (2 * i.val + 1)) ∧
    atWord (2 * (i.val + 1) + 1) = SqrtChain.iter sq squareCount[i] (atWord (2 * (i.val + 1))) := by
  have all : ∀ j : Fin 13,
      SqrtChain.chain[2*j.val+1]? = some (.mul (2*factorIndex[j]) (2*j.val+1)) ∧
      SqrtChain.chain[2*(j.val+1)]? = some (.sqr (2*(j.val+1)) squareCount[j]) ∧
      factorIndex[j] ≤ j.val := by decide +kernel
  obtain ⟨m,s,h⟩ := all i
  have hm := computedStep sq mul a (2*i.val+1) _ m ⟨by omega, Nat.le_refl _⟩
  exact ⟨(show 2*(i.val+1) = 2*i.val+1+1 by omega) ▸ hm,
    computedStep sq mul a _ _ s (Nat.le_refl _)⟩

theorem chainWord_first {α : Type} (sq : α → α) (mul : α → α → α) (a : α) :
    chainWord sq mul a 0 = a ∧ chainWord sq mul a 1 = sq a := by
  obtain ⟨t, ht, _⟩ := run_suffix sq mul a SqrtChain.chain [a]
  have head : chainWord sq mul a 0 = a := by
    change (SqrtChain.runFrom sq mul a [a] SqrtChain.chain).getD 0 a = a
    rw [ht]
    rfl
  refine ⟨head, ?_⟩
  have hs := computedStep sq mul a 0 (.sqr 0 1) rfl (Nat.le_refl _)
  exact hs.trans (congrArg sq head)

abbrev words (a : Limbs) := chainWord squareWords mulWords a

inductive SavedPlace where
  | stack (offset : Nat)
  | reg (index : Fin Reg.count)
  deriving DecidableEq

structure SavedLimb where
  place : SavedPlace
  product : Nat
  index : Fin 5

def savedLimbs (stage : Fin 14) : List SavedLimb := Id.run do
  let slot (off : Nat) (v : Nat × Fin 5) : SavedLimb := ⟨.stack off, v.1, v.2⟩
  let reg (r : Fin Reg.count) (v : Nat × Fin 5) : SavedLimb := ⟨.reg r, v.1, v.2⟩
  let slots (v : Nat) (p q r s t : Nat) :=
    [slot p (v,0), slot q (v,1), slot r (v,2), slot s (v,3), slot t (v,4)]
  let i := stage.val
  if i = 0 then return []
  let mut atoms := slots 0 352 328 304 336 320
  if i ≤ 12 then atoms := atoms ++ slots 1 240 288 312 256 248
  if i = 1 then atoms := atoms ++ [reg 5 (1,0), reg 13 (1,3), reg 12 (1,4)]
  if i = 2 then atoms := atoms ++ [slot 160 (2,0), reg 13 (2,1), reg 15 (2,2),
    reg 12 (2,3), slot 168 (2,3), reg 5 (2,4), slot 144 (2,4)]
  if 3 ≤ i ∧ i ≤ 10 then atoms := atoms ++ slots 2 160 176 208 168 144
  if i = 5 then atoms := atoms ++ [slot 88 (5,0), reg 15 (5,1), reg 13 (5,2),
    reg 3 (5,3), slot 80 (5,4)]
  if i = 6 then atoms := atoms ++ [slot 136 (6,0), reg 13 (6,1), reg 5 (6,2),
    reg 15 (6,3), reg 12 (6,4)]
  if 7 ≤ i ∧ i ≤ 11 then atoms := atoms ++ slots 6 136 192 264 104 112
  if 7 ≤ i ∧ i ≤ 9 then atoms := atoms ++ slots 7 120 96 128 80 88
  if i = 7 then atoms := atoms ++ [reg 5 (7,0), reg 12 (7,3)]
  if i = 8 then atoms := atoms ++ [slot 152 (8,0), slot 184 (8,1), reg 13 (8,1),
    reg 5 (8,2), slot 200 (8,3), reg 12 (8,3), slot 232 (8,4)]
  return atoms

def savedValue (a : Limbs) (s : SavedLimb) : Word :=
  if s.product = 0 then a[s.index] else (words a (2 * s.product))[s.index]

def savedAtoms (stage : Fin 14) (sp : Word) (a : Limbs) : List Atom :=
  (savedLimbs stage).map (fun s =>
    match s.place with
    | .stack off => .mem (sp + BitVec.ofNat 64 off) 64 (savedValue a s)
    | .reg r => .gpr r (savedValue a s)) ++
    (if stage.val = 13 then [.gpr 12 0x1000003d10] else [])

structure ProductState (code : CodeMap) (fr : Activation) (a : Limbs) (i : Fin 14)
    (args : Values Value Reg.count) (mem : Ram) : Prop where
  frame : Atom.All code args mem (LIR.Fn115950.frameAt productPC[i] fr)
  saved : Atom.All code args mem (savedAtoms i (fr.rsp - 440) a)
  squared : WordsAt mem (fr.rsp - 400) 64 (words a (2 * i.val + 1))
  copied : i.val ∈ [7,8,9] → WordsAt mem (fr.rsp - 440) 64 (words a (2 * i.val + 1))
  source : WordsAt mem fr.rsi 64 a
  sourceRead : Readable mem fr.rsi 40
  destWrite : Writable code mem fr.rdi 41
  widths : ∀ r : Fin Reg.count, r.val ∈ [3,5,12,13,14,15] → args[r].width = 64
  writes : RamWriteFrame fr.original mem [fr.region, ⟨fr.rdi.toNat, 41⟩]

structure Geometry (code : CodeMap) (fr : Activation) : Prop where
  cover : ∀ x ∈ LIR.fnCode, x ∈ code
  sourceStack : fr.rsi.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rsi.toNat
  destStack : fr.rdi.toNat + 41 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat
  sourceCode : fr.rsi.toNat + 40 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rsi.toNat
  destCode : fr.rdi.toNat + 41 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rdi.toNat
  stackCode : fr.rsp.toNat + 8 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.low.toNat

def counted (i : Fin 13) : Bool := 6 ≤ i.val && i.val ≤ 8

def srcReg (i : Fin 13) : Fin Reg.count := if i.val = 6 then 15 else 14

def dstReg (i : Fin 13) : Fin Reg.count := if i.val = 6 then 14 else if i.val = 4 then 5 else 3

def countReg (i : Fin 13) : Fin Reg.count := if i.val = 6 then 3 else 15

structure SquareState (code : CodeMap) (fr : Activation) (a : Limbs) (i : Fin 13)
    (args : Values Value Reg.count) (mem : Ram) : Prop where
  frame : Atom.All code args mem (LIR.Fn115950.frameAt squarePC[i] fr)
  saved : Atom.All code args mem (savedAtoms i.succ (fr.rsp - 440) a)
  operand : let base := fr.rsp - 440
    let p := words a (2 * (i.val + 1))
    if counted i then WordsAt mem base 64 p else WordsAt mem (base + 40) 64 (squareWords p)
  src : i.val ≠ 0 → args[srcReg i].get 64 = fr.rsp - 440
  dst : i.val ≠ 0 → args[dstReg i].get 64 = fr.rsp - 440 + 40
  counter : counted i = true → args[countReg i] = ⟨64, BitVec.ofNat 64 squareCount[i]⟩
  source : WordsAt mem fr.rsi 64 a
  sourceRead : Readable mem fr.rsi 40
  destWrite : Writable code mem fr.rdi 41
  widths : ∀ r : Fin Reg.count, r.val ∈ [3,5,12,13,14,15] → args[r].width = 64
  volatile : i.val ≠ 0 → ∀ r : Fin Reg.count, r.val ∈ [1,2,8,9] → args[r].width = 64
  writes : RamWriteFrame fr.original mem [fr.region, ⟨fr.rdi.toNat, 41⟩]

def MultiplyStage (code : CodeMap) (fr : Activation) (a : Limbs) (i : Fin 13) : Prop :=
  ∀ {args mem}, ProductState code fr a i.castSucc args mem →
    ∃ b m, Parser.Reaches code productPC[i.castSucc] args mem squarePC[i] b m ∧
      SquareState code fr a i b m

def SquareStage (code : CodeMap) (fr : Activation) (a : Limbs) (i : Fin 13) : Prop :=
  ∀ {args mem}, SquareState code fr a i args mem →
    ∃ b m, Parser.Reaches code squarePC[i] args mem productPC[i.succ] b m ∧
      ProductState code fr a i.succ b m

end K256.Proofs.Sec1.SqrtChainExecution
