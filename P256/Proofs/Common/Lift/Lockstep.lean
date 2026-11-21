import P256.Proofs.Common.Lift.IR
import X86Proofs.Instructions.Branch.Cond

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG

inductive Runs [Bindings] (code : CodeMap) : Nat → RamState → RamState → Prop
  | refl (s : RamState) : Runs code 0 s s
  | step {k : Nat} {s t u : RamState} (h : X86.Machine.step s = some (.next t))
      (inside : k ≠ 0 → CodeAt code t.RIP) (rest : Runs code k t u) : Runs code (k + 1) s u

def RunsEffect [Bindings] (pre : RamState → Prop) (code : CodeMap) (e : RamState → Effect) :
    Prop :=
  ∀ s, ReadyToStep s → CodeIn code s → pre s → ∃ m s', Runs code m s s' ∧ ReadyToStep s' ∧
    (e s).Holds s s'

def GoesTo (pre : RamState → Prop) (e : RamState → Effect) (t : BitVec 64) (s : RamState) : Prop :=
  pre s ∧ (e s).rip = t

def RepPre (p : BitVec 64) (pre : RamState → Prop) (s : RamState) : Prop :=
  (s.RIP = p ∧ (Operand.reg 1 : Operand 64).read s = 0) ∨ pre s

abbrev RegMap := List (Nat × Nat)

def RegMap.has (ρ : RegMap) (i j : Nat) : Bool := ρ.any fun e => e.1.beq i && e.2.beq j

def At (ρ : RegMap) {n : Nat} (regs : Values Value n) (t : RamState) : Prop :=
  ∀ i j, (i, j) ∈ ρ → ∃ hj : j < n, regs[j] = (Reg.ofIndex i).read t

def operandsOk (ρ : RegMap) (L : List Reg) {n : Nat} (args : Vector (Fin n) L.length) : Bool :=
  (L.zip args.toList).all fun e => e.1.isTracked && ρ.has e.1.index e.2.val

def EffectPart.ofReg : Reg → EffectPart
  | .flag f => .flag f
  | r => .reg r

def EffectPart.Valid (e : RamState → Effect) (cs : List Component) : EffectPart → Prop
  | .reg r => r.isFlag = false ∧ r ≠ .fcc ∧ r.component ∈ cs
  | .flag f => ∀ s, ((e s).flag s f).isSome = true
  | .target => True

def EffectPart.isAt : EffectPart → Nat → Bool
  | .reg r, i => r.isTracked && !r.isFlag && r.index.beq i
  | .flag f, i => (Reg.flag f).index.beq i
  | .target, _ => false

def RemapOk (ρ : RegMap) (outs : List (EffectPart × Nat)) (cs : List Component) (ρ' : RegMap) :
    Prop :=
  ∀ i j, (i, j) ∈ ρ' →
    (EffectPart.ofReg (Reg.ofIndex i), j) ∈ outs ∨ ((Reg.ofIndex i).component ∉ cs ∧ (i, j) ∈ ρ)

def remapOk (ρ : RegMap) (outs : List (EffectPart × Nat)) (cs : List Component) : RegMap → Bool
  | [] => true
  | (i, j) :: ρ' =>
    bif outs.any (fun o => o.1.isAt i && o.2.beq j) then remapOk ρ outs cs ρ'
    else i.blt Reg.count && !cs.any (fun c => (Reg.positions c).any (·.beq i)) &&
      match ρ.dropWhile (fun e => e.1.blt i) with
      | (i', j') :: ρ => i'.beq i && j'.beq j && remapOk ρ outs cs ρ'
      | [] => false

def RegMap.mask (ρ : RegMap) : Nat := ρ.foldr (fun e m => m ||| 1 <<< e.1) 0

def maskLe (m m' : Nat) : Bool := (m &&& m').beq m

def RegMap.args (ρ : RegMap) (n : Nat) [NeZero n] : Vector (Fin n) Reg.count :=
  ⟨((List.range Reg.count).map fun i => Fin.ofNat n ((ρ.lookup i).getD i)).toArray, by simp⟩

def entryMap (m : Nat) : RegMap :=
  (List.range Reg.count).filterMap fun i => if m.testBit i then some (i, i) else none

structure InstrSpec [Bindings] (p : BitVec 64) (ib : List UInt8) (pre : RamState → Prop)
    (e : RamState → Effect) (R : List Reg) (F : List StatusFlag) (cs : List Component) :
    Prop where
  run : RunsEffect pre (codeRange p ib) e
  isLocal : LocalWith F e
  reads : ReadsOnly p e R
  closed : Reg.FlagsClosed R
  params : ∀ f ∈ F, Reg.flag f ∈ R
  pre : ∀ s, s.RIP = p → pre (stateOf p (entriesOf (Reg.operands R F) s) s.external) → pre s
  components : ∀ s c, c.isMem = false → (c ∈ (e s).components ↔ c ∈ cs)

def Reached (P : Lifted) (u : RamState) :
    Transfer Value Ram P.Label signature Reg.count → Prop
  | .jump next => u.RIP = P.address next.label ∧
      (∀ i (h : i < Reg.count), Live (P.live next.label) i →
        next.arguments[i] = (Reg.ofIndex i).read u) ∧ next.store = u.external
  | .call next fr => u.RIP = P.address next.label ∧
      (∀ i (h : i < Reg.count), Live (P.live next.label) i →
        next.arguments[i] = (Reg.ofIndex i).read u) ∧ next.store = u.external ∧ P.FrameOk fr
  | .returned o => o.tag = some ⟨64, u.RIP⟩ ∧
      (∀ i (h : i < Reg.count), Live P.retLive i → o.values[i] = (Reg.ofIndex i).read u) ∧
      o.store = u.external
  | .stuck => True

section Defs

variable [Bindings] (code : CodeMap) (P : Lifted) (blockCode : CodeMap) {n : Nat}

structure Start (ρ : RegMap) (p : BitVec 64) (bytes : List UInt8) (regs : Values Value n)
    (mem : Ram) (t : RamState) : Prop where
  rip : t.RIP = p
  related : At ρ regs t
  store : mem = t.external
  ready : ReadyToStep t
  sse : Prelude.SupportedSSE Bindings.processor t
  codeIn : CodeIn code t
  bytesIn : ∀ x ∈ codeRange p bytes, x ∈ blockCode
  blockIn : ∀ x ∈ blockCode, x ∈ code

structure Finish (k : Nat) (tr : Transfer Value Ram P.Label signature Reg.count) (t u : RamState) :
    Prop where
  run : ∃ m, Runs blockCode m t u ∧ (k = 0 → m = 0)
  ready : ReadyToStep u
  sse : Prelude.SupportedSSE Bindings.processor u
  codeIn : CodeIn code u
  fixed : fixedPart u = fixedPart t
  reached : Reached P u tr

structure Rest (ρ : RegMap) (k : Nat) (p : BitVec 64) (bytes : List UInt8)
    (tail : Block Op P.Label signature Reg.count n) : Prop where
  nonempty : 0 < k → bytes ≠ []
  run : ∀ regs mem t, Start code blockCode ρ p bytes regs mem t →
    tail.eval (dialect code) regs mem ≠ .stuck →
      ∃ u, Finish code P blockCode k (tail.eval (dialect code) regs mem) t u

structure RestInside (ρ : RegMap) (e : RamState → Effect) (cs : List Component)
    (outs : List (EffectPart × Nat)) (k : Nat) (p : BitVec 64) (bytes : List UInt8)
    (tail : Block Op P.Label signature Reg.count n) : Prop where
  run : ∀ regs mem t, Start code blockCode ρ p bytes regs mem t →
    (∀ oj ∈ outs, EffectPart.Valid e cs oj.1 ∧ ∃ h : oj.2 < n, regs[oj.2] = oj.1.value (e t) t) →
    tail.eval (dialect code) regs mem ≠ .stuck →
      ∃ u, Finish code P blockCode (k + 1) (tail.eval (dialect code) regs mem) t u

end Defs

def condFlags (cc : BitVec 4) : List StatusFlag :=
  match cc.toNat / 2 with
  | 0 => [.OF]
  | 1 => [.CF]
  | 2 => [.ZF]
  | 3 => [.CF, .ZF]
  | 4 => [.SF]
  | 5 => [.PF]
  | 6 => [.SF, .OF]
  | _ => [.ZF, .SF, .OF]

def condReads (cc : BitVec 4) : List Reg := (condFlags cc).map Reg.flag

def flagsOf (fs : List StatusFlag) (vs : List Value) : StatusFlags :=
  (fs.zip vs).foldr (fun fv acc => acc.set fv.1 fv.2.truth) ⟨false, false, false, false, false, false⟩

def condOp (cc : BitVec 4) {k : Nat} (v : Vector Value k) : Value :=
  Value.ofBool (condHolds cc (flagsOf (condFlags cc) v.toList))

end P256.Proofs.Lift
