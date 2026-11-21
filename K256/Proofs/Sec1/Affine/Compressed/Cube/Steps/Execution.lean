import K256.Proofs.Sec1.Affine.Compressed.Cube.Steps.Residue
import K256.Proofs.Sec1.Affine.Compressed.Cube.Steps.Words
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Sec1.Sqrt.WordEquality

namespace K256.Proofs.Sec1.Affine.Compressed

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

private theorem storeInBlock {m : Ram} {code : CodeMap} {a pc : Word} {n k : Nat}
    (h : Writable code m a n) (hc : ∀ e ∈ codeRange 0x12065f bytes_l12065f, e ∈ code)
    (hp : (pc - 0x12065f).toNat + k ≤ 1700) : StoreOk code m a n pc k := by
  have len : 1700 ≤ bytes_l12065f.length := by decide +kernel
  have e := ParseSignature.storeOk_of_codeRange h hc (Nat.le_trans hp len)
  have he : 0x12065f + BitVec.ofNat 64 (pc - 0x12065f).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rwa [he] at e

private theorem guarded {α : Type} (p : Prop) [Decidable p] (yes no out : α)
    (h : p) (rest : yes = out) : (if p then yes else no) = out := by rwa [ite_eq_left h]

open Lean Meta Elab Tactic in
private partial def proveGuards (s : K256.Proofs.Refine.Tactic.Shared) (hc l out : Expr) :
    MetaM Expr := do
  let l := l.consumeMData
  unless l.isAppOfArity ``ite 5 do
    unless ← withAssignableSyntheticOpaque (isDefEq l out) do
      throwError "unexpected transfer at the end of the cube block"
    return ← mkEqRefl l
  let #[ty, p, inst, yes, no] := l.getAppArgs | failure
  let a := p.getAppArgs
  let h ← if p.isAppOfArity ``LoadOk 3 then do
    let some h ← K256.Proofs.Refine.Tactic.loadProof? s a[0]! a[1]! a[2]!
      | throwError "cube load outside the stack region"
    pure h
  else do
    unless p.isAppOfArity ``StoreOk 6 do throwError "unexpected guard {p.getAppFn}"
    let some (.offsets r hw fa hin) ← K256.Proofs.Refine.Tactic.partOf? s a[1]! a[2]! a[3]! true
      | throwError "stack write outside workspace"
    let hw ← mkAppM ``Writable.of_offsets #[hw, fa.eq, r.addr.eq, hin]
    let f := mkAppN (mkConst ``storeInBlock) #[a[1]!, a[0]!, a[2]!, a[4]!, a[3]!, a[5]!, hw, hc]
    pure (mkApp f (← mkDecideProof (← inferType f).bindingDomain!))
  return mkAppN (mkConst ``guarded) #[ty, p, inst, yes, no, out, h, ← proveGuards s hc yes out]

open Lean Meta Elab Tactic in
elab "cube_guards" hc:ident : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, l, r) := (← g.getType).eq? | throwError "expected equality"
  let sh ← K256.Proofs.Refine.Tactic.Shared.new #[]
  let cover ← getLocalDeclFromUserName hc.getId
  g.assign (← proveGuards sh cover.toExpr l r)
  replaceMainGoal []

private theorem savedX_of_loads {m : Ram} {sp : Word} {xs : Limbs}
    (h0 : memLoad m (sp + 80) 64 = xs[0]) (h1 : memLoad m (sp + 88) 64 = xs[1])
    (h2 : memLoad m (sp + 64) 64 = xs[2]) (h3 : memLoad m (sp + 48) 64 = xs[3])
    (h4 : memLoad m (sp + 72) 64 = xs[4]) : savedX m sp = xs := by
  apply Vector.ext
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> assumption

open Lean Meta Elab Tactic in
elab "cube_read" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, l, r) := (← instantiateMVars (← g.getType)).eq? | failure
  let #[_, _, initial, address, width] := l.getAppArgs | failure
  let bytes ← mkAppM ``HDiv.hDiv #[width, mkNatLit 8]
  let sh ← K256.Proofs.Refine.Tactic.Shared.new #[]
  let mut ram := initial
  let mut proof ← mkEqRefl l
  let mut value := l
  while ram.isAppOfArity ``memStore 6 do
    let #[_, _, previous, written, bits, word] := ram.getAppArgs | failure
    if let some same ← K256.Proofs.Refine.Tactic.sameAddr? written address then
      let hit := mkAppN (mkConst ``memLoad_memStore_eq)
        #[previous, written, address, bits, word, same, ← mkEqRefl (mkNatLit 0), CFG.Eval.leProof 64 128]
      proof ← mkEqTrans proof hit
      value := word
      break
    let some apart ← K256.Proofs.Refine.Tactic.apartProof? sh written (mkNatLit 8) address bytes
      | throwError "overlapping cube stack accesses"
    let miss := mkAppN (mkConst ``memLoad_memStore_of_rangeApart)
      #[previous, written, address, bits, word, width, apart]
    proof ← mkEqTrans proof miss
    value := mkAppN l.getAppFn (l.getAppArgs.set! 2 previous)
    ram := previous
  let rest ← mkFreshExprSyntheticOpaqueMVar (← mkEq value r)
  g.assign (← mkEqTrans proof rest)
  replaceMainGoal [rest.mvarId!]

private theorem preservedRegisters (P : Fin 53 → Prop) :
    P 22 → P 39 → P 50 → P 51 → ∀ i : Fin 53, i.val ∈ [22, 39, 50, 51] → P i := by
  intro h22 h39 h50 h51 i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  have mem : i = 22 ∨ i = 39 ∨ i = 50 ∨ i = 51 := by omega
  rcases mem with rfl | rfl | rfl | rfl <;> assumption

private theorem cubeGprs (P : Fin 53 → Prop) :
    P 1 → P 2 → P 3 → P 5 → P 8 → P 9 → P 12 → P 13 → P 14 → P 15 →
    ∀ i : Fin 53, i.val ∈ [1, 2, 3, 5, 8, 9, 12, 13, 14, 15] → P i := by
  intro h1 h2 h3 h5 h8 h9 h12 h13 h14 h15 i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  have mem : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 8 ∨ i = 9 ∨
      i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem valueWidth (w : Word) : (⟨64, w⟩ : Value) = ⟨64, (⟨64, w⟩ : Value).get 64⟩ := by
  simp only [Value.get_mk_setWidth, BitVec.setWidth_eq]

private theorem doubleShift (x : Word) : x <<< 1 = x + x := by bv_omega

private def fiveWords (x0 x1 x2 x3 x4 : Word) : Limbs := #v[x0, x1, x2, x3, x4]

private theorem cubeStoreRegion {a r x c d : Word} {n len : Nat} (ha : a = x + c) (hr : r = x + d)
    (hlow : r.toNat + len ≤ 2^32) (h : (c - d).toNat + n ≤ len) :
    InRegions [⟨r.toNat, len⟩] a n := by
  have e := toNat_of_offsets ha hr hlow h
  refine ⟨_, List.Mem.head _, ?_⟩
  change r.toNat ≤ a.toNat ∧ a.toNat + n ≤ r.toNat + len ∧ a.toNat + n ≤ 2^64
  omega

open Lean Meta Elab Tactic in
elab "cube_frame" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let #[o, m, regs] := t.getAppArgs | failure
  let S ← K256.Proofs.Refine.Tactic.Shared.new #[]
  let mut stack := #[]
  let mut ram := m
  while ram.isAppOfArity ``memStore 6 do
    stack := stack.push ram
    ram := ram.getArg! 2
  let mut h ← mkAppM ``RamWriteFrame.refl #[o, regs]
  for store in stack.reverse do
    let #[_, _, prev, a, w, v] := store.getAppArgs | failure
    let some (.offsets r _ fa hin) ← K256.Proofs.Refine.Tactic.partOf? S o a (mkNatLit 8) true | failure
    let within ← mkAppM ``cubeStoreRegion #[fa.eq, r.addr.eq, r.low, hin]
    h := mkAppN (mkConst ``RamWriteFrame.memStore) #[o, prev, regs, h, a, w, v, within]
  g.assign h
  replaceMainGoal []

def addSeven (u : Limbs) : Limbs := #v[u[0] + 7, u[1], u[2], u[3], u[4]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem cubeExecution {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code)
    (arithmetic : ∀ a b c d ok, let xs := maskedX a b c d ok
      FieldRepr (addSeven (cubeProduct xs (inputSquare xs)))
        ⟨(limbValue xs * limbValue xs * limbValue xs + 7) % modulus, Nat.mod_lt _ (by decide)⟩ 8) :
    CubeCall code := by
  intro args mem sp a b c d ok rsp rax r12 r13 r14 r3 r15 r5 hw
  have hc := fun e h => cover e (code_l12065f e h)
  have byte : (BitVec.ofNat 8 ok.toNat).setWidth 64 = BitVec.ofNat 64 ok.toNat := by cases ok <;> rfl
  have repr := arithmetic a b c d ok
  dsimp only at repr
  let mask := -(BitVec.ofNat 64 ok.toNat)
  let xs := fiveWords ((d &&& 0xfffffffffffff) &&& mask)
    ((shldResult 12 c d &&& 0xfffffffffffff) &&& mask)
    (shldResult 24 b c &&& (mask &&& 0xfffffffffffff))
    ((mask &&& 0xfffffffffffff) &&& shldResult 36 a b) ((a >>> 16) &&& mask)
  have hx : maskedX a b c d ok = xs := maskedX_eq_words a b c d ok
  rw [hx] at repr ⊢
  refine ⟨?_, ?_, ?eval, ?post⟩
  case eval =>
    cfg_eval [rsp, rax, byte, r12, r13, r14, r3, r15, r5,
      b_l12065f, b_l12065f_1, b_l12065f_2, b_l12065f_3, b_l12065f_4, b_l12065f_5,
      b_l12065f_6, b_l12065f_7, b_l12065f_8, b_l12065f_9, b_l12065f_10, b_l12065f_11,
      b_l12065f_12, b_l12065f_13, b_l12065f_14, b_l12065f_15, b_l12065f_16, b_l12065f_17,
      b_l12065f_18, b_l12065f_19, b_l12065f_20, b_l12065f_21]
    cube_guards hc
  case post =>
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply cubeGprs <;> exact valueWidth _
    · apply preservedRegisters <;> rfl
    · cube_read <;> rfl
    · cube_read <;> rfl
    · cube_read <;> rfl
    · cube_read <;> rfl
    · apply savedX_of_loads <;> cube_read <;> rfl
    · refine ⟨_, ?_, repr⟩
      lifted_word_reads []
      all_goals simp only [doubleShift, BitVec.setWidth_and, BitVec.reduceSetWidth]
      all_goals dsimp only [xs, mask]
      all_goals lifted_word_eq [fiveWords, addSeven,
        inputSquare120684H, inputSquare120705, inputSquare120777H, inputSquare1207E5H,
        inputSquare120856, inputSquareFinish, inputSquare1208C0, inputSquare,
        cubeProduct120934H, cubeProduct1209B8, cubeProduct120A3C, cubeProduct120ABBC,
        cubeProduct120B1A, cubeProduct120BA9, cubeProduct120C2B, cubeProduct120C87, cubeProduct]
    · cube_frame

end K256.Proofs.Sec1.Affine.Compressed
