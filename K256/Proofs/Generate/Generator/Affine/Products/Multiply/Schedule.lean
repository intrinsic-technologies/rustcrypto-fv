import K256.Proofs.Generate.Generator.Affine.Products.Multiply.Schedule.Words
import K256.Proofs.Generate.Generator.Affine.Products.Representation

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

structure ProductSlots (sp : Word) (m : Ram) (bx r12 r14 r15 : Word) : Prop where
  rbxAt : memLoad m (sp + 232) 64 = bx
  r12At : memLoad m (sp + 240) 64 = r12
  r14At : memLoad m (sp + 256) 64 = r14
  r15At : memLoad m (sp + 264) 64 = r15
  retAt : memLoad m (sp + 280) 64 = 0x10ee37

structure ProductNormalizeInput (sp : Word) (a : Registers) (m : Ram) (x y : Limbs) : Prop where
  rsp : a[4] = ⟨64, sp - 8⟩
  src : a[6] = ⟨64, sp + 152⟩
  dst : a[7] = ⟨64, sp + 376⟩
  base : a[3] = ⟨64, sp + 376⟩
  df : a[22] = ⟨1, 0⟩
  saved : ∀ j : Fin Reg.count, j.val ∈ [3,5,12,13,14,15] → a[j] = ⟨64, a[j].get 64⟩
  slot : memLoad m (sp - 8) 64 = 0x10ecb2
  xAt : WordsAt m (sp + 152) 64 x
  yAt : WordsAt m (sp + 192) 64 y

open Lean Meta Elab.Tactic in
elab "abstract_product_scratch" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let mut frame := target.consumeMData
  for _ in [:3] do
    unless frame.isAppOfArity ``And 2 do throwError "expected post conjunction {frame.getAppFn.constName?}"
    frame := frame.appArg!.consumeMData
  unless frame.isAppOfArity ``RamWriteFrame 3 do throwError "expected write frame"
  let mut mem := frame.getArg! 1
  let mut values := #[]
  let mut indices : Std.HashMap Expr Nat := {}
  while mem.isAppOfArity ``memStore 6 do
    let addr ← Refine.Tactic.addrOf (mem.getArg! 3)
    let value := mem.getArg! 5
    if addr.val < 232 && !indices.contains value &&
        (value.find? (·.isAppOf ``memLoad)).isSome then
      indices := indices.insert value values.size
      values := values.push value
    mem := mem.getArg! 2
  let mut norm := target.consumeMData.getArg! 0
  while norm.isForall do norm := norm.bindingBody!.consumeMData
  unless norm.isAppOfArity ``ProductNormalizeInput 5 do throwError "expected normalization input"
  let regs := norm.getArg! 1
  let some regs ← CFG.Eval.vectorElements? regs | throwError "expected known register vector"
  for i in [0,1,2,5,8,9,10,11,12,13,14,15] do
    let v := regs[i]!
    unless v.isAppOfArity ``Value.mk 2 do continue
    let value := v.getArg! 1
    if value.hasFVar && !indices.contains value then
      indices := indices.insert value values.size
      values := values.push value
  let decls ← values.mapM fun v => do pure (`scratch, ← inferType v)
  let statement ← withLocalDeclsDND decls fun xs =>
    mkForallFVars xs (target.replace fun e => indices[e]?.map (xs[·]!))
  let general ← mkFreshExprSyntheticOpaqueMVar statement
  goal.assign (mkAppN general values)
  let (_, post) ← general.mvarId!.introN values.size
  replaceMainGoal [post]

private theorem wordWidth (x : Word) : Value.mk 64 x = ⟨64,(Value.mk 64 x).get 64⟩ := by
  simp only [Value.get, BitVec.setWidth_eq]

private theorem productRegisterWidths {b : Registers}
    (h3 : b[3] = ⟨64, b[3].get 64⟩)
    (h5 : b[5] = ⟨64, b[5].get 64⟩)
    (h12 : b[12] = ⟨64, b[12].get 64⟩)
    (h13 : b[13] = ⟨64, b[13].get 64⟩)
    (h14 : b[14] = ⟨64, b[14].get 64⟩)
    (h15 : b[15] = ⟨64, b[15].get 64⟩) :
    ∀ j : Fin Reg.count, j.val ∈ [3,5,12,13,14,15] → b[j] = ⟨64, b[j].get 64⟩ := by
  rintro ⟨i, hi⟩ hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

private theorem productControlRegisters {a b : Registers}
    (h22 : b[22] = a[22])
    (h39 : b[39] = a[39])
    (h50 : b[50] = a[50])
    (h51 : b[51] = a[51]) :
    ∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → b[j] = a[j] := by
  rintro ⟨i, hi⟩ hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl <;> assumption

private theorem productSlotWithin {a sp k : Word} (low : (sp - 8).toNat + 288 ≤ 2^32)
    (atOffset : a = sp + k) (fits : (k - (0 - 8)).toNat + 8 ≤ 288) :
    InRegions [⟨(sp - 8).toNat, 288⟩] a 8 := by
  have addr := toNat_of_offsets atOffset (addr_sub sp 8) low fits
  refine ⟨_, List.mem_cons_self, ?_⟩
  change (sp - 8).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (sp - 8).toNat + 288 ∧ a.toNat + 8 ≤ 2^64
  omega

open Lean Meta Elab.Tactic in
elab "coordinate_frame" low:ident : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``RamWriteFrame 3 do throwError "expected a memory frame"
  let origin := t.getArg! 0
  let regions := t.getArg! 2
  let bound := (← getLocalDeclFromUserName low.getId).toExpr
  let mut mem := t.getArg! 1
  let mut writes := #[]
  while mem.isAppOfArity ``memStore 6 do
    let addr := mem.getArg! 3
    let off ← Refine.Tactic.addrOf addr
    let partialProof := mkAppN (mkConst ``productSlotWithin) #[addr,off.base,off.off,bound,off.eq]
    let inside := mkApp partialProof (← mkDecideProof (← inferType partialProof).bindingDomain!)
    writes := writes.push (mem,inside)
    mem := mem.getArg! 2
  unless mem == origin do throwError "unexpected initial memory"
  let mut frame := mkApp2 (mkConst ``RamWriteFrame.refl) origin regions
  for (write, inside) in writes.reverse do
    frame := mkAppN (mkConst ``RamWriteFrame.memStore)
      #[origin,write.getArg! 2,regions,frame,write.getArg! 3,write.getArg! 4,write.getArg! 5,inside]
  g.assign frame
  replaceMainGoal []

private theorem storeAtProductPC {m : Ram} {p addr : Word} {len : Nat}
    (hw : Writable Extracted.programImage m addr 8)
    (within : (p - 0x10e4c0).toNat + len ≤ 2034) :
    StoreOk Extracted.programImage m addr 8 p len := by
  have bound : 2034 ≤ bytes_l10e4c0.length := by decide +kernel
  have ok := K256.Proofs.ParseSignature.storeOk_of_codeRange hw
    (fun x hx => K256.Proofs.Common.fnCode_subset_programImage x (code_l10e4c0 x hx)) (Nat.le_trans within bound)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, show 0x10e4c0 + (p - 0x10e4c0) = p by bv_omega] at ok

open Lean Meta Elab.Tactic in
elab "coordinate_guards" : tactic => withMainContext do
  let target ← getMainTarget
  let some (_, lhs, rhs) := target.eq? | throwError "expected a transfer equation"
  let shared ← Refine.Tactic.Shared.new #[]
  let env : Sec1.Sqrt.WordReads.Env := ⟨shared, #[], (← Refine.Tactic.regions).map (·.addr.base)⟩
  let mut branch := lhs.consumeMData
  let mut guards := #[]
  let ty := branch.getArg! 0
  while branch.isAppOfArity ``ite 5 do
    let cond := branch.getArg! 1
    let proof ← if cond.isAppOfArity ``LoadOk 3 then do
        let args := cond.getAppArgs
        let addr := args[1]!
        let r ← (Sec1.Sqrt.WordReads.normalize env addr).run' {}
        let (s, _) ← Meta.simp r.expr shared.norm shared.normProcs
        let result ← r.mkEqTrans s
        let some valid ← Refine.Tactic.loadProof? shared args[0]! result.expr args[2]!
          | throwError "unknown load location {result.expr}"
        if let some h := result.proof? then
          let f ← withLocalDeclD `addr (← inferType addr) fun x =>
            mkLambdaFVars #[x] (mkAppN cond.getAppFn (args.set! 1 x))
          mkEqMPR (← Meta.mkCongrArg f h) valid
        else pure valid
      else do
        unless cond.isAppOfArity ``StoreOk 6 do throwError "unexpected guard {cond.getAppFn}"
        let args := cond.getAppArgs
        let writable ← mkAppM ``Writable #[args[0]!, args[1]!, args[2]!, args[3]!]
        let some h ← Refine.Tactic.regionAtom? shared writable | throwError "unknown write location"
        let f := mkAppN (mkConst ``storeAtProductPC) #[args[1]!,args[4]!,args[2]!,args[5]!,h]
        pure (mkApp f (← mkDecideProof (← inferType f).bindingDomain!))
    let next := branch.getArg! 3
    let guard := mkAppN (mkConst ``if_pos [.one]) #[cond,branch.getArg! 2,proof,ty,next,branch.getArg! 4]
    guards := guards.push (branch,next,guard)
    branch := next.consumeMData
  let last ← mkFreshExprSyntheticOpaqueMVar (← mkEq branch rhs)
  let mut p := last
  for (before,after,h) in guards.reverse do
    p := mkApp6 (mkConst ``Eq.trans [.one]) ty before after rhs h p
  (← getMainGoal).assign p
  replaceMainGoal [last.mvarId!]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem productBlockCall {sp : Word} {a : Registers} {m : Ram}
    (rsp : a[4].get 64 = sp + 280) (src : a[6].get 64 = sp + 752)
    (scalar : a[2].get 64 = sp + 288) (dst : a[7].get 64 = sp + 376)
    (stack : Writable Extracted.programImage m (sp - 8) 336)
    (coords : Readable m (sp + 752) 80)
    (room : 8 ≤ sp.toNat) (high : sp.toNat + 832 ≤ 2^32)
    (ret : memLoad m (sp + 280) 64 = 0x10ee37) (df : a[22] = ⟨1,0⟩) :
    ∃ (b : Registers) (n : Ram),
      program.runBlock (dialect Extracted.programImage) ⟨.l10e4c0, a, m⟩ =
        .call ⟨.l114930, b, n⟩ (productNormalizeReturn .l10ecb2 0x10ecb2) ∧
      (∀ x y : Limbs, WordsAt n (sp + 152) 64 x → WordsAt n (sp + 192) 64 y →
        ProductNormalizeInput sp b n x y) ∧
      ProductSlots sp n (a[3].get 64) (a[12].get 64) (a[14].get 64) (a[15].get 64) ∧
      (∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → b[j] = a[j]) ∧
      RamWriteFrame m n [⟨(sp - 8).toNat, 288⟩] := by
  have start : (sp - 8).toNat = sp.toNat - 8 := BitVec.toNat_sub_of_le room
  lifted_registers [rsp, src, scalar, dst]
  refine Exists.intro ?regs (Exists.intro ?memory (And.intro ?run ?post))
  case run =>
    generate_block [rsp, src, scalar, dst]
    coordinate_guards
    rfl
  case post =>
    abstract_product_scratch
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y hx hy
      constructor
      case rsp | src => rfl
      case dst | base => apply congrArg (Value.mk 64); lifted_word_reads [] <;> rfl
      case df => exact df
      case saved => apply productRegisterWidths <;> exact wordWidth _
      case slot => lifted_word_reads [] <;> rfl
      case xAt => exact hx
      case yAt => exact hy
    · constructor <;> lifted_word_reads [ret] <;> rfl
    · exact productControlRegisters rfl rfl rfl rfl
    · have low : (sp - 8).toNat + 288 ≤ 2^32 := by omega
      coordinate_frame low


theorem coordinateProductBlock {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (h : ProductInput fr a m x y z) :
    let sp := fr.rsp - 520
    ∃ (b : Registers) (m' : Ram) (xl yl w : Limbs),
      program.runBlock (dialect Extracted.programImage) ⟨.l10e4c0, a, m⟩ =
        .call ⟨.l114930, b, m'⟩ (productNormalizeReturn .l10ecb2 0x10ecb2) ∧
      ProductNormalizeInput sp b m' (mulWords xl w) (mulWords yl w) ∧
      ProductSlots sp m' fr.rdi (sp + 376) fr.rsi 1 ∧
      (∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → b[j] = a[j]) ∧
      RamWriteFrame m m' [⟨(sp - 8).toNat, 288⟩] ∧
      FieldRepr xl x 8 ∧ FieldRepr yl y 8 ∧ FieldRepr w (inverse z) 8 := by
  let sp := fr.rsp - (520 : Word)
  have lower := h.parent.atoms
  obtain ⟨_, df, bx, r14, _, _, _, _, _, _, _, _, _, _, _, _, win, room, _, _⟩ := lower
  simp (disch := decide) only [Atom.Holds, Fin.getElem_fin, Vector.getElem_set_ne] at df bx r14
  change Writable Extracted.programImage m (fr.rsp - 976) 976 at win
  change fr.low.toNat + 976 ≤ fr.rsp.toNat at room
  have low (k : Word) (hk : k.toNat ≤ 976) : (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have spNat : sp.toNat = fr.rsp.toNat - 520 := low 520 (by decide)
  have high := h.parent.high
  have src : fr.rsi = sp + 752 := by rw [h.parent.srcAddr]; dsimp only [sp]; bv_omega
  have alignOff (k : Word) : fr.rsp - k = sp + (520 - k) := by dsimp only [sp]; bv_omega
  have win' : Writable Extracted.programImage m (sp - 8) 336 := by
    rw [show sp - 8 = fr.rsp - 528 by dsimp only [sp]; bv_omega]
    exact win.sub (by rw [low 976 (by decide), low 528 (by decide)]; simp only [BitVec.reduceToNat]; omega)
      (by rw [low 976 (by decide), low 528 (by decide)]; simp only [BitVec.reduceToNat]; omega)
  obtain ⟨xl, yl, _, hx, hy, _, rx, ry, _⟩ := h.coords.repr
  obtain ⟨w, hw, rw'⟩ := h.operand
  have coords := h.parent.source
  rw [src] at hx hy coords
  rw [show sp + 752 + 40 = sp + 792 by bv_omega] at hy
  rw [alignOff 232] at hw
  have num := h.ret
  rw [alignOff 240] at num
  have get {r : Nat} {hr : r < Reg.count} {v : Word} (eq : a[r]'hr = ⟨64,v⟩) : (a[r]'hr).get 64 = v :=
    congrArg (Value.get 64) eq
  have rsp := (get h.sp).trans (alignOff 240)
  have fromSrc := (get h.src).trans src
  have scalar := (get h.scalar).trans (alignOff 232)
  have dst := (get h.dst).trans (alignOff 144)
  have readable : Readable m (sp + 752) 80 := coords.sub (Nat.le_refl _) (by omega)
  have room' : 8 ≤ sp.toNat := by omega
  have high' : sp.toNat + 832 ≤ 2^32 := by omega
  obtain ⟨b, n, run, norm, slots, keep, frame⟩ := productBlockCall (a := a) (sp := sp)
    rsp fromSrc scalar dst win' readable room' high' num df
  obtain ⟨xAt,yAt⟩ := productOutputWords rsp fromSrc scalar dst win' readable room' high' hx hy hw run
  change a[3] = ⟨64,fr.rdi⟩ at bx
  change a[14] = ⟨64,fr.rsi⟩ at r14
  rw [get bx, get h.address, get r14, get h.choice, alignOff 144] at slots
  exact ⟨b, n, xl, yl, w, run, norm _ _ xAt yAt, slots, keep, frame, rx, ry, rw'⟩

end K256.Proofs.Generate.Generator.Affine
