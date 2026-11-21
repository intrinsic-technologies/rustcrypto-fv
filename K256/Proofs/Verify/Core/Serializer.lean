import K256.Proofs.Verify.Core.State
import K256.Proofs.Verify.LIR.Fn10a2f0.Frame
import K256.Proofs.Verify.Core.Serializer.PrefixWords
import K256.Proofs.Verify.Core.Serializer.Bytes
import K256.Proofs.Verify.LIR.HighByteStore

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR Serializer

theorem_by serializerBlock (code : CodeMap) (a : Registers) (m : Ram) :
    program.runBlock (dialect code) ⟨.l10a2f0, a, m⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

open Lean Elab Tactic in
local elab "serialize_stores" : tactic => do
  let identAt (stem : String) (n : Nat) := mkIdent (Name.mkSimple (stem ++ toString n))
  let stores := (List.range 32).toArray.map fun n => identAt "storeAfter" (n+1)
  evalTactic (← `(tactic| extract_lets $stores:ident*))
  let mut facts := #[]
  let mem := mkIdent `mem
  let di := mkIdent `di
  let si := mkIdent `si
  for j in [:32] do
    let next := Syntax.mkNumLit (toString (j+1))
    let step := identAt "written" (j+1)
    let st := stores[j]!
    let group := j / 8
    let loadAt := #[0, 6, 16, 24][group]!
    let mut rules : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
    for n in ([j, loadAt].eraseDups) do
      if n > 0 then
        let h := identAt "written" n
        rules := rules.push (← `(Lean.Parser.Tactic.simpLemma| $h:ident))
    let word := identAt "rd" group
    let byte := mkIdent (Name.str `K256.Proofs.Verify.Core.Serializer ("byte" ++ toString (j % 8)))
    rules := rules ++ #[← `(Lean.Parser.Tactic.simpLemma| $word:ident),
      ← `(Lean.Parser.Tactic.simpLemma| $byte:ident)]
    if j % 8 = 6 then
      let reg ← if j = 14 then `(Lean.Parser.Tactic.simpLemma| show byteRegGpr 6 = 2 from rfl)
        else `(Lean.Parser.Tactic.simpLemma| show byteRegGpr 5 = 1 from rfl)
      rules := rules ++ #[reg, ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceLT),
        ← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte), ← `(Lean.Parser.Tactic.simpLemma| eq_self),
        ← `(Lean.Parser.Tactic.simpLemma| Value.get_mk_setWidth),
        ← `(Lean.Parser.Tactic.simpLemma| BitVec.setWidth_eq)]
    let finish ← if j = 0 then `(tactic| exact $(mkIdent `wr0):ident)
      else `(tactic| rfl)
    evalTactic (← `(tactic| (
      have $step : $st = $mem $next := by
        simp only [$st:ident]
        rw [$di:ident, $si:ident]
        simp only [$rules,*]
        $finish:tactic
      clear_value $st:ident)))
    facts := facts.push (← `(Lean.Parser.Tactic.simpLemma| $step:ident))
  let ret := mkIdent `ret32
  let low := mkIdent `lowRet
  evalTactic (← `(tactic| (
    rw [$(mkIdent `sp):ident, $si:ident, $di:ident]
    simp only [$facts,*, $ret:ident, $low:ident, and_true])))

private def returnsWith {Value Store Label signature results}
    (post : Output Value Store results → Prop) (t : Transfer Value Store Label signature results) :=
  ∃ o, t = .returned o ∧ post o

private theorem guarded {Value Store Label signature results} {post : Output Value Store results → Prop}
    {c : Prop} [Decidable c] {x y : Transfer Value Store Label signature results}
    (h : c) (next : returnsWith post x) : returnsWith post (if c then x else y) := by
  rwa [ite_eq_left h]

open Lean Elab Tactic in
local elab "serializer_guards" : tactic => do
  let load := mkIdent `load
  let store := mkIdent `store
  evalTactic (← `(tactic| refine guarded $(mkIdent `firstLoad):ident (guarded $(mkIdent `firstStore):ident ?_)))
  for n in [1:32] do
    let i := Syntax.mkNumLit (toString n)
    if [6, 16, 24].contains n then
      let off := Syntax.mkNumLit (toString (if n = 6 then 8 else n))
      evalTactic (← `(tactic| refine guarded ($load $i $off (by decide) (by decide)) ?_))
    evalTactic (← `(tactic| refine guarded (c := _) ?_ ?_))
    evalTactic (← `(tactic| exact $store $i (by decide) (by decide +kernel)))
  evalTactic (← `(tactic| refine guarded $(mkIdent `lastLoad):ident ?_))

private theorem offset_toNat (b : BitVec 64) (i : Nat) (low : b.toNat + i < 2^64) :
    (b + BitVec.ofNat 64 i).toNat = b.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt low]

set_option maxHeartbeats 1200000 in
theorem serializeScalar {fr : Activation} {a : Registers} {m : Ram} {w : Vector (BitVec 64) 4}
    (frame : Atom.All Extracted.programImage a m (Fn10a2f0.frameAt .l10a2f0 fr))
    (src : Readable m fr.rsi 32) (dst : Writable Extracted.programImage m fr.rdi 32)
    (words : WordsAt m fr.rsi 64 w)
    (separate : fr.rdi.toNat + 32 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 32 ≤ fr.rdi.toNat)
    (ret : fr.rdi.toNat + 32 ≤ fr.rsp.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a2f0, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ out.values[0] = ⟨64, fr.rdi⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn10a2f0.doneAt fr) ∧
      RamWriteFrame m out.store [⟨fr.rdi.toNat, 32⟩] ∧ WordsAt out.store fr.rdi 64 w := by
  simp only [Fn10a2f0.frameAt, Fn10a2f0.frameAtG12, Atom.All, Atom.Holds] at frame
  obtain ⟨rsp, df, _, _, rbx, rbp, rsi, rdi, _, _, r12, r13, r14, r15, mx, ft, fc,
    readRet, valueRet, lowRet, _, _⟩ := frame
  let mem := prefixStore m fr.rdi w
  have low := dst.readable.low
  have sourceLow := src.low
  have frameN (n : Nat) (hn : n ≤ 32) : RamWriteFrame m (mem n) [⟨fr.rdi.toNat, 32⟩] :=
    prefix_frame (by omega) hn
  have word (n i : Nat) (hn : n ≤ 32) (hi : i < 4) :
      memLoad (mem n) (fr.rsi + BitVec.ofNat 64 (8*i)) 64 = w[i] := by
    rw [(frameN n hn).memLoad_eq]
    · exact words i hi
    have h := offset_toNat fr.rsi (8*i) (by omega)
    refine ⟨by rw [h]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change _ + 8 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 32 ≤ _
    rw [h]
    omega
  have rd0 : memLoad m fr.rsi 64 = w[0] := by
    exact (show memLoad m (fr.rsi + 0#64) 64 = _ from words 0 (by decide)) |> fun h => (congrArg (fun x => memLoad m x 64) (BitVec.add_zero fr.rsi)).symm.trans h
  have rd1 : memLoad (mem 6) (fr.rsi + 8) 64 = w[1] := word 6 1 (by decide) (by decide)
  have rd2 : memLoad (mem 16) (fr.rsi + 16) 64 = w[2] := word 16 2 (by decide) (by decide)
  have rd3 : memLoad (mem 24) (fr.rsi + 24) 64 = w[3] := word 24 3 (by decide) (by decide)
  have ret32 : memLoad (mem 32) fr.rsp 64 = fr.ret := by
    rw [(frameN 32 (by decide)).memLoad_eq, valueRet]
    refine ⟨by have := readRet.low; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact ret.symm
  have wr0 : memStore m fr.rdi (w[0].extractLsb' 0 8) = mem 1 := by
    change _ = memStore m (fr.rdi + 0) _
    exact congrArg (fun x => memStore m x (w[0].extractLsb' 0 8)) (BitVec.add_zero fr.rdi).symm
  have readable (n : Nat) (hn : n ≤ 32) := src.of_frame (frameN n hn)
  have writable (n : Nat) (hn : n ≤ 32) := dst.of_frame (frameN n hn)
  have load (n i : Nat) (hn : n ≤ 32) (hi : i + 8 ≤ 32) :
      LoadOk (mem n) (fr.rsi + BitVec.ofNat 64 i) 8 := by
    apply LoadOk.of_region (readable n hn)
    all_goals rw [offset_toNat _ _ (by omega)]; omega
  have store (n : Nat) (hn : n < 32) {pc : BitVec 64} {len : Nat}
      (inside : (pc - 0x10a2f0).toNat + len ≤ 278) :
      StoreOk Extracted.programImage (mem n) (fr.rdi + BitVec.ofNat 64 n) 1 pc len := by
    have dst' : Writable Extracted.programImage (mem n) (fr.rdi + BitVec.ofNat 64 n) 1 := by
      apply (writable n (by omega)).sub
      all_goals rw [offset_toNat _ _ (by omega)]; omega
    have h := ParseSignature.storeOk_of_codeRange dst'
      (fun x hx => Common.fnCode_subset_programImage x (code_l10a2f0 x hx))
      (show _ ≤ bytes_l10a2f0.length from (show bytes_l10a2f0.length = 278 by decide +kernel) ▸ inside)
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq,
      show (0x10a2f0 : BitVec 64) + (pc - 0x10a2f0) = pc by bv_omega] using h
  have firstLoad : LoadOk m fr.rsi 8 := LoadOk.of_region src (Nat.le_refl _) (by omega)
  have firstStore : StoreOk Extracted.programImage m fr.rdi 1 0x10a300 2 := by
    rw [← BitVec.add_zero fr.rdi]
    exact store 0 (by decide) (pc := 0x10a300) (len := 2) (by decide +kernel)
  have lastLoad : LoadOk (mem 32) fr.rsp 8 :=
    LoadOk.of_region (readRet.of_frame (frameN 32 (by decide))) (Nat.le_refl _) (Nat.le_refl _)
  have si : a[6].get 64 = fr.rsi := congrArg (Value.get 64) rsi
  have di : a[7].get 64 = fr.rdi := congrArg (Value.get 64) rdi
  have sp : a[4].get 64 = fr.rsp := congrArg (Value.get 64) rsp
  let post (out : Output Value Ram Reg.count) :=
    out.tag = some ⟨64, fr.ret⟩ ∧ out.values[0] = ⟨64, fr.rdi⟩ ∧
    Atom.All Extracted.programImage out.values out.store (Fn10a2f0.doneAt fr) ∧
    RamWriteFrame m out.store [⟨fr.rdi.toNat, 32⟩] ∧ WordsAt out.store fr.rdi 64 w
  suffices ok : returnsWith post (program.runBlock (dialect Extracted.programImage) ⟨.l10a2f0, a, m⟩) by
    obtain ⟨out, run, facts⟩ := ok
    exact ⟨out, .done (by unfold Program.step; rw [run]; rfl), facts⟩
  rw [serializerBlock]
  serialize_stores
  serializer_guards
  refine ⟨_, rfl, rfl, rfl, ?_, frameN 32 (by decide), prefix_words _ _ _ (by omega)⟩
  exact ⟨rfl, df, rbx, rbp, r12, r13, r14, r15, mx, ft, fc, trivial⟩

end K256.Proofs.Verify.Core
