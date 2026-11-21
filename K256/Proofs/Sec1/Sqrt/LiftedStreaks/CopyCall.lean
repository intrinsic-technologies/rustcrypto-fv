import K256.Proofs.Sec1.Sqrt.LiftedStreaks.Square
import K256.Proofs.Sec1.Tactic
import K256.Proofs.Sec1.LIR.Generated.Values

set_option autoImplicit false

namespace K256.Proofs.Sec1.Sqrt.LiftedCopy

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open CFG Lift Refine Common.Field LIR

@[cfg_block] def block (pc : BitVec 64) (target : Label) (dst : Fin Reg.count) :
    Block Op Label signature Reg.count Reg.count :=
  .letOp (n := 53) (.out pc (movR64M64Effect pc 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec pc (LoadPre pc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (pc + BitVec.ofNat 64 5)) 8) (movR64M64Effect pc 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec (pc + 5#64) (StorePre (pc + 5#64) 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s ((pc + 5#64) + BitVec.ofNat 64 5)) 8) (movM64R64Effect (pc + 5#64) 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out (pc + 10#64) (movR64M64Effect (pc + 10#64) 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec (pc + 10#64) (LoadPre (pc + 10#64) (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s ((pc + 10#64) + BitVec.ofNat 64 5)) 8) (movR64M64Effect (pc + 10#64) 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec (pc + 15#64) (StorePre (pc + 15#64) 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s ((pc + 15#64) + BitVec.ofNat 64 5)) 8) (movM64R64Effect (pc + 15#64) 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out (pc + 20#64) (movR64M64Effect (pc + 20#64) 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec (pc + 20#64) (LoadPre (pc + 20#64) (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s ((pc + 20#64) + BitVec.ofNat 64 5)) 8) (movR64M64Effect (pc + 20#64) 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec (pc + 25#64) (StorePre (pc + 25#64) 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s ((pc + 25#64) + BitVec.ofNat 64 5)) 8) (movM64R64Effect (pc + 25#64) 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out (pc + 30#64) (movR64M64Effect (pc + 30#64) 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec (pc + 30#64) (LoadPre (pc + 30#64) (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s ((pc + 30#64) + BitVec.ofNat 64 5)) 8) (movR64M64Effect (pc + 30#64) 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out (pc + 35#64) (movR64M64Effect (pc + 35#64) 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec (pc + 35#64) (LoadPre (pc + 35#64) (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s ((pc + 35#64) + BitVec.ofNat 64 5)) 8) (movR64M64Effect (pc + 35#64) 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec (pc + 40#64) (StorePre (pc + 40#64) 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s ((pc + 40#64) + BitVec.ofNat 64 5)) 8) (movM64R64Effect (pc + 40#64) 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec (pc + 45#64) (StorePre (pc + 45#64) 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s ((pc + 45#64) + BitVec.ofNat 64 4)) 8) (movM64R64Effect (pc + 45#64) 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out (pc + 49#64) (movR64R64Effect (pc + 49#64) 7 (BitVec.ofNat 5 dst.val)) (EffectPart.reads (.reg (.gpr 7)) [.gpr (BitVec.ofNat 5 dst.val)] []) (.reg (.gpr 7))) #v[⟨dst.val, by have h : dst.val < 53 := dst.isLt; omega⟩]
    (.letOp (n := 69) (.exec (pc + 49#64) (fun s => s.RIP = (pc + 49#64)) (movR64R64Effect (pc + 49#64) 7 (BitVec.ofNat 5 dst.val)) (Reg.operands [.gpr (BitVec.ofNat 5 dst.val)] [])) #v[⟨dst.val, by have h : dst.val < 53 := dst.isLt; omega⟩]
    (.letOp (n := 70) (.out (pc + 52#64) (movR64R64Effect (pc + 52#64) 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec (pc + 52#64) (fun s => s.RIP = (pc + 52#64)) (movR64R64Effect (pc + 52#64) 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out (pc + 55#64) (callEffect (fun _ => 0x1145f0) (pc + 60#64)) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec (pc + 55#64) (PushPre (pc + 55#64) 5) (callEffect (fun _ => 0x1145f0) (pc + 60#64)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, (pc + 60#64)⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := target, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

private def copyProgram (pc : BitVec 64) (target : Label) (dst : Fin Reg.count) :
    Program Op Label signature Reg.count :=
  ⟨fun _ => block pc target dst⟩

def copyWordsMemory (m : Ram) (base : Word) (w : Limbs) : Ram :=
  memStore (memStore (memStore (memStore (memStore m (base + 32#64) w[4])
    (base + 24#64) w[3]) (base + 16#64) w[2]) (base + 8#64) w[1]) (base + 0#64) w[0]

def argsAfterCopy (a : Values Value Reg.count) (base : Word) (w : Limbs) : Values Value Reg.count :=
  let a := a.set 0 ⟨64, w[0]⟩
  let a := a.set 1 ⟨64, w[1]⟩
  let a := a.set 4 ⟨64, base - 8⟩
  let a := a.set 6 ⟨64, base⟩
  a.set 7 ⟨64, base + 40⟩

def copyFrame (target : Label) (ret : Word) : LIR.lifted.StackFrame :=
  ⟨target, #v[], rfl, some ⟨64, ret⟩⟩

private theorem toNat_add_word {base : Word} {off : Nat}
    (h : base.toNat + off < 2^64) : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
    Nat.mod_eq_of_lt h]

private theorem workspaceBounds {code : CodeMap} {m : Ram} {base : Word}
    (h : Writable code m (base - 112) 192) (hr : 112 ≤ base.toNat) :
    (base - 112).toNat = base.toNat - 112 ∧ base.toNat + 80 ≤ 2^32 := by
  have hlow : (base - 112).toNat = base.toNat - 112 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hr)
  have hw := h.readable.low
  rw [hlow] at hw
  exact ⟨hlow, by omega⟩

private theorem readableAt {code : CodeMap} {m : Ram} {base : Word} (off : Nat)
    (hw : Writable code m (base - 112) 192) (hroom : 112 ≤ base.toNat) (ho : off + 8 ≤ 80) :
    LoadOk m (base + BitVec.ofNat 64 off) 8 := by
  have hb := workspaceBounds hw hroom
  have he := toNat_add_word (base := base) (off := off) (by omega)
  have h := hw.readable.sub (a := base + BitVec.ofNat 64 off) (n := 8)
    (by rw [he, hb.1]; omega) (by rw [he, hb.1]; omega)
  exact ⟨h.low, h.present⟩

private theorem storeAt {code : CodeMap} {m : Ram} {base pc addr : Word}
    (off len : Nat) (hw : Writable code m (base - 112) 192) (hroom : 112 ≤ base.toNat)
    (haddr : base.toNat - 112 ≤ addr.toNat ∧ addr.toNat + 8 ≤ base.toNat + 80)
    (hpc : pc.toNat + 60 ≤ 2^32) (hlen : off + len ≤ 60)
    (hap : base.toNat + 80 ≤ pc.toNat ∨ pc.toNat + 60 ≤ base.toNat - 112) :
    StoreOk code m addr 8 (pc + BitVec.ofNat 64 off) len := by
  have hb := workspaceBounds hw hroom
  have he := toNat_add_word (base := pc) (off := off) (by omega)
  have w := hw.sub (a := addr) (n := 8) (by rw [hb.1]; omega) (by rw [hb.1]; omega)
  refine ⟨w.readable.low, w.readable.present, w.tables, ?_, w.notCode⟩
  have hlo : addr.toNat + 8 ≤ 2^32 := w.readable.low
  apply RangeApart.of_toNat
  · exact Nat.le_trans hlo (by decide)
  · rw [he]
    omega
  · rw [he]
    omega

private theorem readsAfterStore (m : Ram) (base : Word) (v : Word) (dst src : Nat)
    (hs : 40 ≤ src) (hd : dst + 8 ≤ 40) (hu : src + 8 ≤ 80) (hb : base.toNat + 80 ≤ 2^32) :
    memLoad (memStore m (base + BitVec.ofNat 64 dst) v) (base + BitVec.ofNat 64 src) 64 =
      memLoad m (base + BitVec.ofNat 64 src) 64 := by
  apply memLoad_memStore_of_rangeApart
  have e := toNat_add_word (base := base) (off := dst) (by omega)
  have e' := toNat_add_word (base := base) (off := src) (by omega)
  apply RangeApart.of_toNat <;> simp only [e, e'] <;> omega

open Lean Meta in
dsimproc_decl reduceCopyFin (Fin.val _) := fun e => do
  let_expr Fin.val _ i ← e | return .continue
  let some k ← CFG.Eval.indexValue? i | return .continue
  return .done (mkNatLit k)

private theorem get64_word (v : Word) : (⟨64, v⟩ : Value).get 64 = v := by
  simp only [Value.get, BitVec.setWidth_eq]

set_option maxHeartbeats 4000000 in
theorem runCopyCall {code : CodeMap} {caller target : Label} {pc base : Word}
    {args : Values Value Reg.count} {m : Ram} {w : Limbs} (useRbp : Bool)
    (hs : args[4].get 64 = base) (hin : args[14].get 64 = base)
    (hout : (args[if useRbp then 5 else 3]'(by cases useRbp <;> decide)).get 64 = base + 40)
    (hw : Writable code m (base - 112) 192) (hr : 112 ≤ base.toNat)
    (hp : pc.toNat + 60 ≤ 2^32)
    (ha : base.toNat + 80 ≤ pc.toNat ∨ pc.toNat + 60 ≤ base.toNat - 112)
    (hWords : WordsAt m (base + 40) 64 w) :
    (copyProgram pc target (if useRbp then 5 else 3)).runBlock (Lift.dialect code)
        ⟨caller, args, m⟩ =
      .call ⟨.l1145f0, argsAfterCopy args base w,
          memStore (copyWordsMemory m base w) (base - 8) (pc + 60#64)⟩
        (copyFrame target (pc + 60#64)) := by
  have hb := workspaceBounds hw hr
  have h8 : (base - 8).toNat = base.toNat - 8 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 8 ≤ _; omega)
  let m4 := memStore m (base + 32) w[4]
  have ww4 : Writable code m4 (base - 112) 192 := hw.memStore (base + 32) w[4]
  let m3 := memStore m4 (base + 24) w[3]
  have ww3 : Writable code m3 (base - 112) 192 := ww4.memStore (base + 24) w[3]
  let m2 := memStore m3 (base + 16) w[2]
  have ww2 : Writable code m2 (base - 112) 192 := ww3.memStore (base + 16) w[2]
  let m1 := memStore m2 (base + 8) w[1]
  have ww1 : Writable code m1 (base - 112) 192 := ww2.memStore (base + 8) w[1]
  let m0 := memStore m1 base w[0]
  have ww0 : Writable code m0 (base - 112) 192 := ww1.memStore base w[0]
  have st4 : StoreOk code m (base + 32) 8 (pc + 5) 5 :=
    storeAt 5 5 hw hr (by
      rw [show (base + 32).toNat = base.toNat + 32 from
        toNat_add_word (off := 32) (by omega)]
      omega) hp (by decide) ha
  have st3 : StoreOk code m4 (base + 24) 8 (pc + 15) 5 :=
    storeAt 15 5 ww4 hr (by
      rw [show (base + 24).toNat = base.toNat + 24 from
        toNat_add_word (off := 24) (by omega)]
      omega) hp (by decide) ha
  have st2 : StoreOk code m3 (base + 16) 8 (pc + 25) 5 :=
    storeAt 25 5 ww3 hr (by
      rw [show (base + 16).toNat = base.toNat + 16 from
        toNat_add_word (off := 16) (by omega)]
      omega) hp (by decide) ha
  have st1 : StoreOk code m2 (base + 8) 8 (pc + 40) 5 :=
    storeAt 40 5 ww2 hr (by
      rw [show (base + 8).toNat = base.toNat + 8 from
        toNat_add_word (off := 8) (by omega)]
      omega) hp (by decide) ha
  have st0 : StoreOk code m1 base 8 (pc + 45) 4 :=
    storeAt 45 4 ww1 hr (by omega) hp (by decide) ha
  have rd4 : LoadOk m (base + 72) 8 := readableAt 72 hw hr (by decide)
  have val4 : memLoad m (base + 72) 64 = w[4] := by
    have v := hWords 4 (by decide)
    change memLoad m ((base + 40) + 32) 64 = w[4] at v
    rw [BitVec.add_assoc] at v
    exact v
  have rd3 : LoadOk m4 (base + 64) 8 := readableAt 64 ww4 hr (by decide)
  have val3 : memLoad m4 (base + 64) 64 = w[3] := by
    have v := hWords 3 (by decide)
    change memLoad m ((base + 40) + 24) 64 = w[3] at v
    rw [BitVec.add_assoc] at v
    rw [show memLoad m4 (base + 64) 64 = memLoad m (base + 64) 64 from
      readsAfterStore m base w[4] 32 64 (by decide) (by decide) (by decide) hb.2]
    exact v
  have rd2 : LoadOk m3 (base + 56) 8 := readableAt 56 ww3 hr (by decide)
  have val2 : memLoad m3 (base + 56) 64 = w[2] := by
    have v := hWords 2 (by decide)
    change memLoad m ((base + 40) + 16) 64 = w[2] at v
    rw [BitVec.add_assoc] at v
    rw [show memLoad m3 (base + 56) 64 = memLoad m4 (base + 56) 64 from
      readsAfterStore m4 base w[3] 24 56 (by decide) (by decide) (by decide) hb.2]
    rw [show memLoad m4 (base + 56) 64 = memLoad m (base + 56) 64 from
      readsAfterStore m base w[4] 32 56 (by decide) (by decide) (by decide) hb.2]
    exact v
  have rd1 : LoadOk m2 (base + 48) 8 := readableAt 48 ww2 hr (by decide)
  have val1 : memLoad m2 (base + 48) 64 = w[1] := by
    have v := hWords 1 (by decide)
    change memLoad m ((base + 40) + 8) 64 = w[1] at v
    rw [BitVec.add_assoc] at v
    rw [show memLoad m2 (base + 48) 64 = memLoad m3 (base + 48) 64 from
      readsAfterStore m3 base w[2] 16 48 (by decide) (by decide) (by decide) hb.2]
    rw [show memLoad m3 (base + 48) 64 = memLoad m4 (base + 48) 64 from
      readsAfterStore m4 base w[3] 24 48 (by decide) (by decide) (by decide) hb.2]
    rw [show memLoad m4 (base + 48) 64 = memLoad m (base + 48) 64 from
      readsAfterStore m base w[4] 32 48 (by decide) (by decide) (by decide) hb.2]
    exact v
  have rd0 : LoadOk m2 (base + 40) 8 := readableAt 40 ww2 hr (by decide)
  have val0 : memLoad m2 (base + 40) 64 = w[0] := by
    have v := hWords 0 (by decide)
    change memLoad m ((base + 40) + 0#64) 64 = w[0] at v
    rw [BitVec.add_zero] at v
    rw [show memLoad m2 (base + 40) 64 = memLoad m3 (base + 40) 64 from
      readsAfterStore m3 base w[2] 16 40 (by decide) (by decide) (by decide) hb.2]
    rw [show memLoad m3 (base + 40) 64 = memLoad m4 (base + 40) 64 from
      readsAfterStore m4 base w[3] 24 40 (by decide) (by decide) (by decide) hb.2]
    rw [show memLoad m4 (base + 40) 64 = memLoad m (base + 40) 64 from
      readsAfterStore m base w[4] 32 40 (by decide) (by decide) (by decide) hb.2]
    exact v
  have call : StoreOk code m0 (base - 8) 8 (pc + 55) 5 :=
    storeAt 55 5 ww0 hr (by rw [h8]; omega) hp (by decide) ha
  simp only [m4, m3, m2, m1, m0] at rd3 rd2 rd1 rd0 st3 st2 st1 st0 val3 val2 val1 val0 call
  cases useRbp <;> simp only [Bool.false_eq_true, ↓reduceIte] at hout ⊢
  all_goals
    cfg_eval [signature, Fin.getElem_fin, ↓ reduceCopyFin, Vector.getElem_push, Reg.count,
      Nat.reduceLT, Nat.reduceMod, get64_word,
      hs, hin, hout, rd4, rd3, rd2, rd1, rd0, st4, st3, st2, st1, st0,
      val4, val3, val2, val1, val0, call, BitVec.add_zero]
    simp only [get64_word, copyWordsMemory, BitVec.add_zero, copyFrame]
    rw [ite_eq_left rd0]
    dsimp only
    rw [ite_eq_left rd1]
    dsimp only
    rw [val1, ite_eq_left st1]
    dsimp only
    rw [ite_eq_left st0]
    dsimp only
    simp only [val0, call, ↓reduceIte]
    congr 2
    apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
      fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
    intro i
    finite_cases i <;> simp only [argsAfterCopy, Vector.getElem_set] <;> rfl


private theorem writtenWithin {base : Word} {off : Nat}
    (hroom : 112 ≤ base.toNat) (hb : base.toNat + 80 ≤ 2^32) (ho : off + 8 ≤ 80) :
    InRegions [roundStack base] (base + BitVec.ofNat 64 off) 8 := by
  have h112 : (base - 112).toNat = base.toNat - 112 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hroom)
  have haddr := toNat_add_word (base := base) (off := off) (by omega)
  refine ⟨roundStack base, List.mem_cons_self, ?_⟩
  simp only [InRegion, roundStack, h112, haddr]
  omega

private theorem pushedWithin {base : Word}
    (hroom : 112 ≤ base.toNat) (hb : base.toNat + 80 ≤ 2^32) :
    InRegions [roundStack base] (base - 8) 8 := by
  have h112 : (base - 112).toNat = base.toNat - 112 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hroom)
  have h8 : (base - 8).toNat = base.toNat - 8 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 8 ≤ _; omega)
  refine ⟨roundStack base, List.mem_cons_self, ?_⟩
  simp only [InRegion, roundStack, h112, h8]
  omega

private theorem readsOther {base : Word} (m : Ram) (v : Word) (dst src : Nat)
    (hd : dst + 8 ≤ 80) (hs : src + 8 ≤ 80)
    (ha : dst + 8 ≤ src ∨ src + 8 ≤ dst) (hb : base.toNat + 80 ≤ 2^32) :
    memLoad (memStore m (base + BitVec.ofNat 64 dst) v) (base + BitVec.ofNat 64 src) 64 =
      memLoad m (base + BitVec.ofNat 64 src) 64 := by
  apply memLoad_memStore_of_rangeApart
  have e := toNat_add_word (base := base) (off := dst) (by omega)
  have e' := toNat_add_word (base := base) (off := src) (by omega)
  apply RangeApart.of_toNat <;> simp only [e, e'] <;> omega

private theorem readsPushed {base : Word} (m : Ram) (ret : Word) (off : Nat)
    (ho : off + 8 ≤ 80) (hroom : 112 ≤ base.toNat) (hb : base.toNat + 80 ≤ 2^32) :
    memLoad (memStore m (base - 8) ret) (base + BitVec.ofNat 64 off) 64 =
      memLoad m (base + BitVec.ofNat 64 off) 64 := by
  apply memLoad_memStore_of_rangeApart
  have h8 : (base - 8).toNat = base.toNat - 8 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 8 ≤ _; omega)
  have e := toNat_add_word (base := base) (off := off) (by omega)
  apply RangeApart.of_toNat <;> simp only [h8, e] <;> omega

theorem preparedMemory {code : CodeMap} {m : Ram} {base : Word} {w : Limbs}
    (ret : Word) (hroom : 112 ≤ base.toNat) (hw : Writable code m (base - 112) 192) :
    let child := memStore (copyWordsMemory m base w) (base - 8) ret
    Writable code child (base - 112) 192 ∧ WordsAt child base 64 w ∧
      memLoad child (base - 8) 64 = ret ∧ RamWriteFrame m child [roundStack base] := by
  have hb := (workspaceBounds hw hroom).2
  have hframe : RamWriteFrame m
      (memStore (copyWordsMemory m base w) (base - 8) ret) [roundStack base] := by
    unfold copyWordsMemory
    apply RamWriteFrame.memStore _ ret (pushedWithin hroom hb)
    apply RamWriteFrame.memStore _ w[0] (writtenWithin (off := 0) hroom hb (by decide))
    apply RamWriteFrame.memStore _ w[1] (writtenWithin (off := 8) hroom hb (by decide))
    apply RamWriteFrame.memStore _ w[2] (writtenWithin (off := 16) hroom hb (by decide))
    apply RamWriteFrame.memStore _ w[3] (writtenWithin (off := 24) hroom hb (by decide))
    apply RamWriteFrame.memStore _ w[4] (writtenWithin (off := 32) hroom hb (by decide))
    exact RamWriteFrame.refl _ _
  refine ⟨hw.of_frame hframe, ?_, memLoad_memStore _ _ (by decide) (by decide) _, hframe⟩
  intro i hi
  change memLoad (memStore (copyWordsMemory m base w) (base - 8) ret)
    (base + BitVec.ofNat 64 (8 * i)) 64 = w[i]
  rw [readsPushed _ _ _ (by omega) hroom hb]
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases casesI with rfl | rfl | rfl | rfl | rfl
  · simp only [copyWordsMemory, Nat.reduceMul]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · simp only [copyWordsMemory, Nat.reduceMul]
    rw [readsOther (base := base) _ _ 0 8 (by decide) (by decide) (by decide) hb]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · simp only [copyWordsMemory, Nat.reduceMul]
    rw [readsOther (base := base) _ _ 0 16 (by decide) (by decide) (by decide) hb]
    rw [readsOther (base := base) _ _ 8 16 (by decide) (by decide) (by decide) hb]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · simp only [copyWordsMemory, Nat.reduceMul]
    rw [readsOther (base := base) _ _ 0 24 (by decide) (by decide) (by decide) hb]
    rw [readsOther (base := base) _ _ 8 24 (by decide) (by decide) (by decide) hb]
    rw [readsOther (base := base) _ _ 16 24 (by decide) (by decide) (by decide) hb]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · simp only [copyWordsMemory, Nat.reduceMul]
    rw [readsOther (base := base) _ _ 0 32 (by decide) (by decide) (by decide) hb]
    rw [readsOther (base := base) _ _ 8 32 (by decide) (by decide) (by decide) hb]
    rw [readsOther (base := base) _ _ 16 32 (by decide) (by decide) (by decide) hb]
    rw [readsOther (base := base) _ _ 24 32 (by decide) (by decide) (by decide) hb]
    exact memLoad_memStore _ _ (by decide) (by decide) _


theorem runFromLabel {code : CodeMap} {l : LIR.lifted.Location}
    {target : Label} {base : Word} {w : Limbs}
    {useRbp : Bool}
    (hBlock : program.blocks l.label =
      block (address l.label) target (if useRbp then 5 else 3))
    (hs : (l.arguments[4]'(by change 4 < Reg.count; decide)).get 64 = base)
    (hin : (l.arguments[14]'(by change 14 < Reg.count; decide)).get 64 = base)
    (hout : (l.arguments[if useRbp then 5 else 3]'(by
      change (if useRbp then 5 else 3) < Reg.count
      cases useRbp <;> decide)).get 64 = base + 40)
    (hw : Writable code l.store (base - 112) 192) (hr : 112 ≤ base.toNat)
    (hp : (address l.label).toNat + 60 ≤ 2^32)
    (ha : base.toNat + 80 ≤ (address l.label).toNat ∨
      (address l.label).toNat + 60 ≤ base.toNat - 112)
    (hWords : WordsAt l.store (base + 40) 64 w) :
    program.runBlock (Lift.dialect code) l =
      .call ⟨.l1145f0, argsAfterCopy l.arguments base w,
        memStore (copyWordsMemory l.store base w) (base - 8) (address l.label + 60#64)⟩
        (copyFrame target (address l.label + 60#64)) := by
  have he : program.runBlock (Lift.dialect code) l =
      (copyProgram (address l.label) target (if useRbp then 5 else 3)).runBlock (Lift.dialect code) l := by
    unfold Program.runBlock
    rw [hBlock]
    rfl
  rw [he]
  exact runCopyCall (caller := l.label) useRbp hs hin hout hw hr hp ha hWords

end K256.Proofs.Sec1.Sqrt.LiftedCopy
