import K256.Proofs.ParseSignature.Pair.Preparation.Atoms
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.ParseSignature.Pair

open K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

theorem secondScalarEntry {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (active : Active code fr true args mem)
    (hr : Readable fr.original fr.rsi 64) (hin : Outside [callStack fr] fr.rsi 64)
    (limbs : scalarLimbsAt mem (sp fr + 16) fr.original fr.rsi) :
    ∃ regs after, program.runBlock (dialect code) ⟨.l103b12, args, mem⟩ =
      .call ⟨.l107730, regs, after⟩ (resumeAt .l103b75 0x103b75) ∧
      ScalarEntry code fr 0x103b75 (fr.rsi + 32) regs after ∧
      scalarLimbsAt after (sp fr + 104) fr.original fr.rsi := by
  have atoms := active.atoms
  change Atom.All code args mem (callerLayout fr) at atoms
  simp only [callerLayout, Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨hsp, hdf, hbx, hbp, h12, h13, h14, h15, hmxcsr, hftw, hfcw,
    hsave₁, hsave₂, rest⟩ := atoms
  have tail : Atom.All code args mem ((callerLayout fr).drop 13) := rest
  obtain ⟨_, _, _, hw, room, _⟩ := rest
  change Writable code mem (fr.rsp - 560) 560 at hw
  change fr.low.toNat + 560 ≤ fr.rsp.toNat at room
  have rsp : Value.get 64 args[4] = sp fr := congrArg (Value.get 64) hsp
  have r14 : Value.get 64 args[14] = fr.rsi := congrArg (Value.get 64) h14
  have stackPlus (off : Nat) (h : off ≤ 184) :
      sp fr + BitVec.ofNat 64 off = fr.rsp - BitVec.ofNat 64 (184 - off) := by
    have hv := congrArg (BitVec.ofNat 64) (show 184 - off + off = 184 by omega)
    rw [BitVec.ofNat_add] at hv
    change BitVec.ofNat 64 (184 - off) + BitVec.ofNat 64 off = 184 at hv
    change fr.rsp - 184 + BitVec.ofNat 64 off = _
    bv_omega
  have address (off i : Nat) (hi : 8 * i + off ≤ 184) :
      wordAddr (sp fr + BitVec.ofNat 64 off) 64 i =
        fr.rsp - BitVec.ofNat 64 (184 - (off + 8 * i)) := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact stackPlus _ (by omega)
  have limb (i : Nat) (hi : i < 4) :
      memLoad mem (fr.rsp - BitVec.ofNat 64 (184 - (16 + 8 * i))) 64 =
        scalarWord fr.original fr.rsi i := by
    rw [← address 16 i (by omega)]
    exact limbs i hi
  let w := scalarWord fr.original fr.rsi
  let m1 := memStore mem (fr.rsp - 64) (w 2)
  let m2 := memStore m1 (fr.rsp - 56) (w 3)
  let m3 := memStore m2 (fr.rsp - 80) (w 0)
  let backup := memStore m3 (fr.rsp - 72) (w 1)
  let src := fr.rsi + 32
  let m5 := memStore backup (fr.rsp - 88) (memLoad fr.original (src + 24) 64)
  let m6 := memStore m5 (fr.rsp - 96) (memLoad fr.original (src + 16) 64)
  let m7 := memStore m6 (fr.rsp - 104) (memLoad fr.original (src + 8) 64)
  let m8 := memStore m7 (fr.rsp - 112) (memLoad fr.original (fr.rsi + 32) 64)
  let after := putScalar fr backup (fr.rsi + 32) 0x103b75
  have within := topWritesWithin room
  have t0 : RamWriteFrame mem mem (topWrites fr) := .refl _ _
  have t1 : RamWriteFrame mem m1 (topWrites fr) := topWordFrame room t0 64 _ (by decide) (by decide)
  have t2 : RamWriteFrame mem m2 (topWrites fr) := topWordFrame room t1 56 _ (by decide) (by decide)
  have t3 : RamWriteFrame mem m3 (topWrites fr) := topWordFrame room t2 80 _ (by decide) (by decide)
  have t4 : RamWriteFrame mem backup (topWrites fr) := topWordFrame room t3 72 _ (by decide) (by decide)
  have t5 : RamWriteFrame mem m5 (topWrites fr) := topWordFrame room t4 88 _ (by decide) (by decide)
  have t6 : RamWriteFrame mem m6 (topWrites fr) := topWordFrame room t5 96 _ (by decide) (by decide)
  have t7 : RamWriteFrame mem m7 (topWrites fr) := topWordFrame room t6 104 _ (by decide) (by decide)
  have t8 : RamWriteFrame mem m8 (topWrites fr) := topWordFrame room t7 112 _ (by decide) (by decide)
  have t9 : RamWriteFrame mem after (topWrites fr) := putScalar_top room t4 _ _
  have guard {m : Ram} (hf : RamWriteFrame mem m (topWrites fr))
      (off pc len : Nat) (ho : off ≤ 560) (hb : 8 ≤ off) (hi : pc + len ≤ bytes_l103b12.length) :
      StoreOk code m (fr.rsp - BitVec.ofNat 64 off) 8 (0x103b12 + BitVec.ofNat 64 pc) len :=
    storeOk_of_codeRange (stackWordWritable (hw.of_frame hf) off ho hb)
      (fun x hx => hcode x (code_l103b12 x hx)) hi
  have stackRead {m : Ram} (hf : RamWriteFrame mem m (topWrites fr))
      (off : Nat) (ho : off ≤ 560) (hb : 8 ≤ off) :
      LoadOk m (fr.rsp - BitVec.ofNat 64 off) 8 :=
    LoadOk.of_region (stackWordWritable (hw.of_frame hf) off ho hb).readable (Nat.le_refl _) (Nat.le_refl _)
  have l0 : LoadOk mem (fr.rsp - 168) 8 := stackRead t0 168 (by decide) (by decide)
  have l1 : LoadOk mem (fr.rsp - 160) 8 := stackRead t0 160 (by decide) (by decide)
  have l2 : LoadOk mem (fr.rsp - 152) 8 := stackRead t0 152 (by decide) (by decide)
  have l3 : LoadOk m1 (fr.rsp - 144) 8 := stackRead t1 144 (by decide) (by decide)
  have v0 := limb 0 (by decide)
  have v1 := limb 1 (by decide)
  have v2 := limb 2 (by decide)
  have v3 : memLoad m1 (fr.rsp - 144) 64 = w 3 :=
    (stackWordKeep fr mem 64 144 (w 2) (by decide) (by decide) (by decide)).trans (limb 3 (by decide))
  change memLoad mem (fr.rsp - 168) 64 = w 0 at v0
  change memLoad mem (fr.rsp - 160) 64 = w 1 at v1
  change memLoad mem (fr.rsp - 152) 64 = w 2 at v2
  obtain ⟨l56, v56⟩ : LoadOk backup (fr.rsi + 56) 8 ∧
      memLoad backup (fr.rsi + 56) 64 = memLoad fr.original (fr.rsi + 56) 64 :=
    inputWord room hr hin (active.writes.trans t4 within) 56 (by decide)
  obtain ⟨l48, v48⟩ : LoadOk m5 (fr.rsi + 48) 8 ∧
      memLoad m5 (fr.rsi + 48) 64 = memLoad fr.original (fr.rsi + 48) 64 :=
    inputWord room hr hin (active.writes.trans t5 within) 48 (by decide)
  obtain ⟨l32, v32⟩ : LoadOk m6 (fr.rsi + 32) 8 ∧
      memLoad m6 (fr.rsi + 32) 64 = memLoad fr.original (fr.rsi + 32) 64 :=
    inputWord room hr hin (active.writes.trans t6 within) 32 (by decide)
  obtain ⟨l40, v40⟩ : LoadOk m6 (fr.rsi + 40) 8 ∧
      memLoad m6 (fr.rsi + 40) 64 = memLoad fr.original (fr.rsi + 40) 64 :=
    inputWord room hr hin (active.writes.trans t6 within) 40 (by decide)
  have g1 : StoreOk code mem (fr.rsp - 64) 8 0x103b21 5 :=
    guard t0 64 15 5 (by decide) (by decide) (by decide)
  have g2 : StoreOk code m1 (fr.rsp - 56) 8 0x103b2b 8 :=
    guard t1 56 25 8 (by decide) (by decide) (by decide)
  have g3 : StoreOk code m2 (fr.rsp - 80) 8 0x103b33 5 :=
    guard t2 80 33 5 (by decide) (by decide) (by decide)
  have g4 : StoreOk code m3 (fr.rsp - 72) 8 0x103b38 5 :=
    guard t3 72 38 5 (by decide) (by decide) (by decide)
  have g5 : StoreOk code backup (fr.rsp - 88) 8 0x103b41 5 :=
    guard t4 88 47 5 (by decide) (by decide) (by decide)
  have g6 : StoreOk code m5 (fr.rsp - 96) 8 0x103b4a 5 :=
    guard t5 96 56 5 (by decide) (by decide) (by decide)
  have g7 : StoreOk code m6 (fr.rsp - 104) 8 0x103b57 5 :=
    guard t6 104 69 5 (by decide) (by decide) (by decide)
  have g8 : StoreOk code m7 (fr.rsp - 112) 8 0x103b5c 5 :=
    guard t7 112 74 5 (by decide) (by decide) (by decide)
  have g9 : StoreOk code m8 (fr.rsp - 192) 8 0x103b70 5 :=
    guard t8 192 94 5 (by decide) (by decide) (by decide)
  have push : sp fr - 8 = fr.rsp - 192 := by change fr.rsp - 184 - 8 = _; bv_omega
  have a16 : sp fr + 16 = fr.rsp - 168 := stackPlus 16 (by decide)
  have a24 : sp fr + 24 = fr.rsp - 160 := stackPlus 24 (by decide)
  have a32 : sp fr + 32 = fr.rsp - 152 := stackPlus 32 (by decide)
  have a40 : sp fr + 40 = fr.rsp - 144 := stackPlus 40 (by decide)
  have a120 : sp fr + 120 = fr.rsp - 64 := stackPlus 120 (by decide)
  have a128 : sp fr + 128 = fr.rsp - 56 := stackPlus 128 (by decide)
  have a104 : sp fr + 104 = fr.rsp - 80 := stackPlus 104 (by decide)
  have a112 : sp fr + 112 = fr.rsp - 72 := stackPlus 112 (by decide)
  have a96 : sp fr + 96 = fr.rsp - 88 := stackPlus 96 (by decide)
  have a88 : sp fr + 88 = fr.rsp - 96 := stackPlus 88 (by decide)
  have a80 : sp fr + 80 = fr.rsp - 104 := stackPlus 80 (by decide)
  have a72 : sp fr + 72 = fr.rsp - 112 := stackPlus 72 (by decide)
  have src56 : fr.rsi + 56 = src + 24 := by dsimp only [src]; bv_omega
  have src48 : fr.rsi + 48 = src + 16 := by dsimp only [src]; bv_omega
  have src40 : fr.rsi + 40 = src + 8 := by dsimp only [src]; bv_omega
  let regs : Values Value Reg.count :=
    let regs := args.set 0 ⟨64, memLoad fr.original src 64⟩
    let regs := regs.set 1 ⟨64, memLoad fr.original (src + 8) 64⟩
    let regs := regs.set 2 ⟨64, 32⟩
    let regs := regs.set 4 ⟨64, fr.rsp - 192⟩
    let regs := regs.set 6 ⟨64, fr.rsp - 112⟩
    regs.set 7 ⟨64, sp fr + 8⟩
  refine ⟨regs, after, ?block, ?entry, ?backup⟩
  case block =>
    cfg_eval
    dsimp only [m1, m2, m3, backup, m5, m6, m7, m8] at l3 l56 v56 l48 v48 l32 v32 l40 v40
    dsimp only [m1, m2, m3, backup, m5, m6, m7, m8] at v3 g1 g2 g3 g4 g5 g6 g7 g8 g9
    rw [src56] at l56 v56
    rw [src48] at l48 v48
    rw [src40] at l40 v40
    simp only [rsp, r14, push, a16, a24, a32, a40, a120, a128, a104, a112, a96, a88, a80, a72,
      l0, l1, l2, l3, v0, v1, v2, v3, g1, g2, g3, g4, g5, g6, g7, g8, g9,
      src56, src48, src40, l56, v56, l48, v48, l32, v32, l40, v40, ↓reduceIte]
    congr 2
    apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
      fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
    intro i
    finite_cases i <;> simp only [regs, Vector.getElem_set] <;> rfl
  case entry =>
    have keepSaved (off : Nat) (hi : off ≤ 48) :
        memLoad after (fr.rsp - BitVec.ofNat 64 off) 64 =
          memLoad mem (fr.rsp - BitVec.ofNat 64 off) 64 := by
      change memLoad (putScalar fr backup src 0x103b75) _ 64 = _
      rw [putScalar_keep fr backup src 0x103b75 off (by omega) (by omega) (by omega)]
      simp (disch := omega) only [backup, m3, m2, m1, BitVec.ofNat_eq_ofNat, stackWordKeep fr]
    have s₁ := (keepSaved 16 (by decide)).trans hsave₁
    have s₂ := (keepSaved 8 (by decide)).trans hsave₂
    apply scalarEntry_of_copy src 0x103b75 room (active.writes.trans t4 within)
    · refine callerAtoms tail ?_ s₁ s₂ t9
      simp only [callerLayout, Fn103ac0.frameAt, Fn103ac0.frameAtG0, List.take_succ_cons,
        List.take_zero, Atom.All, Atom.Holds, regs, Fin.getElem_fin, Vector.getElem_set]
      exact ⟨rfl, hdf, hbx, hbp, h12, h13, h14, h15, hmxcsr, hftw, hfcw, trivial⟩
    · intro i hi
      obtain ⟨i, bound⟩ := i
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [regs, Fin.getElem_fin, Vector.getElem_set, ↓reduceIte] <;>
        first | rfl | exact active.widths 8 (by decide) | exact active.widths 9 (by decide)
    · simp only [regs, Vector.getElem_set, ↓reduceIte]
      rfl
    · simp only [regs, Vector.getElem_set, ↓reduceIte]
    · simp only [regs, Vector.getElem_set, ↓reduceIte, a72]
      rfl
    · simp only [regs, Vector.getElem_set, ↓reduceIte]
      rfl
    · decide
  case backup =>
    intro i hi
    change memLoad after (wordAddr (sp fr + BitVec.ofNat 64 104) 64 i) 64 = _
    rw [address 104 i (by omega), putScalar_keep fr backup _ _ _ (by omega) (by omega) (by omega)]
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have same (m : Ram) (a v : BitVec 64) : memLoad (memStore m a v) a 64 = v :=
      memLoad_memStore_same m a v (by decide) (by decide)
    rcases hi' with rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [backup, m3, m2, m1, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
        BitVec.ofNat_eq_ofNat, stackWordKeep fr, same, w]

end K256.Proofs.ParseSignature.Pair
