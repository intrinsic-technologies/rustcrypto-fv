import K256.Proofs.Sec1.Affine.Compressed.Parity
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Sec1.Affine.Compressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR

open K256.Proofs.Common.Field

def normalizationInput (mem : Ram) (sp : Word) (s : Limbs) : Ram :=
  let m1 := memStore mem (sp + 264) s[0]
  let m2 := memStore m1 (sp + 272) s[1]
  let m3 := memStore m2 (sp + 280) s[2]
  let m4 := memStore m3 (sp + 288) s[3]
  let m5 := memStore m4 (sp + 296) s[4]
  memStore m5 (sp - 8) (0x120e9b : Word)

theorem normalizationInput_words (mem : Ram) (sp : Word) (s : Limbs) :
    WordsAt (normalizationInput mem sp s) (sp + 264) 64 s := by
  intro i hi
  have apart {o k : Word} (h : 8 ≤ (k - o).toNat ∧ 8 ≤ (o - k).toNat) :
      RangeApart (sp + o) 8 (sp + k) 8 := RangeApart.of_offsets rfl rfl h
  have stores (m : Ram) (o k : Word) (v : Word)
      (h : 8 ≤ (k - o).toNat ∧ 8 ≤ (o - k).toNat) :
      memLoad (memStore m (sp + o) v) (sp + k) 64 = memLoad m (sp + k) 64 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (apart h)
  have self (m : Ram) (o v : Word) :
      memLoad (memStore m (sp + o) v) (sp + o) 64 = v :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have idx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases idx with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [normalizationInput, wordAddr, BitVec.add_assoc, addr_sub sp 8]
    simp (disch := decide +kernel) only [stores, BitVec.reduceAdd, Nat.reduceDiv, Nat.reduceMul]
    exact self _ _ _

private theorem selectedLimb (a : Limbs) (want : BitVec 8) (i : Nat) (h : i < 5) :
    (a[i] ^^^ (negated a)[i]) &&& parityMask a[0] want ^^^ (negated a)[i] = (selectRoot a want)[i] := by
  simp only [selectRoot, Vector.getElem_ofFn, Fin.getElem_fin]

set_option maxHeartbeats 1200000 in
theorem normalizationCall (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (a : Limbs) (want : BitVec 8) (sp : Word)
    (hcode : ∀ x ∈ codeRange 0x120e17 bytes_l120e17, x ∈ code)
    (hsp : Value.get 64 args[4] = sp)
    (hm : -((Value.get 64 args[0]).setWidth 8).setWidth 64 = parityMask a[0] want)
    (h0 : Value.get 64 args[14] = a[0])
    (n0 : memLoad mem (sp + 96) 64 = (negated a)[0])
    (h1 : Value.get 64 args[15] = a[1])
    (n1 : memLoad mem (sp + 40) 64 = (negated a)[1])
    (h2 : Value.get 64 args[12] = a[2])
    (n2 : memLoad mem (sp + 8) 64 = (negated a)[2])
    (h3 : Value.get 64 args[13] = a[3])
    (n3 : Value.get 64 args[3] = (negated a)[3])
    (h4 : Value.get 64 args[5] = a[4])
    (n4 : memLoad mem (sp + 16) 64 = (negated a)[4])
    (hw : Writable code mem (sp - 8) 312) :
    ∃ callee, program.runBlock (dialect code) ⟨.l120e17, args, mem⟩ =
      .call ⟨.l114930, callee, normalizationInput mem sp (selectRoot a want)⟩
        ⟨.l120e9b, #v[], rfl, some ⟨64, 0x120e9b⟩⟩ ∧
      callee[4] = ⟨64, sp - 8⟩ ∧ callee[6] = ⟨64, sp + 264⟩ ∧ callee[7] = ⟨64, sp + 392⟩ ∧
      callee[22] = args[22] ∧ callee[39] = args[39] ∧ callee[50] = args[50] ∧ callee[51] = args[51] ∧ callee[3] = args[3] ∧
      ∀ i : Fin 53, i.val ∈ [5,12,13,14,15] → callee[i] = ⟨64,callee[i].get 64⟩ := by
  let sel := selectRoot a want
  have readAt (off : Word) (h : (off - (0 - 8)).toNat + 8 ≤ 312) : LoadOk mem (sp + off) 8 :=
    LoadOk.of_offsets hw.readable rfl (addr_sub sp 8) h
  have storeAt {m : Ram} (w : Writable code m (sp - 8) 312)
      (a' off : Word) (ha : a' = sp + off) (h : (off - (0 - 8)).toNat + 8 ≤ 312)
      (pc len : Nat) (hp : pc + len ≤ bytes_l120e17.length) :
      StoreOk code m a' 8 (0x120e17 + BitVec.ofNat 64 pc) len :=
    ParseSignature.storeOk_of_codeRange (w.of_offsets ha (addr_sub sp 8) h) hcode hp
  have l0 := readAt 96 (by decide)
  have l1 := readAt 40 (by decide)
  have l2 := readAt 8 (by decide)
  have l4 := readAt 16 (by decide)
  let m0 := mem
  have w0 : Writable code m0 (sp - 8) 312 := hw
  let m1 := memStore m0 (sp + 264) sel[0]
  have w1 : Writable code m1 (sp - 8) 312 := w0.memStore (sp + 264) sel[0]
  have st0 : StoreOk code m0 (sp + 264) 8 0x120e5e 8 :=
    storeAt w0 _ 264 rfl (by decide) 71 8 (by decide +kernel)
  have e0 : (a[0] ^^^ (negated a)[0]) &&& parityMask a[0] want ^^^ (negated a)[0] = sel[0] :=
    selectedLimb a want 0 (by decide)
  let m2 := memStore m1 (sp + 272) sel[1]
  have w2 : Writable code m2 (sp - 8) 312 := w1.memStore (sp + 272) sel[1]
  have st1 : StoreOk code m1 (sp + 272) 8 0x120e66 8 :=
    storeAt w1 _ 272 rfl (by decide) 79 8 (by decide +kernel)
  have e1 : (a[1] ^^^ (negated a)[1]) &&& parityMask a[0] want ^^^ (negated a)[1] = sel[1] :=
    selectedLimb a want 1 (by decide)
  let m3 := memStore m2 (sp + 280) sel[2]
  have w3 : Writable code m3 (sp - 8) 312 := w2.memStore (sp + 280) sel[2]
  have st2 : StoreOk code m2 (sp + 280) 8 0x120e6e 8 :=
    storeAt w2 _ 280 rfl (by decide) 87 8 (by decide +kernel)
  have e2 : (a[2] ^^^ (negated a)[2]) &&& parityMask a[0] want ^^^ (negated a)[2] = sel[2] :=
    selectedLimb a want 2 (by decide)
  let m4 := memStore m3 (sp + 288) sel[3]
  have w4 : Writable code m4 (sp - 8) 312 := w3.memStore (sp + 288) sel[3]
  have st3 : StoreOk code m3 (sp + 288) 8 0x120e76 8 :=
    storeAt w3 _ 288 rfl (by decide) 95 8 (by decide +kernel)
  have e3 : (a[3] ^^^ (negated a)[3]) &&& parityMask a[0] want ^^^ (negated a)[3] = sel[3] :=
    selectedLimb a want 3 (by decide)
  let m5 := memStore m4 (sp + 296) sel[4]
  have w5 : Writable code m5 (sp - 8) 312 := w4.memStore (sp + 296) sel[4]
  have st4 : StoreOk code m4 (sp + 296) 8 0x120e7e 8 :=
    storeAt w4 _ 296 rfl (by decide) 103 8 (by decide +kernel)
  have e4 : (a[4] ^^^ (negated a)[4]) &&& parityMask a[0] want ^^^ (negated a)[4] = sel[4] :=
    selectedLimb a want 4 (by decide)
  have push : StoreOk code m5 (sp - 8) 8 0x120e96 5 :=
    storeAt w5 _ (0 - 8) (addr_sub sp 8) (by decide) 127 5 (by decide +kernel)
  dsimp only [m5, m4, m3, m2, m1, m0] at st0 st1 st2 st3 st4 push
  refine ⟨?_, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [hsp, hm, h0, h1, h2, h3, h4, n0, n1, n2, n3, n4, l0, l1, l2, l4,
      e0, e1, e2, e3, e4, st0, st1, st2, st3, st4, push, ite_true]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i,hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Sec1.Affine.Compressed
