import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2

set_option autoImplicit false

namespace K256.Proofs.Sec1.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

def selectionWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp + 7).toNat, 1⟩, ⟨(sp + 80).toNat, 65⟩]

private theorem selectionOffset {sp : BitVec 64} {i : Nat}
    (hsp : (sp + 7).toNat + 273 ≤ 2 ^ 32) (hi : 7 ≤ i ∧ i ≤ 280) :
    (sp + BitVec.ofNat 64 i).toNat = (sp + 7).toNat + (i - 7) := by
  have he : BitVec.ofNat 64 i = (7 : BitVec 64) + BitVec.ofNat 64 (i - 7) := by
    change BitVec.ofNat 64 i = BitVec.ofNat 64 7 + BitVec.ofNat 64 (i - 7)
    rw [← BitVec.ofNat_add, show 7 + (i - 7) = i by omega]
  rw [he, ← BitVec.add_assoc, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i - 7 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

private theorem selectionWritable {code : CodeMap} {m : Ram} {sp : BitVec 64} {i : Nat}
    (hw : Writable code m (sp + 7) 273) (hi : 7 ≤ i ∧ i < 280) :
    Writable code m (sp + BitVec.ofNat 64 i) 1 := by
  apply hw.sub <;> rw [selectionOffset hw.readable.low (by omega)] <;> omega

private theorem selectionOutput {sp : BitVec 64} {i : Nat}
    (hsp : (sp + 7).toNat + 273 ≤ 2 ^ 32) (hi : i < 65) :
    InRegion ⟨(sp + 80).toNat, 65⟩ (sp + BitVec.ofNat 64 (80 + i)) 1 := by
  unfold InRegion
  have hdst : (sp + 80).toNat = (sp + 7).toNat + 73 :=
    selectionOffset (i := 80) hsp (by decide)
  change (sp + 80).toNat ≤ _ ∧ _ + 1 ≤ (sp + 80).toNat + 65 ∧ _
  rw [selectionOffset hsp (by omega), hdst]
  omega

private theorem selectionSource {sp : BitVec 64} {i : Nat}
    (hsp : (sp + 7).toNat + 273 ≤ 2 ^ 32) (hi : i < 65) :
    Outside (selectionWrites sp) (sp + BitVec.ofNat 64 (215 + i)) 1 := by
  have hsrc := selectionOffset hsp (i := 215 + i) (by omega)
  have hdst : (sp + 80).toNat = (sp + 7).toNat + 73 :=
    selectionOffset (i := 80) hsp (by decide)
  refine ⟨by omega, ?_⟩
  intro r hr
  simp only [selectionWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inr (by simpa only [hsrc] using show (sp + 7).toNat + 1 ≤
      (sp + 7).toNat + (215 + i - 7) by omega)
  · exact Or.inr (by
      change (sp + 80).toNat + 65 ≤ (sp + BitVec.ofNat 64 (215 + i)).toNat
      rw [hdst, hsrc]
      omega)

private def selectedByteMemory (sp : BitVec 64) (i : Nat) (m : Ram) : Ram :=
  memStore (memStore m (sp + 7) (0 : BitVec 8)) (sp + BitVec.ofNat 64 (80 + i))
    (memLoad m (sp + BitVec.ofNat 64 (215 + i)) 8)

private theorem selectionMemoryStep {sp : BitVec 64} {i : Nat} {o m : Ram}
    (hsp : (sp + 7).toNat + 273 ≤ 2 ^ 32) (hi : i < 65)
    (frame : RamWriteFrame o m (selectionWrites sp))
    (copied : ∀ j < i, memLoad m (sp + BitVec.ofNat 64 (80 + j)) 8 =
      memLoad o (sp + BitVec.ofNat 64 (215 + j)) 8) :
    RamWriteFrame o (selectedByteMemory sp i m) (selectionWrites sp) ∧
      ∀ j < i + 1, memLoad (selectedByteMemory sp i m) (sp + BitVec.ofNat 64 (80 + j)) 8 =
        memLoad o (sp + BitVec.ofNat 64 (215 + j)) 8 := by
  have hs : InRegion ⟨(sp + 7).toNat, 1⟩ (sp + 7) 1 :=
    ⟨Nat.le_refl _, Nat.le_refl _, by omega⟩
  have hm := frame.memStore (0 : BitVec 8) ⟨_, List.mem_cons_self .., hs⟩
  refine ⟨hm.memStore _ ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
    selectionOutput hsp hi⟩, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    unfold selectedByteMemory
    rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
    exact frame.memLoad_eq (selectionSource hsp hi)
  · have hj' : j < i := by omega
    have hjdst := selectionOutput hsp (i := j) (by omega)
    have hidst := selectionOutput hsp hi
    have hjaddr := selectionOffset hsp (i := 80 + j) (by omega)
    have hiaddr := selectionOffset hsp (i := 80 + i) (by omega)
    have apart : RangeApart (sp + BitVec.ofNat 64 (80 + i)) 1
        (sp + BitVec.ofNat 64 (80 + j)) 1 := by
      apply RangeApart.of_toNat hidst.2.2 hjdst.2.2
      right
      omega
    have apartScratch : RangeApart (sp + 7) 1 (sp + BitVec.ofNat 64 (80 + j)) 1 := by
      apply RangeApart.of_toNat hs.2.2 hjdst.2.2
      left
      omega
    unfold selectedByteMemory
    rw [memLoad_memStore_of_rangeApart _ _ _ _ 8 apart,
      memLoad_memStore_of_rangeApart _ _ _ _ 8 apartScratch]
    exact copied j hj'

private def selectionLabel (i : Nat) : Label :=
  if i < 65 then .l121890 else .l1218bb

def SelectionKeeps (a b : Vector Value Reg.count) : Prop :=
  ∀ r : Fin Reg.count, r.val ∈ [0, 3, 4, 5, 9, 10, 11, 12, 13, 14, 15, 22, 39, 50, 51] →
    b[r] = a[r]

private theorem selectionBlock {code : CodeMap} {sp : BitVec 64} {i : Nat}
    {a : Vector Value Reg.count} {m : Ram}
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (hstack : Writable code m (sp + 7) 273) (hi : i < 65)
    (hsp : a[4] = ⟨64, sp⟩) (hidx : a[2] = ⟨64, BitVec.ofNat 64 i⟩)
    (hsel : a[0].get 8 = 0) :
    ∃ b : Vector Value Reg.count,
      program.runBlock (dialect code) ⟨.l121890, a, m⟩ =
        .jump ⟨selectionLabel (i + 1), b, selectedByteMemory sp i m⟩ ∧
      b[2] = ⟨64, BitVec.ofNat 64 (i + 1)⟩ ∧ SelectionKeeps a b := by
  let temp := memStore m (sp + 7) (0 : BitVec 8)
  have hwrite := hstack.memStore (sp + 7) (0 : BitVec 8)
  have hsrcw := selectionWritable hstack (i := 215 + i) (by omega)
  have hsrc : LoadOk m (sp + BitVec.ofNat 64 (215 + i)) 1 :=
    ⟨hsrcw.readable.low, hsrcw.readable.present⟩
  have htmpw : Writable code m (sp + 7) 1 :=
    hstack.sub (Nat.le_refl _) (by omega)
  have haltw := selectionWritable hwrite (i := 8 + i) (by omega)
  have halt : LoadOk temp (sp + BitVec.ofNat 64 (8 + i)) 1 :=
    ⟨haltw.readable.low, haltw.readable.present⟩
  have htmpRead : LoadOk temp (sp + 7) 1 := by
    have hw := htmpw.memStore (sp + 7) (0 : BitVec 8)
    exact ⟨hw.readable.low, hw.readable.present⟩
  have hdstw := selectionWritable hwrite (i := 80 + i) (by omega)
  have htmp : StoreOk code m (sp + 7) 1 0x121898 4 :=
    ParseSignature.storeOk_of_codeRange (base := 0x121890) (off := 8) htmpw
      (fun x hx => hcode x (code_l121890 x hx)) (by decide)
  have hdst : StoreOk code temp (sp + BitVec.ofNat 64 (80 + i)) 1 0x1218ad 5 :=
    ParseSignature.storeOk_of_codeRange (base := 0x121890) (off := 29) hdstw
      (fun x hx => hcode x (code_l121890 x hx)) (by decide)
  have hr : memLoad temp (sp + 7) 8 = 0 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have hspGet : a[4].get 64 = sp := by rw [hsp, Value.get_mk]
  have hidxGet : a[2].get 64 = BitVec.ofNat 64 i := by rw [hidx, Value.get_mk]
  have hselGet : (a[0].get 64).setWidth 8 = 0 := by
    change (a[0].bits.setWidth 64).setWidth 8 = 0
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
    exact hsel
  have addr (k : Nat) : sp + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      sp + BitVec.ofNat 64 (k + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm i k]
  have addrSrc : sp + BitVec.ofNat 64 i + 215 = sp + BitVec.ofNat 64 (215 + i) := addr 215
  have addrAlt : sp + BitVec.ofNat 64 i + 8 = sp + BitVec.ofNat 64 (8 + i) := addr 8
  have addrDst : sp + BitVec.ofNat 64 i + 80 = sp + BitVec.ofNat 64 (80 + i) := addr 80
  have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) :=
    (BitVec.ofNat_add i 1).symm
  have hsimp : (testFlags ((0 : BitVec 8) &&& 0)).ZF.getD false = true := rfl
  have hc (he : i + 1 = 65) : BitVec.ofNat 64 (i + 1) = 65 := by
    rw [he]
    rfl
  have hc' (he : i + 1 < 65) : BitVec.ofNat 64 (i + 1) ≠ 65 := by
    intro h
    have ht := congrArg BitVec.toNat h
    change (i + 1) % 2 ^ 64 = 65 at ht
    omega
  have hbranch : (!(BitVec.ofNat 64 (i + 1) == 65)) = true ↔ i + 1 < 65 := by
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
    exact ⟨fun h => Nat.lt_of_le_of_ne (by omega) (fun he => h (hc he)), hc'⟩
  dsimp only [temp] at halt htmpRead hdst hr
  refine ⟨?b, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [hspGet, hidxGet, hselGet, addrAlt, addrSrc, addrDst, hsrc, halt,
      htmp, htmpRead, hdst, hr, hsimp, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      hinc, cmpSpec_ZF, hbranch, selectionLabel, selectedByteMemory]
    have hw (x : BitVec 8) : (x.setWidth 32).setWidth 8 = x := by
      rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
    rw [hw]
    split <;> rename_i h <;> first | (rw [ite_eq_left h] <;> rfl) | (rw [ite_eq_right h] <;> rfl)
  case post =>
    refine ⟨rfl, ?_⟩
    intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases r with ⟨r, hb⟩
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> rfl

theorem selectionLoop {code : CodeMap} {sp : BitVec 64} {a : Vector Value Reg.count}
    {m : Ram} {calls : List (StackFrame Value Label signature Reg.count)}
    (hcode : ∀ x ∈ fnCode, x ∈ code) (hstack : Writable code m (sp + 7) 273)
    (hsp : a[4] = ⟨64, sp⟩) (hidx : a[2] = ⟨64, 0⟩) (hsel : a[0].get 8 = 0) :
    ∃ (b : Vector Value Reg.count) (m' : Ram), (program.sem (dialect code)).Reaches
      ⟨⟨.l121890, a, m⟩, calls⟩ ⟨⟨.l1218bb, b, m'⟩, calls⟩ ∧
      b[2] = ⟨64, 65⟩ ∧ SelectionKeeps a b ∧
      RamWriteFrame m m' (selectionWrites sp) ∧
      ∀ i < 65, memLoad m' (sp + BitVec.ofNat 64 (80 + i)) 8 =
        memLoad m (sp + BitVec.ofNat 64 (215 + i)) 8 := by
  have hprefix (i : Nat) (hi : i ≤ 65) :
      ∃ (b : Vector Value Reg.count) (m' : Ram), (program.sem (dialect code)).Reaches
        ⟨⟨.l121890, a, m⟩, calls⟩ ⟨⟨selectionLabel i, b, m'⟩, calls⟩ ∧
        b[2] = ⟨64, BitVec.ofNat 64 i⟩ ∧ SelectionKeeps a b ∧
        RamWriteFrame m m' (selectionWrites sp) ∧
        ∀ j < i, memLoad m' (sp + BitVec.ofNat 64 (80 + j)) 8 =
          memLoad m (sp + BitVec.ofNat 64 (215 + j)) 8 := by
    induction i with
    | zero =>
      exact ⟨a, m, .refl _, hidx, fun _ _ => rfl, RamWriteFrame.refl _ _, fun _ h => by omega⟩
    | succ i ih =>
      have hlt : i < 65 := by omega
      obtain ⟨b, mid, reached, idx, keeps, frame, copied⟩ := ih (by omega)
      have hsp' : b[4] = ⟨64, sp⟩ := (keeps 4 (by decide)).trans hsp
      have hsel' : b[0].get 8 = 0 := by
        change b[(0 : Fin Reg.count)].get 8 = 0
        rw [keeps 0 (by decide)]
        exact hsel
      obtain ⟨b', next, idx', keeps'⟩ :=
        selectionBlock hcode (hstack.of_frame frame) hlt hsp' idx hsel'
      have step : (program.sem (dialect code)).Step ⟨⟨selectionLabel i, b, mid⟩, calls⟩
          ⟨⟨selectionLabel (i + 1), b', selectedByteMemory sp i mid⟩, calls⟩ := by
        change program.step (dialect code) ⟨⟨selectionLabel i, b, mid⟩, calls⟩ = _
        rw [show selectionLabel i = .l121890 from ite_eq_left hlt]
        simp only [Program.step, next, Transfer.next]
      exact ⟨b', _, reached.tail step, idx', fun r hr => (keeps' r hr).trans (keeps r hr),
        selectionMemoryStep hstack.readable.low hlt frame copied⟩
  exact hprefix 65 (by decide)

end K256.Proofs.Sec1.Serialize
