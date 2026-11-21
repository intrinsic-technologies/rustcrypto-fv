import K256.Proofs.Verify.Core.Lincomb.Interface
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Lincomb.Double

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Tactic Common.Field

def ySquareSlots : Vector (BitVec 64) 5 := #v[0x20, 0x28, 0x48, 0x60, 0x40]

def saveYSquare (m : Ram) (q : BitVec 64) (w : Limbs) : Ram :=
  memStore (memStore (memStore (memStore (memStore m (q + 0x20) w[0])
    (q + 0x28) w[1]) (q + 0x48) w[2]) (q + 0x60) w[3]) (q + 0x40) w[4]

private theorem covered : ∀ x ∈ codeRange 0x110d0e bytes_l110d0e,
    x ∈ Extracted.programImage :=
  fun x hx => Common.fnCode_subset_programImage x (code_l110d0e x hx)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem secondSquareSetup {a : Registers} {m : Ram} {q : BitVec 64} {w : Limbs}
    (rsp : a[4].get 64 = q) (window : Writable Extracted.programImage m (q - 8) 0x1f8)
    (input : WordsAt m (q + 0x1a8) 64 w) :
    let n := memStore (saveYSquare m q w) (q - 8) (0x110d64 : BitVec 64)
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l110d0e,a,m⟩ =
      .call ⟨.l1145f0,b,n⟩ ⟨.l110d64,#v[],rfl,some ⟨64,0x110d64⟩⟩ ∧
      b[4] = ⟨64,q-8⟩ ∧ b[6] = ⟨64,q+0x178⟩ ∧ b[7] = ⟨64,q+0x1d0⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      memLoad n (q - 8) 64 = 0x110d64 ∧
      (∀ i : Fin 5, memLoad n (q + ySquareSlots[i]) 64 = w[i]) ∧
      RamWriteFrame m n [⟨(q-8).toNat,0x68 + 8⟩] := by
  intro n
  have word (i : Nat) (hi : i < 5) :
      memLoad m (q + (0x1a8 + BitVec.ofNat 64 (8*i))) 64 = w[i] := by
    rw [← BitVec.add_assoc]
    exact input i hi
  have w0 : memLoad m (q + 0x1a8) 64 = w[0] := word 0 (by decide)
  have w1 : memLoad m (q + 0x1b0) 64 = w[1] := word 1 (by decide)
  have w2 : memLoad m (q + 0x1b8) 64 = w[2] := word 2 (by decide)
  have w3 : memLoad m (q + 0x1c0) 64 = w[3] := word 3 (by decide)
  have w4 : memLoad m (q + 0x1c8) 64 = w[4] := word 4 (by decide)
  refine ⟨?_, ?run, ?sp, ?si, ?di, ?keep, ?slot, ?copies, ?frame⟩
  case run =>
    cfg_eval [rsp]
    segment_words [w0,w1,w2,w3,w4]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using covered)
    rfl
  case sp => rfl
  case si => rfl
  case di => rfl
  case keep =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  case slot =>
    exact memLoad_memStore_same _ _ _ rfl (by decide)
  case copies =>
    rintro ⟨i, hi⟩
    rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4) with rfl|rfl|rfl|rfl|rfl
    · rw [show ySquareSlots[(⟨0, hi⟩ : Fin 5)] = 0x20 from rfl]
      dsimp only [n,saveYSquare]
      segment_words [] <;> rfl
    · rw [show ySquareSlots[(⟨1, hi⟩ : Fin 5)] = 0x28 from rfl]
      dsimp only [n,saveYSquare]
      segment_words [] <;> rfl
    · rw [show ySquareSlots[(⟨2, hi⟩ : Fin 5)] = 0x48 from rfl]
      dsimp only [n,saveYSquare]
      segment_words [] <;> rfl
    · rw [show ySquareSlots[(⟨3, hi⟩ : Fin 5)] = 0x60 from rfl]
      dsimp only [n,saveYSquare]
      segment_words [] <;> rfl
    · rw [show ySquareSlots[(⟨4, hi⟩ : Fin 5)] = 0x40 from rfl]
      dsimp only [n,saveYSquare]
      segment_words [] <;> rfl
  case frame =>
    have low := window.readable.low
    have inside (off : BitVec 64) (fit : (off - (0 - 8)).toNat + 8 ≤ 112) :
        InRegions [⟨(q-8).toNat,112⟩] (q+off) 8 := by
      have nat := toNat_of_offsets (n := 8) (rfl : q + off = q + off) (addr_sub q 8) low (by omega)
      refine ⟨_, .head _, ?_⟩
      change (q-8).toNat ≤ (q+off).toNat ∧ (q+off).toNat + 8 ≤ (q-8).toNat + 112 ∧
        (q+off).toNat + 8 ≤ 2^64
      rw [nat]
      omega
    have f := (RamWriteFrame.refl m _).memStore w[0] (inside 0x20 (by decide))
    have f := f.memStore w[1] (inside 0x28 (by decide))
    have f := f.memStore w[2] (inside 0x48 (by decide))
    have f := f.memStore w[3] (inside 0x60 (by decide))
    have f := f.memStore w[4] (inside 0x40 (by decide))
    exact f.memStore (0x110d64 : BitVec 64)
      ⟨_, .head _, Nat.le_refl _, Nat.add_le_add_left (by decide : 8 ≤ 112) _, by omega⟩

end K256.Proofs.Verify.Core.Lincomb.Double
