import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Induction
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.SquareInterface

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  Common.Field

def doubleWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp - 112).toNat, 112⟩, ⟨(sp + 8).toNat, 0xe8⟩, ⟨(sp + 0xf8).toNat, 8⟩,
   ⟨(sp + 0x108).toNat, 0x98⟩, ⟨(sp + 0x1a8).toNat, 24⟩,
   ⟨(sp + 0x490).toNat, 40⟩, ⟨(sp + 0x850).toNat, 40⟩]

def DoubleArithmetic : Prop :=
  ∀ {fr : Activation} {p : Projective} {a : Registers} {m : Ram} {n : Nat}
    {x y z : Limbs}, n < 4 →
    let sp := fr.rsp - 0xcb8
    Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11d880 fr) →
    a[5] = ⟨64, 0x1000003d10⟩ →
    memLoad m (sp + 0x1bc) 32 = BitVec.ofNat 32 (n+1) →
    memLoad m (sp + 0x1c8) 64 = 0xfffffffffff8 →
    WordsAt m (sp + 0x128) 64 x →
    WordsAt m (sp + 0x150) 64 y →
    WordsAt m (sp + 0x178) 64 z →
    (∀ i : Fin 5, memLoad m (sp + squareCopies[i]) 64 = (squareWords y)[i]) →
    WordsAt m (sp + 0x490) 64 (squareWords z) →
    FieldRepr x p.x 1 → FieldRepr y p.y 1 → FieldRepr z p.z 1 →
    ∃ b out, Reaches .l11d880 a m (doublesLabel n) b out ∧
      DoublesState fr p.double n b out ∧ RamWriteFrame m out (doubleWrites sp)

private theorem stack_offset {m : Ram} {fr : Activation}
    (window : Writable Extracted.programImage m (fr.rsp - 0xed8) 0xed8)
    (k : Nat) (hk : k ≤ 0xcb8) :
    ((fr.rsp - 0xcb8) + BitVec.ofNat 64 k).toNat = (fr.rsp - 0xed8).toNat + 0x220 + k := by
  have h : (fr.rsp - 0xcb8) + BitVec.ofNat 64 k =
      (fr.rsp - 0xed8) + BitVec.ofNat 64 (0x220 + k) := by
    rw [BitVec.ofNat_add]
    bv_omega
  rw [h, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 0x220 + k < 2^64 by omega)]
  rw [Nat.mod_eq_of_lt (show (fr.rsp - 0xed8).toNat + (0x220 + k) < 2^64 by
    have := window.readable.low
    omega), Nat.add_assoc]

private theorem stack_below {m : Ram} {fr : Activation}
    (window : Writable Extracted.programImage m (fr.rsp - 0xed8) 0xed8) :
    ((fr.rsp - 0xcb8) - 112).toNat = (fr.rsp - 0xed8).toNat + (0x220 - 112) := by
  rw [show (fr.rsp - 0xcb8) - 112 = (fr.rsp - 0xed8) + (0x220 - 112 : BitVec 64) by bv_omega]
  rw [BitVec.toNat_add]
  have h := window.readable.low
  simp only [BitVec.reduceSub, BitVec.reduceToNat]
  exact Nat.mod_eq_of_lt (by omega)

private theorem square_frame_transfer {m : Ram} {fr : Activation}
    (window : Writable Extracted.programImage m (fr.rsp - 0xed8) 0xed8) :
    RegionsWithin (squareWrites (fr.rsp - 0xcb8)) (doubleWrites (fr.rsp - 0xcb8)) := by
  let sp := fr.rsp - 0xcb8
  have fits (k j len width : Nat) (hk : k ≤ 0xcb8) (hj : j ≤ 0xcb8)
      (lo : j ≤ k) (hi : k + len ≤ j + width) :
      (sp + BitVec.ofNat 64 j).toNat ≤ (sp + BitVec.ofNat 64 k).toNat ∧
      (sp + BitVec.ofNat 64 k).toNat + len ≤ (sp + BitVec.ofNat 64 j).toNat + width := by
    dsimp only [sp]
    rw [stack_offset window _ hk, stack_offset window _ hj]
    omega
  intro r hr
  simp only [squareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  · have hh := fits 0x30 8 0x28 0xe8 (by decide) (by decide) (by decide) (by decide)
    exact ⟨⟨(sp + 8).toNat, 0xe8⟩, by simp [doubleWrites, sp], hh.1, hh.2⟩
  · have hh := fits 0x88 8 8 0xe8 (by decide) (by decide) (by decide) (by decide)
    exact ⟨⟨(sp + 8).toNat, 0xe8⟩, by simp [doubleWrites, sp], hh.1, hh.2⟩
  · have hh := fits 0x1bc 0x1a8 4 24 (by decide) (by decide) (by decide) (by decide)
    exact ⟨⟨(sp + 0x1a8).toNat, 24⟩, by simp [doubleWrites, sp], hh.1, hh.2⟩
  · exact ⟨⟨(sp + 0x490).toNat, 40⟩, by simp [doubleWrites, sp], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨⟨(sp + 0x850).toNat, 40⟩, by simp [doubleWrites, sp], Nat.le_refl _, Nat.le_refl _⟩

private theorem square_frame_outside {m : Ram} {fr : Activation}
    (window : Writable Extracted.programImage m (fr.rsp - 0xed8) 0xed8)
    (k len : Nat) (between : 0x100 ≤ k)
    (afterMask : k + len ≤ 0x1bc ∨ 0x1c0 ≤ k) (top : k + len ≤ 0x490) :
    Outside (squareWrites (fr.rsp - 0xcb8))
      ((fr.rsp - 0xcb8) + BitVec.ofNat 64 k) len := by
  let sp := fr.rsp - 0xcb8
  have hks : (sp + BitVec.ofNat 64 k).toNat = (fr.rsp - 0xed8).toNat + 0x220 + k :=
    stack_offset window k (by omega)
  have h30 : (sp + 0x30).toNat = (fr.rsp - 0xed8).toNat + 0x220 + 0x30 :=
    stack_offset window 0x30 (by decide)
  have h88 : (sp + 0x88).toNat = (fr.rsp - 0xed8).toNat + 0x220 + 0x88 :=
    stack_offset window 0x88 (by decide)
  have hcounter : (sp + 0x1bc).toNat = (fr.rsp - 0xed8).toNat + 0x220 + 0x1bc :=
    stack_offset window 0x1bc (by decide)
  have h490 : (sp + 0x490).toNat = (fr.rsp - 0xed8).toNat + 0x220 + 0x490 :=
    stack_offset window 0x490 (by decide)
  have h850 : (sp + 0x850).toNat = (fr.rsp - 0xed8).toNat + 0x220 + 0x850 :=
    stack_offset window 0x850 (by decide)
  have hbelow : (sp - 112).toNat = (fr.rsp - 0xed8).toNat + (0x220 - 112) :=
    stack_below window
  refine ⟨?_, ?_⟩
  · change (sp + BitVec.ofNat 64 k).toNat + len ≤ _
    rw [hks]
    have := window.readable.low
    omega
  · intro r hr
    simp only [squareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (sp + BitVec.ofNat 64 k).toNat + len ≤ (sp - 112).toNat ∨
        (sp - 112).toNat + 112 ≤ (sp + BitVec.ofNat 64 k).toNat
      simp only [hks, hbelow]
      omega
    · change (sp + BitVec.ofNat 64 k).toNat + len ≤ (sp + 0x30).toNat ∨
        (sp + 0x30).toNat + 0x28 ≤ (sp + BitVec.ofNat 64 k).toNat
      simp only [hks, h30]
      omega
    · change (sp + BitVec.ofNat 64 k).toNat + len ≤ (sp + 0x88).toNat ∨
        (sp + 0x88).toNat + 8 ≤ (sp + BitVec.ofNat 64 k).toNat
      simp only [hks, h88]
      omega
    · change (sp + BitVec.ofNat 64 k).toNat + len ≤ (sp + 0x1bc).toNat ∨
        (sp + 0x1bc).toNat + 4 ≤ (sp + BitVec.ofNat 64 k).toNat
      simp only [hks, hcounter]
      omega
    · change (sp + BitVec.ofNat 64 k).toNat + len ≤ (sp + 0x490).toNat ∨
        (sp + 0x490).toNat + 40 ≤ (sp + BitVec.ofNat 64 k).toNat
      simp only [hks, h490]
      omega
    · change (sp + BitVec.ofNat 64 k).toNat + len ≤ (sp + 0x850).toNat ∨
        (sp + 0x850).toNat + 40 ≤ (sp + BitVec.ofNat 64 k).toNat
      simp only [hks, h850]
      omega

theorem doubleStep_of_arithmetic (squares : SquarePreparation) (arithmetic : DoubleArithmetic) :
    DoubleStep doubleWrites := by
  intro fr p a m n bound state
  let sp := fr.rsp - 0xcb8
  have atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11d810 fr) := by
    simpa only [doublesLabel, Nat.add_one_ne_zero, ite_false] using state.atoms
  have count : a[1].get 32 = BitVec.ofNat 32 (n+1) := by
    have h := congrArg (BitVec.setWidth 32) state.count
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)] using h
  have window : Writable Extracted.programImage m (fr.rsp - 0xed8) 0xed8 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := atoms
    exact h
  obtain ⟨x, y, z, wx, wy, wz, hx, hy, hz⟩ := state.acc.coordinates
  have accAddr : fr.rsp - 0xb90 = sp + 0x128 := by dsimp only [sp]; bv_omega
  rw [accAddr] at wx wy wz
  have yAddr : sp + 0x128 + 40 = sp + 0x150 := by bv_omega
  have zAddr : sp + 0x128 + 80 = sp + 0x178 := by bv_omega
  rw [yAddr] at wy
  rw [zAddr] at wz
  obtain ⟨b, mem, r, atm, mask, counter, yy, zz, frame⟩ :=
    squares atoms state.savedWidths count state.mask state.temp wy wz
  have move {k : Nat} {l : Limbs} (words : WordsAt m (sp + BitVec.ofNat 64 k) 64 l)
      (hk : k = 0x128 ∨ k = 0x150 ∨ k = 0x178) :
      WordsAt mem (sp + BitVec.ofNat 64 k) 64 l := by
    apply words.of_frame frame (by decide)
    exact square_frame_outside window k 40 (by omega) (by omega) (by omega)
  have saved : memLoad mem (sp + 0x1c8) 64 = 0xfffffffffff8 := by
    exact (frame.memLoad_eq (square_frame_outside window 0x1c8 8
      (by decide) (by decide) (by decide))).trans state.savedMask
  obtain ⟨c, out, tail, done, writes⟩ := arithmetic (by omega : n < 4) atm mask counter saved
    (move wx (by decide)) (move wy (by decide)) (move wz (by decide)) yy zz hx hy hz
  have transfer := (RamWriteFrame.refl m (doubleWrites sp)).trans frame
    (square_frame_transfer window)
  have total := transfer.trans writes (fun r h => ⟨r, h, Nat.le_refl _, Nat.le_refl _⟩)
  have run := r.trans tail
  refine ⟨c, out, ?_, done, total⟩
  simpa only [doublesLabel, Nat.add_one_ne_zero, ite_false] using run

end K256.Proofs.Generate.Generator.Multiply
