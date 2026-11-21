import K256.Proofs.Verify.Core.Lincomb.Loop.Column
import K256.Proofs.Verify.Core.Lincomb.Loop.Packed

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private theorem rowOffset {m : Ram} {table : BitVec 64} (read : Readable m table 0x1340)
    (j : Fin 4) (off : Nat) (fit : off ≤ 0x9a0) :
    table.toNat ≤ (row table j + BitVec.ofNat 64 off).toNat ∧
    (row table j + BitVec.ofNat 64 off).toNat + (0x9a0-off) ≤ table.toNat+0x1340 := by
  have low := read.low
  unfold row
  split
  · rw [toNat_add_ofNat table off (by omega)]
    omega
  · have r := toNat_add_ofNat table 0x9a0 (by omega)
    change (table+0x9a0).toNat = table.toNat+0x9a0 at r
    rw [toNat_add_ofNat _ off (by omega)]
    omega

theorem lookupLoad {m : Ram} {table : BitVec 64} {k : Nat} (read : Readable m table 0x1340)
    (j : Fin 4) (bound : k < 129) :
    LoadOk m (row table j + 1920 + BitVec.ofNat 64 (272*(j.val%2)) + 8 + BitVec.ofNat 64 k) 1 := by
  have off := rowOffset read j (1920+272*(j.val%2)+8+k) (by omega)
  rw [show row table j + 1920 + BitVec.ofNat 64 (272*(j.val%2)) + 8 + BitVec.ofNat 64 k =
    row table j + BitVec.ofNat 64 (1920+272*(j.val%2)+8+k) by simp only [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
  exact LoadOk.of_region read off.1 (by omega)

theorem packMemory {a : Registers} {m n : Ram} {table sp dst : BitVec 64}
    (entry : RoutineEntry a m sp 0x478) (frame : RamWriteFrame m n [scratch sp 0x478])
    (read : Readable m table 0x1340) (apart : Outside [scratch sp 0x478, ⟨dst.toNat,120⟩] table 0x1340)
    (j : Fin 4) (i : Nat) (hi : i < 8) :
    let addr := row table j + BitVec.ofNat 64 (960*(j.val%2)) + BitVec.ofNat 64 (120*i)
    Readable n addr 120 ∧ Outside (digitWrites (baseSp sp)) addr 120 := by
  intro addr
  have r := rowOffset read j (960*(j.val%2)+120*i) (by omega)
  have eq : addr = row table j + BitVec.ofNat 64 (960*(j.val%2)+120*i) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  rw [← eq] at r
  have hi' : addr.toNat + 120 ≤ table.toNat + 0x1340 := by omega
  refine ⟨(read.of_frame frame).sub r.1 hi', ?_⟩
  have room := entry.room
  have low := entry.returnSlot.low
  have base : (baseSp sp).toNat = sp.toNat - 0x1d8 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 0x1d8 ≤ sp.toNat; omega))
  have p1 := toNat_add_ofNat (baseSp sp) 0x58 (by omega)
  have p2 := toNat_add_ofNat (baseSp sp) 0xe0 (by omega)
  change (baseSp sp + 0x58).toNat = _ at p1
  change (baseSp sp + 0xe0).toNat = _ at p2
  have dis := apart.2 _ (.head _)
  change table.toNat + 0x1340 ≤ sp.toNat-0x478 ∨ sp.toNat-0x478+0x478 ≤ table.toNat at dis
  refine ⟨by have := read.low; omega,fun r' hr => ?_⟩
  simp only [digitWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl <;> dsimp only <;> omega

end K256.Proofs.Verify.Core.Lincomb.Loop
