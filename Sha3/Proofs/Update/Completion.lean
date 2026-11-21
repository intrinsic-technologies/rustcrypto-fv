import Sha3.Proofs.Update.Completion.Bounds
import Sha3.Proofs.Update.Completion.Tail
import Sha3.Proofs.Update.Division
import Sha3.Proofs.Update.FullBlocks
import Sha3.Proofs.Update.BlockAlgorithm

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program
open Keccak Permutation

theorem completion_advance [Bindings] {v : Variant} {initial s : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    (h : BodyInvariant initial s) (boundary : ReturnBoundary) (hb : ¬ InProgram boundary.rip)
    (offset : Nat) (hoffset : offset ≤ bytes.size) (hip : s.RIP = divisionAddress v)
    (hpointer : s.regValue .r15 = initial.regValue .rsi)
    (hslot : (Operand.mem (frameBase initial) : Operand 64).read s = initial.regValue .rsi + 200)
    (h14 : s.regValue .rbx = initial.regValue .rdx + BitVec.ofNat 64 offset)
    (h15 : s.regValue .r12 = BitVec.ofNat 64 (bytes.size - offset)) :
    ∃ fuel t, Advances boundary fuel s t ∧ BodyInvariant initial t ∧
      t.RIP = cursorWriteAddress v ∧
      t.regValue .rdi = initial.regValue .rsi + 200 ∧
      memoryLanes (initial.regValue .rsi) t =
        (Incremental.update keccakLanes v.rate
          ⟨memoryLanes (initial.regValue .rsi) s, 0⟩
          (bytes.extract offset bytes.size)).lanes ∧
      (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64
        (Incremental.update keccakLanes v.rate
          ⟨memoryLanes (initial.regValue .rsi) s, 0⟩
          (bytes.extract offset bytes.size)).cursor := by
  let n := bytes.size - offset
  let count := n / v.rate
  let full := count * v.rate
  have hdecomp : full + n % v.rate = n := by
    dsimp only [full, count]
    simpa only [Nat.mul_comm] using Nat.div_add_mod n v.rate
  have hspan : offset + full ≤ bytes.size := by dsimp only [n] at hdecomp; omega
  have hremaining : bytes.size - (offset + full) = n % v.rate := by
    dsimp only [n] at hdecomp ⊢
    omega
  have hlt : bytes.size - (offset + full) < v.rate := by
    rw [hremaining]
    exact Nat.mod_lt _ v.rate_pos
  obtain ⟨fuel, u, ha, hu, huip, hu12, hu14, hu15, hupointer, huslot, hulanes⟩ :
      ∃ fuel u, Advances boundary fuel s u ∧ BodyInvariant initial u ∧
        u.RIP = tailAddress v ∧ u.regValue .r13 = BitVec.ofNat 64 full ∧
        u.regValue .rbx = initial.regValue .rdx + BitVec.ofNat 64 offset ∧
        u.regValue .r12 = BitVec.ofNat 64 (n % v.rate) ∧
        u.regValue .r15 = initial.regValue .rsi ∧
        (Operand.mem (frameBase initial) : Operand 64).read u = initial.regValue .rsi + 200 ∧
        memoryLanes (initial.regValue .rsi) u =
          FullBlocks.absorbedPrefix (memoryLanes (initial.regValue .rsi) s)
            v.rate bytes offset count := by
    have hn : n < 2 ^ 32 := by have := hc.input_size_lt; dsimp only [n]; omega
    obtain ⟨fuel, d, hd, hid, dr, df⟩ := Division.advance_invariant hc h boundary hb n hn hip h15
    have hd12 : d.regValue .r13 = BitVec.ofNat 64 full := by
      simpa only [full, count, Nat.mul_comm] using dr.full
    have hd14 : d.regValue .rbx = initial.regValue .rdx + BitVec.ofNat 64 offset :=
      dr.input.trans h14
    have hdlanes : memoryLanes (initial.regValue .rsi) d =
        memoryLanes (initial.regValue .rsi) s := by
      apply LaneMemory.memoryLanes_eq_of_memByte_eq
      intro address
      rw [df.external Division.clobbers_nomem]
    have hdptr := (df.read (n := 64) (r := 15) (by simp [Division.clobbers])).trans hpointer
    have hdslot : (Operand.mem (frameBase initial) : Operand 64).read d = initial.regValue .rsi + 200 := by
      simpa only [Operand.read, df.external Division.clobbers_nomem] using hslot
    by_cases hz : count = 0
    · refine ⟨fuel, d, hd, hid, dr.short hz, hd12, hd14, dr.remaining, hdptr, hdslot, ?_⟩
      simpa only [hz, FullBlocks.absorbedPrefix_zero] using hdlanes
    · have hpos : 0 < count := Nat.pos_of_ne_zero hz
      obtain ⟨h13, h5, hdip⟩ := dr.blocks hpos
      obtain ⟨u, hrun, hiu, huip, _, _, hkept, hlanes, _, hslotu, hptru⟩ :=
        FullBlocks.full_blocks_from_start (count := count) hc hb hspan hpos hid hdip hdptr
          (h5.trans h14) h13
      refine ⟨_, u, hd.trans hrun, hiu, huip, ?_, ?_, ?_, hptru, hslotu.trans hdslot, ?_⟩
      · exact (hkept 13 (by simp [FullBlocks.keptRegisters])).trans hd12
      · exact (hkept 3 (by simp [FullBlocks.keptRegisters])).trans hd14
      · exact (hkept 12 (by simp [FullBlocks.keptRegisters])).trans dr.remaining
      · simpa only [hdlanes] using hlanes
  obtain ⟨tailFuel, t, htail, ht, htip, htptr, htlanes, htcount⟩ :=
    Completion.tail_advance hc hu boundary hb offset full hspan hlt huip hupointer huslot hu14 hu12
      (by rw [hremaining]; exact hu15)
  have hupdate : Incremental.update keccakLanes v.rate
      ⟨memoryLanes (initial.regValue .rsi) s, 0⟩ (bytes.extract offset bytes.size) =
      Incremental.update keccakLanes v.rate
        ⟨memoryLanes (initial.regValue .rsi) u, 0⟩
        (bytes.extract (offset + full) bytes.size) := by
    rw [ByteArray.extract_eq_extract_append_extract (offset + full) (by omega) hspan,
      Incremental.update_append, update_full_blocks bytes _ v.rate offset count v.rate_pos hspan,
      hulanes]
  rw [← hupdate] at htlanes htcount
  exact ⟨_, t, ha.trans htail, ht, htip, htptr, htlanes, htcount⟩

end Sha3.Proofs.Update
