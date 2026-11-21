import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Generate.LIR.CallPre
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Ecdh.Scalar

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Ecdh.LIR

def prepareMemory (m : Ram) (base : BitVec 64) (start : Nat) (ret : BitVec 64) : Ram :=
  let m := memStore m (base + BitVec.ofNat 64 (start + 24)) (0 : BitVec 64)
  let m := memStore m (base + BitVec.ofNat 64 (start + 16)) (0 : BitVec 64)
  let m := memStore m (base + BitVec.ofNat 64 (start + 8)) (0 : BitVec 64)
  let m := memStore m (base + BitVec.ofNat 64 start) (0 : BitVec 64)
  memStore m (base - 8) ret

theorem prepareMemory_frame {code : CodeMap} {m : Ram} {base ret : BitVec 64} {start : Nat}
    (win : Writable code m (base - 8) (start + 40)) :
    RamWriteFrame m (prepareMemory m base start ret)
      [⟨(base - 8).toNat, 8⟩, ⟨(base + BitVec.ofNat 64 start).toNat, 32⟩] := by
  let z := base + BitVec.ofNat 64 start
  let regions : List Prelude.MemoryRegion := [⟨(base - 8).toNat, 8⟩, ⟨z.toNat, 32⟩]
  have low := win.readable.low
  have zAddr : z = (base - 8) + BitVec.ofNat 64 (start + 8) := by
    dsimp only [z]
    rw [BitVec.ofNat_add]
    bv_omega
  have zLow : z.toNat + 32 ≤ 2 ^ 64 := by
    rw [zAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := start + 8) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have cell (j : Nat) (hj : j ≤ 24) : InRegions regions (base + BitVec.ofNat 64 (start + j)) 8 := by
    refine ⟨⟨z.toNat, 32⟩, by simp [regions], ?_⟩
    have addr : (base + BitVec.ofNat 64 (start + j)).toNat = z.toNat + j := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      change (z + BitVec.ofNat 64 j).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]
    change z.toNat ≤ _ ∧ _ + 8 ≤ z.toNat + 32 ∧ _ + 8 ≤ 2 ^ 64
    rw [addr]
    omega
  have slot : InRegions regions (base - 8) 8 := by
    refine ⟨⟨(base - 8).toNat, 8⟩, List.mem_cons_self, ?_⟩
    exact ⟨Nat.le_refl _, Nat.le_refl _, by omega⟩
  exact RamWriteFrame.refl m regions
    |>.memStore (0 : BitVec 64) (cell 24 (by decide))
    |>.memStore (0 : BitVec 64) (cell 16 (by decide))
    |>.memStore (0 : BitVec 64) (cell 8 (by decide))
    |>.memStore (0 : BitVec 64) (cell 0 (by decide))
    |>.memStore ret slot

theorem prepareMemory_return (m : Ram) (base : BitVec 64) (start : Nat) (ret : BitVec 64) :
    memLoad (prepareMemory m base start ret) (base - 8) 64 = ret :=
  memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem prepareMemory_words (m : Ram) (base ret : BitVec 64) {start : Nat}
    (offset : start = 0x8d8 ∨ start = 0x1058) :
    WordsAt (prepareMemory m base start ret) (base + BitVec.ofNat 64 start) 64 (Vector.replicate 4 0) := by
  intro i hi
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals rcases offset with rfl | rfl
  all_goals unfold prepareMemory
  all_goals
    simp (config := { bitVecOfNat := false }) only [wordAddr, Nat.reduceDiv, Nat.reduceMul,
      Nat.reduceAdd, BitVec.reduceOfNat, Lift.reduceAddOffset, add_zero_lit, Vector.getElem_replicate]
    simp (disch := store_disch) only [memLoad_memStore_same, memLoad_memStore_of_rangeApart]

def selectArgs (a : Vector Value Reg.count) (base : BitVec 64) (flag : BitVec 32) :=
  let a := a.set 1 ⟨64, flag.setWidth 64⟩
  let a := a.set 2 ⟨64, base + 0x158⟩
  let a := a.set 4 ⟨64, base - 8⟩
  let a := a.set 5 ⟨64, flag.setWidth 64⟩
  let a := a.set 6 ⟨64, base + 0x8d8⟩
  let a := a.set 7 ⟨64, base + 0xc98⟩
  a.set 12 ⟨64, base + 0xc98⟩

def compareArgs (a : Vector Value Reg.count) (base : BitVec 64) :=
  let a := a.set 4 ⟨64, base - 8⟩
  let a := a.set 6 ⟨64, base + 0x1058⟩
  a.set 7 ⟨64, base + 0xc98⟩

theorem selectArgs_width {a : Vector Value Reg.count} (base : BitVec 64) (flag : BitVec 32)
    (i : Fin Reg.count) (width : a[i].width = 64) : (selectArgs a base flag)[i].width = 64 := by
  change (selectArgs a base flag)[i.val].width = 64
  simp only [selectArgs, Vector.getElem_set]
  repeat' first | rfl | exact width | split

theorem compareArgs_width {a : Vector Value Reg.count} (base : BitVec 64)
    (i : Fin Reg.count) (width : a[i].width = 64) : (compareArgs a base)[i].width = 64 := by
  change (compareArgs a base)[i.val].width = 64
  simp only [compareArgs, Vector.getElem_set]
  repeat' first | rfl | exact width | split

local macro "prepare_registers" regs:Lean.Parser.Tactic.simpLemma : tactic =>
  `(tactic| (
    congr 2
    apply (show ∀ {v w : Vector Value 53}, (∀ i : Fin 53, v[i.val] = w[i.val]) → v = w from
      fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
    intro i
    finite_cases i <;> simp only [$regs, Vector.getElem_set] <;> rfl))

theorem prepareSelect {code : CodeMap} {a : Vector Value Reg.count} {m : Ram} {base : BitVec 64}
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (rsp : a[4].get 64 = base) (r15 : a[15].get 64 = base + 0x158)
    (win : Writable code m (base - 8) 0x900)
    (bit : memLoad m (base + 0x178) 8 = 1) :
    let flag := memLoad m (base + 0x178) 32
    program.runBlock (dialect code) ⟨.l1016be, a, m⟩ =
      .call ⟨.l10a220, selectArgs a base flag, prepareMemory m base 0x8d8 0x101712⟩
        ⟨.l101712, #v[], rfl, some ⟨64, 0x101712⟩⟩ ∧ flag.setWidth 8 = 1 := by
  constructor
  · have incl := fun x hx => hcode x (code_l1016be x hx)
    cfg_eval [rsp, r15]
    iterate 6
      refine (ite_eq_left ?_).trans ?_
      · slot_guard using incl
    repeat' rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by decide))]
    prepare_registers selectArgs
  · rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 32),
      extractLsb'_memLoad _ _ _ _ (by decide) (by decide) (by decide)]
    simpa only [Nat.reduceDiv, BitVec.add_zero] using bit

theorem prepareCompare {code : CodeMap} {a : Vector Value Reg.count} {m : Ram} {base : BitVec 64}
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (rsp : a[4].get 64 = base) (r12 : a[12].get 64 = base + 0xc98)
    (win : Writable code m (base - 8) 0x1080) :
    program.runBlock (dialect code) ⟨.l101712, a, m⟩ =
      .call ⟨.l10a280, compareArgs a base, prepareMemory m base 0x1058 0x101752⟩
        ⟨.l101752, #v[], rfl, some ⟨64, 0x101752⟩⟩ := by
  have incl := fun x hx => hcode x (code_l101712 x hx)
  cfg_eval [rsp, r12]
  iterate 5
    refine (ite_eq_left ?_).trans ?_
    · slot_guard using incl
  prepare_registers compareArgs

end K256.Proofs.Ecdh.Scalar
