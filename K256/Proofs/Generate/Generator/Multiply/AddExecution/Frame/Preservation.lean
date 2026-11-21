import K256.Proofs.Generate.Generator.Multiply.AddExecution.Frame.State
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Frame.Segment

namespace K256.Proofs.Generate.Generator.Multiply.AddFrame

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR

private theorem stackOffset {fr : Activation} (depth : 0x218 ≤ fr.rsp.toNat)
    {k : Nat} (hk : k ≤ 0x218) :
    (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
  have h : k < 2^64 := by omega
  have h' : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 k).toNat ≤ fr.rsp.toNat; omega), h']

theorem AtBody.preserve {fr : Activation} {a : Values Value n} {b : Values Value k} {m m' : Ram}
    (s : AtBody fr a m) (p : a.Prefix b) (h : RamWriteFrame m m' (spills (fr.rsp - 0x218)))
    (depth : 0x218 ≤ fr.rsp.toNat) (low : fr.rsp.toNat + 8 ≤ 2^32) : AtBody fr b m' := by
  have hbase := stackOffset (fr := fr) depth (Nat.le_refl 0x218)
  change (fr.rsp - 0x218).toNat = fr.rsp.toNat - 0x218 at hbase
  have hsum (i : Nat) (hi : i ≤ 0x218) :
      ((fr.rsp - 0x218) + BitVec.ofNat 64 i).toNat = fr.rsp.toNat - 0x218 + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), hbase, Nat.mod_eq_of_lt (by omega)]
  have hs : ((fr.rsp - 0x218) + 0x188).toNat = _ := hsum 0x188 (by decide)
  have keep (addr : BitVec 64) (bound : addr.toNat + 8 ≤ 2^64)
      (first : (fr.rsp - 0x218).toNat + 0x180 ≤ addr.toNat)
      (second : addr.toNat + 8 ≤ fr.rsp.toNat - 0x218 + 0x188 ∨ fr.rsp.toNat - 48 ≤ addr.toNat) :
      memLoad m' addr 64 = memLoad m addr 64 := by
    apply h.memLoad_eq
    refine ⟨bound, ?_⟩
    intro r hr
    simp only [spills, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr first
    · change addr.toNat + 8 ≤ ((fr.rsp - 0x218) + 0x188).toNat ∨
        ((fr.rsp - 0x218) + 0x188).toNat + 0x60 ≤ addr.toNat
      omega
  have slot (i : Nat) (hi : i ≤ 48) :=
    stackOffset (fr := fr) depth (show i ≤ 0x218 by omega)
  have saved (i : Nat) (hi : i ≤ 48) :
      memLoad m' (fr.rsp - BitVec.ofNat 64 i) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 i) 64 := by
    have := slot i hi
    apply keep <;> omega
  have nh := Nat.lt_of_lt_of_le s.size p.1
  refine ⟨nh, (congrArg (Value.get 64) (p.2 65 s.size nh)).trans s.sp,
    p.read (by have := s.size; omega) (by omega) s.df,
    p.read (by have := s.size; omega) (by omega) s.mx,
    p.read (by have := s.size; omega) (by omega) s.ftw,
    p.read (by have := s.size; omega) (by omega) s.fcw, ?_,
    (saved 48 (by decide)).trans s.bx, (saved 40 (by decide)).trans s.r12,
    (saved 32 (by decide)).trans s.r13, (saved 24 (by decide)).trans s.r14,
    (saved 16 (by decide)).trans s.r15, (saved 8 (by decide)).trans s.bp,
    (keep fr.rsp (by omega) (by omega) (by omega)).trans s.ret⟩
  have hdest : ((fr.rsp - 0x218) + 0x180).toNat = _ := hsum 0x180 (by decide)
  exact (keep _ (by omega) (by omega) (by omega)).trans s.dest

theorem spillsWithin (fr : Activation) (depth : 0x218 ≤ fr.rsp.toNat) :
    RegionsWithin (spills (fr.rsp - 0x218)) (regions fr) := by
  intro r hr
  have hbase := stackOffset (fr := fr) depth (Nat.le_refl 0x218)
  change (fr.rsp - 0x218).toNat = fr.rsp.toNat - 0x218 at hbase
  have hs : ((fr.rsp - 0x218) + 0x188).toNat = (fr.rsp - 0x218).toNat + 0x188 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := fr.rsp.isLt; change _ + 392 < _; omega)]
    rfl
  refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;>
    simp only [spills, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl <;> dsimp <;> omega

end K256.Proofs.Generate.Generator.Multiply.AddFrame
