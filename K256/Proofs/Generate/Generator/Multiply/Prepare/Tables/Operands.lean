import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Blocks
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine

abbrev entryOff (first : Bool) (i : Nat) := (if first then 0x850 else 0x490) + 120*i
abbrev baseOff (first : Bool) : Nat := if first then 0x328 else 0xc10
abbrev ptr (q : BitVec 64) (k : Nat) := q + BitVec.ofNat 64 k

theorem ptrNat {q : BitVec 64} (high : q.toNat + 3256 ≤ 2^32) {k : Nat} (hk : k ≤ 3256) :
    (ptr q k).toNat = q.toNat + k := by
  simp only [ptr,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a := k) (b := 2^64) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

def copyWrites (q : BitVec 64) (k : Nat) : List MemoryRegion :=
  [⟨q.toNat + 0x418,120⟩,⟨q.toNat + k,120⟩,⟨q.toNat + 0x128,120⟩,⟨q.toNat + 0x1d0,120⟩]

theorem copyRecord {m : Ram} {p : Projective} {src dst : BitVec 64}
    (stored : p.Stored m src) : p.Stored (memCopy m dst src 120) dst := by
  simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using
    (Projective.Stored.memCopy (src := src) (dst := dst) (off := 0)
      (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using stored) (by decide) (by decide : 0+120 ≤ 120))

private theorem keepRecord {m : Ram} {p : Projective} {at_ src dst : BitVec 64}
    (stored : p.Stored m at_) (ah : at_.toNat + 120 ≤ 2^64) (dh : dst.toNat + 120 ≤ 2^64)
    (apart : at_.toNat + 120 ≤ dst.toNat ∨ dst.toNat + 120 ≤ at_.toNat) :
    p.Stored (memCopy m dst src 120) at_ := by
  let writes : List MemoryRegion := [⟨dst.toNat,120⟩]
  have frame := Sec1.Wrapper.Copy.memCopy_frame (src := src) (RamWriteFrame.refl m writes)
    (show InRegions writes dst 120 from ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,dh⟩)
  exact stored.of_frame frame ⟨ah,fun _ h => List.mem_singleton.mp h ▸ apart⟩

theorem copied (first : Bool) (i : Fin 7) {m : Ram} {q : BitVec 64} {p t : Projective}
    (high : q.toNat + 3256 ≤ 2^32) (base : p.Stored m (q + baseOffset first))
    (prev : t.Stored m (if i.val = 0 then q + baseOffset first else q+0x1d0)) :
    let n := copyOperands first i q m
    p.Stored n (q+0x1d0) ∧ t.Stored n (q+0x128) ∧
      t.Stored n (ptr q (entryOff first i)) ∧ RamWriteFrame m n (copyWrites q (entryOff first i)) := by
  let k := entryOff first i
  have small := i.isLt
  have bounds : 0x490 ≤ k ∧ k+120 ≤ 0xc10 := by cases first <;> dsimp [k,entryOff] <;> omega
  let b := q + baseOffset first
  let e := ptr q k
  let u := q+0x418
  let w := q+0x1d0
  let v := q+0x128
  have en : e.toNat = q.toNat+k := ptrNat high (by omega)
  have un : u.toNat = q.toNat+0x418 := ptrNat high (by decide)
  have wn : w.toNat = q.toNat+0x1d0 := ptrNat high (by decide)
  have vn : v.toNat = q.toNat+0x128 := ptrNat high (by decide)
  have bn : b.toNat = q.toNat+baseOff first := by cases first <;> exact ptrNat high (by decide)
  have ba : (baseOff first = 0x328 ∨ baseOff first = 0xc10) := by cases first <;> decide
  let stage := if i.val = 0 then memCopy m e b 120 else memCopy (memCopy m u w 120) e u 120
  let source := if i.val = 0 then b else e
  let rs := copyWrites q k
  have inside (x : BitVec 64) (hx : x = u ∨ x = e ∨ x = v ∨ x = w) : InRegions rs x 120 := by
    rcases hx with rfl|rfl|rfl|rfl
    · exact ⟨_,.head _,by change q.toNat+1048 ≤ u.toNat ∧ _; rw [un]; exact ⟨by omega,Nat.le_refl _,by omega⟩⟩
    · exact ⟨_,.tail _ (.head _),by change q.toNat+k ≤ e.toNat ∧ _; rw [en]; exact ⟨by omega,Nat.le_refl _,by omega⟩⟩
    · exact ⟨_,.tail _ (.tail _ (.head _)),by change q.toNat+296 ≤ v.toNat ∧ _; rw [vn]; exact ⟨by omega,Nat.le_refl _,by omega⟩⟩
    · exact ⟨_,.tail _ (.tail _ (.tail _ (.head _))),by change q.toNat+464 ≤ w.toNat ∧ _; rw [wn]; exact ⟨by omega,Nat.le_refl _,by omega⟩⟩
  have step {j : Ram} {x y : BitVec 64} (f : RamWriteFrame m j rs) (hx : x = u ∨ x = e ∨ x = v ∨ x = w) :
      RamWriteFrame m (memCopy j x y 120) rs := Sec1.Wrapper.Copy.memCopy_frame f (inside x hx)
  have staged : t.Stored stage e ∧ t.Stored stage source ∧ p.Stored stage b ∧ RamWriteFrame m stage rs := by
    by_cases z : i.val = 0
    · simp only [stage,source,z,ite_true]
      change t.Stored m (if i.val = 0 then b else w) at prev
      rw [ite_eq_left z] at prev
      exact ⟨copyRecord prev,keepRecord prev (by omega) (by omega) (by omega),
        keepRecord base (by change b.toNat + 120 ≤ _; omega) (by omega) (by change b.toNat + 120 ≤ _ ∨ _ ≤ b.toNat; omega),
        step (.refl ..) (by simp)⟩
    · simp only [stage,source,z,ite_false]
      change t.Stored m (if i.val = 0 then b else w) at prev
      rw [ite_eq_right z] at prev
      have ts : t.Stored (memCopy (memCopy m u w 120) e u 120) e := copyRecord (copyRecord prev)
      have ps : p.Stored (memCopy m u w 120) b := keepRecord base (by omega) (by omega) (by omega)
      exact ⟨ts,ts,keepRecord ps (by omega) (by omega) (by omega),
        step (step (.refl ..) (by simp)) (by simp)⟩
  obtain ⟨atE,atSrc,atB,frame⟩ := staged
  have pv : p.Stored (memCopy stage v source 120) b := keepRecord atB (by omega) (by omega) (by omega)
  have ev : t.Stored (memCopy stage v source 120) e := keepRecord atE (by omega) (by omega) (by omega)
  have tv : t.Stored (memCopy stage v source 120) v := copyRecord atSrc
  let n := memCopy (memCopy stage v source 120) w b 120
  change p.Stored n w ∧ t.Stored n v ∧ t.Stored n e ∧ RamWriteFrame m n rs
  exact ⟨copyRecord pv,keepRecord (dst := w) tv (by omega) (by omega) (by omega),
    keepRecord (dst := w) ev (by omega) (by omega) (by omega),step (x := w) (step (x := v) frame (by simp)) (by simp)⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
