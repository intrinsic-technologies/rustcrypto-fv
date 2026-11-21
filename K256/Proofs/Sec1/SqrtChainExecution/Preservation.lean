import K256.Proofs.Sec1.SqrtChainExecution.Stages
import K256.Proofs.Sec1.SqrtCounted.Frame

namespace K256.Proofs.Sec1.SqrtChainExecution

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine Common.Field

def savedReg (i : Fin 14) (r : Fin Reg.count) : Bool :=
  r.val ∈ [3,5,12,13,14,15] && !(i.val == 7 && r.val == 3) &&
    !(i.val ∈ [8,9] && r.val == 15)

private theorem recorded (i : Fin 14) (s : SavedLimb) (hs : s ∈ savedLimbs i) :
    match s.place with
    | .stack n => 80 ≤ n ∧ n ≤ 352
    | .reg r => savedReg i r = true := by
  let ok (s : SavedLimb) := match s.place with
    | .stack n => decide (80 ≤ n ∧ n ≤ 352)
    | .reg r => savedReg i r
  have h : ∀ j : Fin 14, (savedLimbs j).all (fun s => match s.place with
      | .stack n => decide (80 ≤ n ∧ n ≤ 352) | .reg r => savedReg j r) = true := by decide +kernel
  have check : ok s = true := List.all_eq_true.mp (h i) s hs
  cases he : s.place with
  | stack n => exact of_decide_eq_true (by simpa only [ok,he] using check)
  | reg r => simpa only [ok,he] using check

private theorem all_map {code : CodeMap} {a b : Values Value Reg.count} {m n : Ram}
    {f : α → Atom} (l : List α)
    (h : ∀ x ∈ l, (f x).Holds code a m → (f x).Holds code b n) :
    Atom.All code a m (l.map f) → Atom.All code b n (l.map f) := by
  induction l with
  | nil => exact id
  | cons x l ih =>
    rintro ⟨hx,hl⟩
    exact ⟨h x List.mem_cons_self hx, ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) hl⟩

theorem savedAtoms_of_eq {code : CodeMap} {a b : Values Value Reg.count} {m n : Ram}
    (i : Fin 14) (base : Word) (v : Limbs)
    (regs : ∀ r, savedReg i r = true → b[r] = a[r])
    (slots : ∀ k : Nat, 80 ≤ k → k ≤ 352 →
      memLoad n (base + BitVec.ofNat 64 k) 64 = memLoad m (base + BitVec.ofNat 64 k) 64)
    (before : Atom.All code a m (savedAtoms i base v)) : Atom.All code b n (savedAtoms i base v) := by
  obtain ⟨hl,h13⟩ := (Atom.all_append _ _).1 before
  apply (Atom.all_append _ _).2
  constructor
  · apply all_map (savedLimbs i) _ hl
    intro s hs hyp
    have valid := recorded i s hs
    cases he : s.place with
    | stack k =>
      rw [he] at valid
      simp only [he,Atom.Holds] at hyp ⊢
      exact (slots k valid.1 valid.2).trans hyp
    | reg r =>
      rw [he] at valid
      simp only [he,Atom.gpr,Atom.Holds] at hyp ⊢
      exact (regs r valid).trans hyp
  · by_cases hi : i.val = 13
    · simp only [hi, ite_true] at h13 ⊢
      exact ⟨(regs 12 (by simp only [savedReg, hi]; decide)).trans h13.1,trivial⟩
    · simp only [hi, ite_false, Atom.All]

theorem roundBounds {code : CodeMap} {fr : Activation} {args mem} (g : Geometry code fr)
    (frame : SqrtCounted.LoopFrame code args mem fr) :
    let base := fr.rsp - 440
    fr.low.toNat + 552 ≤ fr.rsp.toNat ∧ fr.rsp.toNat + 8 ≤ 2^32 ∧
    (base.toNat + 80 ≤ 0x100000 ∨ 0x12aa00 ≤ base.toNat - 112) := by
  intro base
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,rd,_,_,_,room,_,_⟩ := frame
  change Readable mem fr.rsp 8 at rd
  change fr.low.toNat + 552 ≤ fr.rsp.toNat at room
  have hb : base.toNat = fr.rsp.toNat - 440 :=
    BitVec.toNat_sub_of_le (by change 440 ≤ fr.rsp.toNat; omega)
  exact ⟨room,rd.low,by have := g.stackCode; omega⟩

theorem localData_of_round {code : CodeMap} {fr : Activation} {m n : Ram} {a : Limbs}
    (g : Geometry code fr) (room : fr.low.toNat+552 ≤ fr.rsp.toNat)
    (bound : fr.rsp.toNat + 8 ≤ 2^32) (source : WordsAt m fr.rsi 64 a) (rd : Readable m fr.rsi 40)
    (writes : RamWriteFrame fr.original m [fr.region,⟨fr.rdi.toNat,41⟩])
    (round : RamWriteFrame m n [Sqrt.roundStack (fr.rsp - 440)]) :
    (∀ k : Nat, 80 ≤ k → k ≤ 352 →
      memLoad n (fr.rsp - 440 + BitVec.ofNat 64 k) 64 =
      memLoad m (fr.rsp - 440 + BitVec.ofNat 64 k) 64) ∧
    WordsAt n fr.rsi 64 a ∧ RamWriteFrame fr.original n [fr.region,⟨fr.rdi.toNat,41⟩] := by
  let base := fr.rsp - 440
  have hb : base.toNat = fr.rsp.toNat - 440 :=
    BitVec.toNat_sub_of_le (by change 440 ≤ fr.rsp.toNat; omega)
  have hb' : (base - 112).toNat = fr.rsp.toNat - 552 := by
    rw [BitVec.toNat_sub_of_le (by change 112 ≤ base.toNat; omega),hb]
    change fr.rsp.toNat - 440 - 112 = fr.rsp.toNat - 552
    omega
  have apart := g.sourceStack
  refine ⟨?_,?_,?_⟩
  · intro k lo hi
    apply round.memLoad_eq
    have haddr : (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a := k) (by omega),Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_,?_⟩
    · change (base + BitVec.ofNat 64 k).toNat + 64 / 8 ≤ 2^64
      omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      right
      change (base - 112).toNat + 192 ≤ (base + BitVec.ofNat 64 k).toNat
      omega
  · intro i hi
    refine (round.memLoad_eq ?_).trans (source i hi)
    have rlow := rd.low
    have hx : (wordAddr fr.rsi 64 i).toNat = fr.rsi.toNat + 8*i := by
      unfold wordAddr
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      change (fr.rsi.toNat + (8*i) % 2^64) % 2^64 = _
      rw [Nat.mod_eq_of_lt (a := 8*i) (by omega),Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_,?_⟩
    · change (wordAddr fr.rsi 64 i).toNat + 8 ≤ 2^64
      omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      change (wordAddr fr.rsi 64 i).toNat + 8 ≤ (base - 112).toNat ∨
        (base - 112).toNat + 192 ≤ (wordAddr fr.rsi 64 i).toNat
      omega
  · apply writes.trans round
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region,List.mem_cons_self,?_,?_⟩
    · change fr.low.toNat ≤ (base - 112).toNat
      omega
    · change (base - 112).toNat + 192 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      omega

end K256.Proofs.Sec1.SqrtChainExecution
