import K256.Proofs.Common.Refine.Simulation
import K256.Proofs.Common.Refine.Lemma.Layout
import K256.Proofs.Common.Refine.Lemma.Store
import K256.Proofs.Common.Refine.Lemma.Region
import K256.Proofs.Common.Refine.Lemma.Frame
import K256.Proofs.Common.Refine.Lemma.SysVEntry
import Prelude.Execution.CallingConvention

namespace K256.Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift Prelude

section Layout

variable {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat} {results : Nat}
  {P : Program UOp ULabel usig results} {D : Dialect UOp UValue UStore} {lifted : Lifted}
  {Ctx : Type}
  {code : CodeMap}

theorem Layout.machine [Bindings] {L : Layout P D lifted Ctx} {code : CodeMap} {c₀ : Ctx}
    {boundary : ReturnBoundary}
    (hlifted : Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code))
      (Lift.Rel code lifted) (Lift.RetRel code lifted))
    (h : ∀ label, L.BlockSimulation code label) :
    Simulation (machineAnyReturn boundary) (P.sem D)
      (fun u s => ∃ l, L.StateRel code c₀ u l ∧ Lift.Rel code lifted l s)
      (fun uo t => ∃ lo, L.RetRel code c₀ uo lo ∧ Lift.RetRel code lifted lo t) :=
  hlifted.trans (L.simulation code c₀ h)

section Run

variable {E : lifted.Location → Prop}
  {fin : Transfer Value Ram lifted.Label signature Reg.count → Prop}

theorem Ahead.here {l : lifted.Location} (h : E l) : Ahead lifted code E l := ⟨l, .refl l, h⟩

theorem Ahead.of_step {l : lifted.Location}
    (hfin : ∀ l', fin (lifted.program.runBlock (dialect code) l') → E l')
    (h : Onward lifted code E fin (lifted.program.runBlock (dialect code) l)) :
    Ahead lifted code E l := by
  cases hs : lifted.program.runBlock (dialect code) l with
  | jump l' =>
    rw [hs] at h
    obtain ⟨l'', hr, he⟩ := h
    exact ⟨l'', .jump hs hr, he⟩
  | call l' fr => exact ⟨l, .refl l, hfin l (by rw [hs]; rw [hs] at h; exact h)⟩
  | returned o => exact ⟨l, .refl l, hfin l (by rw [hs]; rw [hs] at h; exact h)⟩
  | stuck => exact ⟨l, .refl l, hfin l (by rw [hs]; rw [hs] at h; exact h)⟩

theorem Ahead.of_step_jump {l : lifted.Location}
    (h : Onward lifted code E (fun _ => False) (lifted.program.runBlock (dialect code) l)) :
    Ahead lifted code E l :=
  Ahead.of_step (fun _ h => h.elim) h

theorem Ahead.of_step_call {Q : lifted.Location → lifted.StackFrame → Prop} {l : lifted.Location}
    (h : Onward lifted code (fun l' => CallTo Q (lifted.program.runBlock (dialect code) l'))
      (CallTo Q)
      (lifted.program.runBlock (dialect code) l)) :
    Ahead lifted code (fun l' => CallTo Q (lifted.program.runBlock (dialect code) l')) l :=
  Ahead.of_step (fun _ h => h) h

theorem Ahead.of_step_ret {Q : Output Value Ram Reg.count → Prop} {l : lifted.Location}
    (h : Onward lifted code (fun l' => ReturnOf Q (lifted.program.runBlock (dialect code) l'))
      (ReturnOf Q)
      (lifted.program.runBlock (dialect code) l)) :
    Ahead lifted code (fun l' => ReturnOf Q (lifted.program.runBlock (dialect code) l')) l :=
  Ahead.of_step (fun _ h => h) h

end Run

section MatchedBy

variable {L : Layout P D lifted Ctx} {c : Ctx} {l : lifted.Location}

theorem Layout.matches_jump {u : Location UValue UStore ULabel usig} :
    L.MatchedBy code c l (.jump u) = Ahead lifted code (L.Rel code c u) l := rfl

theorem Layout.matches_call {u : Location UValue UStore ULabel usig}
    {uf : CFG.StackFrame UValue ULabel usig results} :
    L.MatchedBy code c l (.call u uf) = Ahead lifted code (fun l' => CallTo (fun l'' lf =>
      ∃ c', L.Rel code c' u l'' ∧ L.Resumes code c' c uf lf)
        (lifted.program.runBlock (dialect code) l')) l :=
  rfl

theorem Layout.matches_returned {uo : Output UValue UStore results} :
    L.MatchedBy code c l (.returned uo) =
      Ahead lifted code
        (fun l' => ReturnOf (L.RetRel code c uo) (lifted.program.runBlock (dialect code) l')) l :=
  rfl

theorem Layout.matches_stuck : L.MatchedBy code c l .stuck := trivial

theorem Layout.matches_ite {b : Prop} [Decidable b]
    {x y : Transfer UValue UStore ULabel usig results}
    (hx : b → L.MatchedBy code c l x) (hy : ¬b → L.MatchedBy code c l y) :
    L.MatchedBy code c l (if b then x else y) := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

end MatchedBy

end Layout

theorem args_eq_vars (v : Vector Value Reg.count) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
      a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39
      a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 : Value,
      v = ⟨(a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 ::
        a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: a20 :: a21 :: a22 :: a23 :: a24 :: a25 :: a26 ::
        a27 :: a28 :: a29 :: a30 :: a31 :: a32 :: a33 :: a34 :: a35 :: a36 :: a37 :: a38 :: a39 ::
        a40 :: a41 :: a42 :: a43 :: a44 :: a45 :: a46 :: a47 :: a48 :: a49 :: a50 :: a51 :: a52 ::
        []).toArray, rfl⟩ := by
  obtain ⟨⟨l⟩, hl⟩ := v
  match l, hl with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 ::
      a15 :: a16 :: a17 :: a18 :: a19 :: a20 :: a21 :: a22 :: a23 :: a24 :: a25 :: a26 :: a27 ::
      a28 :: a29 :: a30 :: a31 :: a32 :: a33 :: a34 :: a35 :: a36 :: a37 :: a38 :: a39 :: a40 ::
      a41 :: a42 :: a43 :: a44 :: a45 :: a46 :: a47 :: a48 :: a49 :: a50 :: a51 :: a52 :: [], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
      a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31,
      a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47,
      a48, a49, a50, a51, a52, rfl⟩

@[elab_as_elim] theorem args_cases {motive : Vector Value Reg.count → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
      a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46
      a47 a48 a49 a50 a51 a52 : Value,
      motive ⟨(a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 ::
        a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: a20 :: a21 :: a22 :: a23 :: a24 :: a25 ::
        a26 :: a27 :: a28 :: a29 :: a30 :: a31 :: a32 :: a33 :: a34 :: a35 :: a36 :: a37 :: a38 ::
        a39 :: a40 :: a41 :: a42 :: a43 :: a44 :: a45 :: a46 :: a47 :: a48 :: a49 :: a50 :: a51 ::
        a52 :: []).toArray, rfl⟩)
    (v : Vector Value Reg.count) : motive v := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31,
    a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47,
    a48, a49, a50, a51, a52, rfl⟩ := args_eq_vars v
  exact h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _

theorem sysVCalleeReturn_calleeSaved {σ : Type} {initial final : X86.State σ} {ret : BitVec 64}
    (h : Prelude.Execution.CallingConvention.SysVCalleeReturn initial final ret) :
    ∀ r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List Syntax.Reg),
      final.regValue r = initial.regValue r := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem sub_sub_sub_left (x c d : BitVec 64) : x - c - (x - d) = d - c := by bv_omega
theorem add_sub_sub_left (x c d : BitVec 64) : x + c - (x - d) = c + d := by bv_omega
theorem sub_sub_add_left (x c d : BitVec 64) : x - c - (x + d) = 0 - c - d := by bv_omega
theorem sub_sub_self_left (x d : BitVec 64) : x - (x - d) = d := by bv_omega
theorem sub_add_self_left (x d : BitVec 64) : x - (x + d) = 0 - d := by bv_omega
theorem add_sub_self_right (x c : BitVec 64) : x + c - x = c := by bv_omega
theorem sub_sub_self_right (x c : BitVec 64) : x - c - x = 0 - c := by bv_omega

theorem addr_lit (c : BitVec 64) : c = 0 + c := (BitVec.zero_add c).symm

theorem addr_eq_of_offsets {a b x c d : BitVec 64} (ha : a = x + c) (hb : b = x + d) (h : c = d) :
    a = b := by
  subst ha hb h
  rfl

theorem addr_add_of_offsets {a b x c d e : BitVec 64} (ha : a = x + c) (hb : b = x + d)
    (h : d - c = e) : b = a + e := by
  subst ha hb h
  bv_omega

theorem RangeApart.of_regions {a b r s x y c d e f : BitVec 64} {n k len₁ len₂ : Nat}
    (ha : a = x + c) (hr : r = x + d) (hb : b = y + e) (hs : s = y + f)
    (hlr : r.toNat + len₁ ≤ 2 ^ 32) (hls : s.toNat + len₂ ≤ 2 ^ 32)
    (hap : r.toNat + len₁ ≤ s.toNat ∨ s.toNat + len₂ ≤ r.toNat)
    (hin : (c - d).toNat + n ≤ len₁ ∧ (e - f).toNat + k ≤ len₂) : RangeApart a n b k := by
  have h1 := toNat_of_offsets ha hr hlr hin.1
  have h2 := toNat_of_offsets hb hs hls hin.2
  exact RangeApart.of_toNat (by omega) (by omega) (by omega)

theorem memLoad_memStore_eq (mem : Ram) {a b : BitVec 64} {n : Nat} (v : BitVec n) (hab : a = b)
    (h8 : n % 8 = 0) (h128 : n ≤ 128) : memLoad (memStore mem a v) b n = v := by
  subst hab
  exact memLoad_memStore_same mem a v h8 h128

section Access

variable {code : CodeMap} {o m : Ram} {a b : BitVec 64} {len n : Nat} {x c d : BitVec 64}

theorem StoreOk.of_region {p : BitVec 64} {codeLen : Nat} (h : Writable code m b len)
    (h₁ : b.toNat ≤ a.toNat) (h₂ : a.toNat + n ≤ b.toNat + len)
    (hap : RangeApart a n p codeLen) : StoreOk code m a n p codeLen :=
  let h' := h.sub h₁ h₂
  ⟨h'.readable.low, h'.readable.present, h'.tables, hap, h'.notCode⟩

private theorem bounds_of_offsets' (hlow : b.toNat + len ≤ 2 ^ 32) (ha : a = x + c)
    (hb : b = x + d) (h : (c - d).toNat + n ≤ len) :
    b.toNat ≤ a.toNat ∧ a.toNat + n ≤ b.toNat + len := by
  rw [toNat_of_offsets ha hb hlow h]
  omega

theorem StoreOk.of_offsets {p : BitVec 64} {codeLen : Nat} (h : Writable code m b len)
    (ha : a = x + c) (hb : b = x + d) (hin : (c - d).toNat + n ≤ len)
    (hap : RangeApart a n p codeLen) : StoreOk code m a n p codeLen :=
  have hb' := bounds_of_offsets' h.readable.low ha hb hin
  StoreOk.of_region h hb'.1 hb'.2 hap

end Access

namespace WordsAt

variable {m o : Ram} {base : BitVec 64} {w n : Nat} {vals : Vector (BitVec w) n}

private theorem mul_add_le' {k i n : Nat} (hi : i < n) : k * i + k ≤ k * n := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

private theorem toNat_wordAddr' {i : Nat} (hi : i < n) (hw0 : 0 < w / 8)
    (hn : base.toNat + w / 8 * n ≤ 2 ^ 64) :
    (wordAddr base w i).toNat = base.toNat + w / 8 * i := by
  have hmi : w / 8 * i + w / 8 ≤ w / 8 * n := mul_add_le' hi
  simp only [wordAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := w / 8 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem from_succ {k : Nat} (hk : k < n) (h : memLoad m (wordAddr base w k) w = vals[k])
    (hs : ∀ i (hi : i < n), k + 1 ≤ i → memLoad m (wordAddr base w i) w = vals[i]) :
    ∀ i (hi : i < n), k ≤ i → memLoad m (wordAddr base w i) w = vals[i] := by
  intro i hi hki
  rcases Nat.eq_or_lt_of_le hki with rfl | hlt
  · exact h
  · exact hs i hi hlt

theorem from_end : ∀ i (hi : i < n), n ≤ i → memLoad m (wordAddr base w i) w = vals[i] :=
  fun _ hi h => absurd hi (Nat.not_lt.mpr h)

theorem of_from (h : ∀ i (hi : i < n), 0 ≤ i → memLoad m (wordAddr base w i) w = vals[i]) :
    WordsAt m base w vals := fun i hi => h i hi (Nat.zero_le i)

theorem of_frame (h : WordsAt o base w vals) {regions : List MemoryRegion}
    (hf : RamWriteFrame o m regions) (hw0 : 0 < w / 8) (hout : Outside regions base (w / 8 * n)) :
    WordsAt m base w vals := by
  intro i hi
  have hmi := mul_add_le' (k := w / 8) hi
  rw [hf.memLoad_eq ⟨?_, fun r hr => ?_⟩]
  · exact h i hi
  · have := hout.1
    rw [toNat_wordAddr' hi hw0 (by omega)]; omega
  · have := hout.1
    rw [toNat_wordAddr' hi hw0 (by omega)]
    rcases hout.2 r hr with h' | h' <;> omega

end WordsAt

namespace Activation

variable {s : RamState} {stackBytes : Nat} {ret : BitVec 64}

theorem ofEntry_region_within (x : Nat) (hx : (ofEntry s stackBytes ret).region.Contains x) :
    (Stack.region s stackBytes).Contains x := by
  simp only [Activation.region, contains_iff, ofEntry_low_toNat] at hx
  rw [contains_iff]
  change (s.regValue .rsp).toNat - stackBytes ≤ x ∧
    x < (s.regValue .rsp).toNat - stackBytes +
      ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - stackBytes))
  change _ ≤ x ∧ x < _ + ((s.regValue .rsp).toNat - _) at hx
  omega

end Activation

section Region

variable {mem : Ram}

theorem readable_of_word64At {region : MemoryRegion} {value : BitVec 64}
    (h : region.Word64At mem value) (hbound : region.Bounded) :
    Readable mem (BitVec.ofNat 64 region.start) 8 := by
  have hlow : region.start + 8 < 2 ^ 32 := by
    have h8 : region.size = 8 := h.1.symm
    have : region.start + region.size < 2 ^ 32 := hbound
    omega
  refine ⟨?_, fun i hi => ?_⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [bytes_of_word64At h i hi]
    rfl

theorem WordsAt.of_word64At {start n : Nat} {vals : Vector (BitVec 64) n}
    (h : ∀ i (hi : i < n), (⟨start + 8 * i, 8⟩ : MemoryRegion).Word64At mem vals[i]) :
    WordsAt mem (BitVec.ofNat 64 start) 64 vals := by
  intro i hi
  have := memLoad_of_word64At (h i hi)
  rwa [BitVec.ofNat_add] at this

theorem Readable.of_word64At {start n : Nat} {vals : Nat → BitVec 64}
    (h : ∀ i < n, (⟨start + 8 * i, 8⟩ : MemoryRegion).Word64At mem (vals i))
    (hlow : start + 8 * n ≤ 2 ^ 32) :
    Readable mem (BitVec.ofNat 64 start) (8 * n) := by
  have hstart : (BitVec.ofNat 64 start).toNat = start := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by rw [hstart]; omega, fun j hj => ?_⟩
  have hb : mem[BitVec.ofNat 64 (start + 8 * (j / 8)) + BitVec.ofNat 64 (j % 8)]? = _ :=
    bytes_of_word64At (h (j / 8) (by omega)) (j % 8) (by omega)
  rw [← BitVec.ofNat_add, Nat.add_assoc, Nat.div_add_mod] at hb
  rw [← BitVec.ofNat_add, hb]
  rfl

theorem WordsAt.of_hasBytes {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes mem bytes) :
    WordsAt mem (BitVec.ofNat 64 region.start) 8
      (Vector.ofFn fun i : Fin bytes.size => bytes[i.val].toBitVec) := by
  intro i hi
  rw [Vector.getElem_ofFn, wordAddr, show 8 / 8 * i = i by omega,
    (Bytes.of_hasBytes h).loadByte i hi]
  simp only [hi, ↓reduceDIte]

theorem outside_of_within {n : Nat} {regions : Vector MemoryRegion n} {small : List MemoryRegion}
    (h : ∀ r ∈ small, ∃ r' ∈ regions, ∀ x, r.Contains x → r'.Contains x) :
    ∀ x, (∀ r ∈ regions, ¬ r.Contains x) → ∀ r ∈ small, ¬ r.Contains x := by
  intro x hx r hr hc
  obtain ⟨r', hr', hsub⟩ := h r hr
  exact hx r' hr' (hsub x hc)

end Region

end K256.Proofs.Refine
