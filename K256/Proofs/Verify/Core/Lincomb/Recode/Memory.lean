import K256.Proofs.Verify.Core.Lincomb.Interface
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

noncomputable abbrev machine := dialect Extracted.programImage

def IteratorAt (m : Ram) (ptr next : BitVec 64) (block : Nat) (lo hi : BitVec 64) : Prop :=
  WordsAt m ptr 64 (#v[next, 0, BitVec.ofNat 64 block, lo, hi] : Vector (BitVec 64) 5)

abbrev returnTo (label : Label) (pc : BitVec 64) :
    StackFrame Value Label signature Reg.count :=
  ⟨label, #v[], rfl, some ⟨64, pc⟩⟩

theorem resume (label : Label) (pc : BitVec 64) (out : Output Value Ram Reg.count) :
    (returnTo label pc).resume out = ⟨label, out.values, out.store⟩ := by
  change Location.mk label ((returnTo label pc).resume out).arguments out.store = _
  rw [ParseSignature.resume_arguments]

theorem jump {source target : Label} {a b : Registers} {m n : Ram}
    {out : Output Value Ram Reg.count}
    (step : program.runBlock machine ⟨source, a, m⟩ = .jump ⟨target, b, n⟩)
    (tail : program.Exec machine ⟨⟨target, b, n⟩, []⟩ out) :
    program.Exec machine ⟨⟨source, a, m⟩, []⟩ out :=
  .next (by simp only [Program.step, step, Transfer.next]) tail

theorem done {label : Label} {a : Registers} {m : Ram} {out : Output Value Ram Reg.count}
    (step : program.runBlock machine ⟨label, a, m⟩ = .returned out) :
    program.Exec machine ⟨⟨label, a, m⟩, []⟩ out :=
  .done (by simp only [Program.step, step, Transfer.next])

theorem storeGuard {mem : Ram} {addr base : BitVec 64} {size off len : Nat}
    {bytes : List UInt8} (writable : Writable Extracted.programImage mem addr size)
    (included : ∀ x ∈ codeRange base bytes, x ∈ fnCode) (within : off + len ≤ bytes.length) :
    StoreOk Extracted.programImage mem addr size (base + BitVec.ofNat 64 off) len :=
  ParseSignature.storeOk_of_codeRange writable
    (fun _ hx => Common.fnCode_subset_programImage _ (included _ hx)) within

theorem stackSlot {a : Registers} {m : Ram} {sp : BitVec 64} {depth : Nat}
    (entry : RoutineEntry a m sp depth) {off : BitVec 64} {len : Nat}
    (lower : off.toNat ≤ depth) (upper : len ≤ off.toNat) :
    Writable Extracted.programImage m (sp - off) len := by
  apply entry.stack.sub
  all_goals
    have room := entry.room
    have offNat : (sp - off).toNat = sp.toNat - off.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    have baseNat : (sp - BitVec.ofNat 64 depth).toNat = sp.toNat - depth := by
      have h := sp.isLt
      have hdepth : (BitVec.ofNat 64 depth).toNat = depth :=
        by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), hdepth]
    rw [offNat, baseNat]
    omega

theorem inScratch {sp : BitVec 64} {depth : Nat} {off : BitVec 64} {len : Nat}
    (room : depth ≤ sp.toNat) (lower : off.toNat ≤ depth) (upper : len ≤ off.toNat) :
    InRegion (scratch sp depth) (sp - off) len := by
  simp only [InRegion, scratch, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega : off.toNat ≤ sp.toNat))]
  have := sp.isLt
  omega

theorem outsideOne {rs : List MemoryRegion} {a : BitVec 64} {len : Nat}
    (outside : Outside rs a len) {i : Nat} (hi : i < len) :
    Outside rs (a + BitVec.ofNat 64 i) 1 := by
  have bound := outside.1
  have addr : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by omega : a.toNat + i < 2^64)]
  refine ⟨by rw [addr]; omega, fun r hr => ?_⟩
  rw [addr]
  rcases outside.2 r hr with h | h <;> omega

theorem digitBytes_of_frame {m m' : Ram} {dst : BitVec 64} {ds : List Int}
    {rs : List MemoryRegion} (frame : RamWriteFrame m m' rs) (apart : Outside rs dst 257)
    (h : DigitBytes m dst ds) : DigitBytes m' dst ds := by
  intro i
  exact (frame.memLoad_eq (outsideOne apart i.isLt)).trans (h i)

theorem digitBytes_append {m : Ram} {dst : BitVec 64} {ds : List Int} {d : Int}
    (h : DigitBytes m dst ds) (i : ds.length < 257) :
    DigitBytes (memStore m (dst + BitVec.ofNat 64 ds.length) (BitVec.ofInt 8 d)) dst (ds ++ [d]) := by
  intro ⟨j, hj⟩
  change memLoad _ (dst + BitVec.ofNat 64 j) 8 = BitVec.ofInt 8 ((ds ++ [d])[j]?.getD 0)
  by_cases he : j = ds.length
  · subst j
    rw [memLoad_memStore_same _ _ _ (by decide) (by decide), List.getElem?_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  · have apart : RangeApart (dst + BitVec.ofNat 64 ds.length) 1 (dst + BitVec.ofNat 64 j) 1 := by
      intro k hk l hl eq
      have hk' : k = 0 := by omega
      have hl' : l = 0 := by omega
      rw [hk', hl'] at eq
      have eq₀ : BitVec.ofNat 64 ds.length = BitVec.ofNat 64 j := by bv_omega
      have eq' := congrArg BitVec.toNat eq₀
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := ds.length) (by omega : ds.length < 2^64),
        Nat.mod_eq_of_lt (a := j) (by omega : j < 2^64)] at eq'
      exact he eq'.symm
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ apart, h ⟨j, hj⟩]
    by_cases hj' : j < ds.length
    · rw [List.getElem?_append_left hj']
    · have hn : ds.length ≤ j := by omega
      have hn' : (ds ++ [d]).length ≤ j := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      change BitVec.ofInt 8 (ds[j]?.getD 0) = _
      rw [List.getElem?_eq_none hn, List.getElem?_eq_none hn']

theorem digitBytes_append_zero {m : Ram} {dst : BitVec 64} {ds : List Int} {k : Nat}
    (h : DigitBytes m dst ds) : DigitBytes m dst (ds ++ List.replicate k 0) := by
  intro i
  rw [h i]
  by_cases hi : i.val < ds.length
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_append_right (by omega)]
    by_cases hj : i.val - ds.length < k
    · simp only [List.getElem?_replicate, hj, ite_true, Option.getD_some, Option.getD_none]
    · simp only [List.getElem?_replicate, hj, ite_false]

end K256.Proofs.Verify.Core.Lincomb.Recode
