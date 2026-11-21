import K256.Proofs.Generate.Generator.Multiply.Prepare.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Generate.Generator.Affine.Select.Setup
import K256.Proofs.Common.Image

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def setupMemory (m : Ram) (q : BitVec 64) : Ram :=
  memStore (memStore (memCopy m (q + 0x128) 0x203258 120) (q + 8) (66 : BitVec 64))
    (q + 0x38) (66 : BitVec 64)

private theorem copyIdentityGuard {m : Ram} {q : BitVec 64}
    (image : ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2)
    (dst : Writable Extracted.programImage m (q + 0x128) 120) :
    RepMovsOk Extracted.programImage m 0 0x203258 (q + 0x128) 15 8 0x11d634 3 := by
  have span (i : Nat) (hi : i < 120) :
      ∃ b, ((0x203258 : BitVec 64) + BitVec.ofNat 64 i, b) ∈ Extracted.programImage := by
    apply exists_mem_toCodeMap (s := rodataSection) (by simp [rodataSection, Extracted.programSections])
    · change 0x200000 ≤ ((0x203258 : BitVec 64) + BitVec.ofNat 64 i).toNat
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
      omega
    · change ((0x203258 : BitVec 64) + BitVec.ofNat 64 i).toNat < 0x200000 + Extracted.rodataBytes.size
      simp only [Common.rodataBytes_size, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
      omega
  obtain ⟨read, apart⟩ := Affine.readableCodeSpan span image (by decide) (by decide) dst (by decide)
  exact copyGuard read (by slot_guard using code_l11d620) apart

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem initializeAccumulator {a : Registers} {m : Ram} {q table : BitVec 64}
    (rsp : a[4].get 64 = q) (df : a[22].get 1 = 0)
    (stack : Writable Extracted.programImage m q 3256)
    (image : ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2)
    (widths : ParseSignature.ArgumentWidths a) (saved : SavedWidths a)
    (len₁ : memLoad m (q + 0x100) 64 = 1) (len₂ : memLoad m (q + 0x1a0) 64 = 1)
    (ptr : memLoad m (q + 0x1c0) 64 = table) (count : memLoad m (q + 0x60) 64 = 66) :
    ∃ b, Reaches .l11d620 a m .l11d6a6 b (setupMemory m q) ∧
      ParseSignature.ArgumentWidths b ∧ SavedWidths b ∧ b[5] = ⟨64,0⟩ ∧ b[12] = ⟨64,q+0x1d0⟩ ∧ b[13] = ⟨64,table⟩ ∧ b[15] = ⟨64,q+0x490⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i] := by
  have copy := copyIdentityGuard (q := q) image (by slot_state region)
  let m₁ := memCopy m (q + 0x128) 0x203258 120
  let m₂ := memStore m₁ (q + 8) (66 : BitVec 64)
  have one : memLoad m₁ (q + 0x100) 64 = 1 :=
    (memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (x := q) rfl rfl (by decide))).trans len₁
  have two : memLoad m₂ (q + 0x1a0) 64 = 1 := by
    dsimp only [m₂, m₁, memCopy]
    repeat rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (x := q) rfl rfl (by decide))]
    exact len₂
  have address : memLoad (setupMemory m q) (q + 0x1c0) 64 = table := by
    dsimp only [setupMemory, memCopy]
    repeat rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (x := q) rfl rfl (by decide))]
    exact ptr
  have copiedPtr : memLoad m₁ (q + 0x1c0) 64 = table :=
    (memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (x := q) rfl rfl (by decide))).trans ptr
  have capacity : memLoad (setupMemory m q) (q + 0x60) 64 = 66 := by
    dsimp only [setupMemory, memCopy]
    repeat rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (x := q) rfl rfl (by decide))]
    exact count
  have limit : memLoad (setupMemory m q) (q + 8) 64 = 66 := by
    unfold setupMemory
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _
      (RangeApart.of_offsets (x := q) rfl rfl (by decide)), memLoad_memStore_same _ _ _ rfl (by decide)]
  have stack₁ : Writable Extracted.programImage m₁ q 3256 := stack.memStore _ _
  have stack₂ : Writable Extracted.programImage m₂ q 3256 := stack₁.memStore _ _
  have ok (off : BitVec 64) (h : off.toNat + 8 ≤ 3256) : Readable m (q + off) 8 :=
    stack.readable.of_offsets rfl (addr_self q) (by change (off - 0).toNat + 8 ≤ 3256; rwa [show off - (0 : BitVec 64) = off by bv_omega])
  have l₁ := (ok 0x100 (by decide)).memStore (q + 0x128) (memLoad m 0x203258 960)
  have l₂ := ((ok 0x1a0 (by decide)).memStore (q + 0x128) (memLoad m 0x203258 960)).memStore (q + 8) (66 : BitVec 64)
  have l₃ (off : BitVec 64) (h : off.toNat + 8 ≤ 3256) : Readable (setupMemory m q) (q + off) 8 :=
    (((ok off h).memStore (q + 0x128) (memLoad m 0x203258 960)).memStore (q + 8) (66 : BitVec 64)).memStore (q + 0x38) _
  have load₁ : LoadOk m₁ (q + 0x100) 8 := LoadOk.of_region l₁ (Nat.le_refl _) (Nat.le_refl _)
  have load₂ : LoadOk m₂ (q + 0x1a0) 8 := LoadOk.of_region l₂ (Nat.le_refl _) (Nat.le_refl _)
  have load₃ (off : BitVec 64) (h : off.toNat + 8 ≤ 3256) : LoadOk (setupMemory m q) (q + off) 8 :=
    LoadOk.of_region (l₃ off h) (Nat.le_refl _) (Nat.le_refl _)
  have w₁ : Writable Extracted.programImage m₁ (q+8) 8 :=
    stack₁.of_offsets rfl (addr_self q) (by decide)
  have w₂ : Writable Extracted.programImage m₂ (q+0x38) 8 :=
    stack₂.of_offsets rfl (addr_self q) (by decide)
  have write₁ : StoreOk Extracted.programImage m₁ (q+8) 8 0x11d64a 5 := by
    exact ParseSignature.storeOk_of_codeRange (off := 0x2a) w₁
      (fun x hx => Common.fnCode_subset_programImage x (code_l11d620 x hx)) (by decide +kernel)
  have write₂ : StoreOk Extracted.programImage m₂ (q+0x38) 8 0x11d662 5 := by
    exact ParseSignature.storeOk_of_codeRange (off := 0x42) w₂
      (fun x hx => Common.fnCode_subset_programImage x (code_l11d620 x hx)) (by decide +kernel)
  have ptrOk := load₃ 0x1c0 (by decide)
  have capOk := load₃ 0x60 (by decide)
  have limOk := load₃ 8 (by decide)
  have capacityBranch (a : Registers) (n : Ram) (rsp : a[4].get 64 = q)
      (zero : a[5].get 64 = 0) (value : memLoad n (q + 0x60) 64 = 66)
      (ok : LoadOk n (q + 0x60) 8) :
      ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l11d690,a,n⟩ =
        .jump ⟨.l11d69b,b,n⟩ ∧ ∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,5,6,7,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
    refine ⟨?_, ?run, ?regs⟩
    case run => arithmetic_segment using code_l11d690 [rsp,zero,value,ok]
    case regs =>
      intro i hi
      obtain ⟨i,h⟩ := i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have limitBranch (a : Registers) (n : Ram) (rsp : a[4].get 64 = q)
      (zero : a[5].get 64 = 0) (value : memLoad n (q + 8) 64 = 66)
      (ok : LoadOk n (q + 8) 8) :
      ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l11d69b,a,n⟩ =
        .jump ⟨.l11d6a6,b,n⟩ ∧ ∀ i : Fin Reg.count, i.val ∈ [1,2,3,4,5,6,7,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
    refine ⟨?_, ?run, ?regs⟩
    case run => arithmetic_segment using code_l11d69b [rsp,zero,value,ok]
    case regs =>
      intro i hi
      obtain ⟨i,h⟩ := i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have init : program.runBlock (dialect Extracted.programImage) ⟨.l11d620,a,m⟩ =
      .jump ⟨.l11d690,?b₁,setupMemory m q⟩ := by
    arithmetic_segment using code_l11d620 [rsp, df, copy, one, two, address, copiedPtr, load₁,
      load₂, ptrOk, write₁, write₂, m₁, m₂, setupMemory, or_true]
  obtain ⟨b₂,first,keep₂⟩ := capacityBranch ?b₁ _ rsp rfl capacity capOk
  obtain ⟨b₃,second,keep₃⟩ := limitBranch b₂ _ ((congrArg (Value.get 64) (keep₂ 4 (by decide))).trans rsp)
    ((congrArg (Value.get 64) (keep₂ 5 (by decide))).trans rfl) limit limOk
  have keep (i : Fin Reg.count) (h : i.val ∈ [1,2,3,4,5,6,7,8,9,12,13,14,15,22,39,50,51]) :
      b₃[i] = (?b₁ : Registers)[i] := (keep₃ i h).trans (keep₂ i h)
  refine ⟨b₃, ?reaches, ?regs⟩
  case reaches =>
    refine Star.step (b := ⟨⟨.l11d690,?b₁,setupMemory m q⟩,[]⟩) ?_ (Star.step (b := ⟨⟨.l11d69b,b₂,setupMemory m q⟩,[]⟩) ?_ (Semantics.Reaches.single ?_))
    all_goals change program.step _ _ = _
    all_goals simp only [Program.step,init,first,second,Transfer.next]
  case regs =>
    refine ⟨?_,?_,keep 5 (by decide),keep 12 (by decide),keep 13 (by decide),keep 15 (by decide),?_⟩
    · rintro ⟨i,h⟩ hi
      have w := widths ⟨i,h⟩ hi
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rw [keep _ (by simp)] <;> first | rfl | exact w
    · rintro ⟨i,h⟩ hi
      have w := saved ⟨i,h⟩ hi
      simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rw [keep _ (by simp)] <;> first | rfl | exact w
    rintro ⟨i,h⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> exact keep _ (by simp)

end K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
