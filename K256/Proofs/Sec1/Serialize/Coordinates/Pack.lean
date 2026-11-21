import K256.Proofs.Sec1.Serialize.Coordinates.PackCall
import K256.Proofs.Sec1.Serialize.PackExecution

namespace K256.Proofs.Sec1.Serialize.Coordinates

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

def packWrites (base : BitVec 64) (k : Axis) : List MemoryRegion :=
  [⟨(base - 8).toNat, 8⟩, ⟨(base + k.offset).toNat, 32⟩]

theorem pack (k : Axis) {code : CodeMap} (cover : ∀ x ∈ fnCode, x ∈ code)
    {args : Values Value Reg.count} {m : Ram} {base : BitVec 64}
    {a : Vector (BitVec 64) 5} (rsp : args[4] = ⟨64, base⟩)
    (src : args[15] = ⟨64, base + 80⟩)
    (win : Writable code m (base - 8) 320) (words : WordsAt m (base + 80) 64 a) :
    ∃ (b : Values Value Reg.count) (m' : Ram), (program.sem (dialect code)).Reaches
        ⟨⟨k.packSite, args, m⟩, []⟩ ⟨⟨k.afterPack, b, m'⟩, []⟩ ∧
      b[4] = ⟨64, base⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = args[i]) ∧
      RamWriteFrame m m' (packWrites base k) ∧
      WordsAt m' (base + k.offset) 64 (packWords a) := by
  let sp := base - 8
  let m₁ := memStore m sp k.packReturn
  have slot : Writable code m sp 8 := win.sub (Nat.le_refl _) (by dsimp only [sp]; omega)
  have dest : Writable code m (base + k.offset) 32 :=
    win.of_offsets rfl (addr_sub _ _) (by cases k <;> decide)
  have readSrc : Readable m (base + 80) 40 :=
    win.readable.of_offsets rfl (addr_sub _ _) (by decide)
  obtain ⟨child, call, h4, h6, h7, preserved⟩ := packCall k cover rsp src slot
  have words₁ : WordsAt m₁ (base + 80) 64 a :=
    words.write_apart sp k.packReturn (RangeApart.of_offsets (addr_sub _ _) rfl (by decide))
  have hret : memLoad m₁ sp 64 = k.packReturn :=
    memLoad_memStore_same m sp k.packReturn (by decide) (by decide)
  have sep : sp.toNat + 8 ≤ (base + k.offset).toNat := by
    have h := toNat_of_offsets (a := base + k.offset) rfl (addr_sub base 8) win.readable.low
      (n := 32) (by cases k <;> decide)
    rw [h]
    apply Nat.add_le_add_left (k := sp.toNat)
    cases k <;> decide
  obtain ⟨out, run, tag, pop, _, regs, hf, hw⟩ :=
    packExecution (fun x hx => cover x (code_l1148d0 x hx)) h4 h6 h7
      (readSrc.memStore sp k.packReturn) (dest.memStore sp k.packReturn) words₁
      (slot.readable.memStore sp k.packReturn) hret (by cases k <;> decide) (Or.inl sep)
  have pushed : RamWriteFrame m m₁ (packWrites base k) := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _, ?_⟩
    have := slot.readable.low
    change sp.toNat + 8 ≤ 2 ^ 64
    omega
  refine ⟨out.values, out.store, reaches_call call run tag, ?_, ?_, pushed.trans hf ?_, hw⟩
  · simpa only [BitVec.sub_add_cancel] using pop
  · intro i hi
    apply Eq.trans (regs i ?_) (preserved i hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  · intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩

end K256.Proofs.Sec1.Serialize.Coordinates
