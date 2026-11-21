import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Eval
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Sec1.Parser.Frame

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Sec1.LIR

def savedRegistersMemory (mem : Ram) (sp : BitVec 64) (args : Values Value Reg.count) : Ram :=
  let m₁ := memStore mem (sp - 8) (args[15].get 64)
  let m₂ := memStore m₁ (sp - 16) (args[14].get 64)
  let m₃ := memStore m₂ (sp - 24) (args[12].get 64)
  memStore m₃ (sp - 32) (args[3].get 64)

theorem savedRegistersMemory_frame {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (args : Values Value Reg.count) {regions : List Prelude.MemoryRegion}
    (writable : Writable code mem (sp - 32) 32) (included : InRegions regions (sp - 32) 32) :
    RamWriteFrame mem (savedRegistersMemory mem sp args) regions := by
  obtain ⟨region, member, bounds⟩ := included
  have inside (off : BitVec 64) (fits : (0 - off - (0 - 32)).toNat + 8 ≤ 32) :
      InRegions regions (sp - off) 8 := by
    refine ⟨region, member, ?_⟩
    have addr := toNat_of_offsets (addr_sub sp off) (addr_sub sp 32) writable.readable.low fits
    obtain ⟨start, stop, limit⟩ := bounds
    exact ⟨by omega, by omega, by omega⟩
  exact ((((RamWriteFrame.refl mem regions).memStore (args[15].get 64)
    (inside 8 (by decide))).memStore (args[14].get 64)
    (inside 16 (by decide))).memStore (args[12].get 64)
    (inside 24 (by decide))).memStore (args[3].get 64) (inside 32 (by decide))

theorem savedRegistersMemory_load (mem : Ram) (sp : BitVec 64) (args : Values Value Reg.count) :
    memLoad (savedRegistersMemory mem sp args) (sp - 32) 64 = args[3].get 64 ∧
    memLoad (savedRegistersMemory mem sp args) (sp - 24) 64 = args[12].get 64 ∧
    memLoad (savedRegistersMemory mem sp args) (sp - 16) 64 = args[14].get 64 ∧
    memLoad (savedRegistersMemory mem sp args) (sp - 8) 64 = args[15].get 64 ∧
    memLoad (savedRegistersMemory mem sp args) sp 64 = memLoad mem sp 64 := by
  have apart {a b : BitVec 64}
      (forward : 8 ≤ (a - b).toNat) (back : 8 ≤ (b - a).toNat) :
      RangeApart (sp - a) 8 (sp - b) 8 := by
    apply RangeApart.of_offsets (addr_sub sp a) (addr_sub sp b)
    rw [show 0 - b - (0 - a) = a - b by bv_omega, show 0 - a - (0 - b) = b - a by bv_omega]
    exact ⟨forward, back⟩
  have retApart (a : BitVec 64) (forward : 8 ≤ a.toNat) (back : 8 ≤ (0 - a).toNat) :
      RangeApart (sp - a) 8 sp 8 :=
    RangeApart.of_offsets (addr_sub sp a) (addr_self sp) ⟨by
      rwa [show 0 - (0 - a) = a by bv_omega], by
      rwa [show 0 - a - 0 = 0 - a by bv_omega]⟩
  dsimp only [savedRegistersMemory]
  refine ⟨memLoad_memStore_same _ _ _ (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apart (by decide) (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apart (by decide) (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (apart (by decide) (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apart (by decide) (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (apart (by decide) (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (apart (by decide) (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (retApart _ (by decide) (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (retApart _ (by decide) (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (retApart _ (by decide) (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (retApart _ (by decide) (by decide))]

theorem entryBlock {code : CodeMap} {args : Values Value Reg.count} {mem : Ram} {sp len : BitVec 64}
    (rsp : args[4].get 64 = sp) (rdx : args[2].get 64 = len)
    (writable : Writable code mem (sp - 32) 32)
    (included : ∀ x ∈ codeRange 0x106390 bytes_l106390, x ∈ code) :
    ∃ next : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l106390, args, mem⟩ =
        (if len = 0 then .jump ⟨.l106560, next, savedRegistersMemory mem sp args⟩
         else .jump ⟨.l1063a7, next, savedRegistersMemory mem sp args⟩) ∧
      next[4] = ⟨64, sp - 344⟩ ∧
      ∀ i : Fin Reg.count,
        i.val ∈ [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22, 39, 50, 51] →
          next[i] = args[i] := by
  let m₁ := memStore mem (sp - 8) (args[15].get 64)
  let m₂ := memStore m₁ (sp - 16) (args[14].get 64)
  let m₃ := memStore m₂ (sp - 24) (args[12].get 64)
  have slot (off : BitVec 64) (inside : (32 - off).toNat + 8 ≤ 32) :
      Writable code mem (sp - off) 8 :=
    writable.of_offsets (addr_sub sp off) (addr_sub sp 32)
      (by rwa [show 0 - off - (0 - 32) = 32 - off by bv_omega])
  have h₁ : StoreOk code mem (sp - 8) 8 0x106390 2 :=
    ParseSignature.storeOk_of_codeRange (off := 0) (slot 8 (by decide)) included (by decide)
  have h₂ : StoreOk code m₁ (sp - 16) 8 0x106392 2 :=
    ParseSignature.storeOk_of_codeRange (off := 2)
      ((slot 16 (by decide)).memStore (sp - 8) (args[15].get 64)) included (by decide)
  have h₃ : StoreOk code m₂ (sp - 24) 8 0x106394 2 :=
    ParseSignature.storeOk_of_codeRange (off := 4)
      (((slot 24 (by decide)).memStore (sp - 8) (args[15].get 64)).memStore
        (sp - 16) (args[14].get 64)) included (by decide)
  have h₄ : StoreOk code m₃ (sp - 32) 8 0x106396 1 :=
    ParseSignature.storeOk_of_codeRange (off := 6)
      ((((slot 32 (by decide)).memStore (sp - 8) (args[15].get 64)).memStore
        (sp - 16) (args[14].get 64)).memStore (sp - 24) (args[12].get 64)) included (by decide)
  dsimp only [m₁, m₂, m₃] at h₂ h₃ h₄
  refine ⟨?_, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [rsp, rdx, h₁, h₂, h₃, h₄,
      testFlags, BitVec.and_self, Option.getD_some, beq_iff_eq, ↓reduceIte]
    by_cases empty : len = 0
    · simp only [ite_eq_left empty] <;> rfl
    · simp only [ite_eq_right empty] <;> rfl
  case post =>
    refine ⟨rfl, ?_⟩
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Sec1.Parser.Frame
