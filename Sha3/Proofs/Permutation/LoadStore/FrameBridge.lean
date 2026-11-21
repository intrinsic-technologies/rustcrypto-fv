import Sha3.Proofs.Permutation.LoadStore.Entry

namespace X86Proofs

open X86 X86.Machine X86.UserProcess Prelude Sha3.Spec.Program

theorem CodeIn.of_memoryWriteFrame {s t : RamState} {code : CodeMap}
    {regions : Vector Prelude.MemoryRegion n}
    (hcode : CodeIn code s) (hframe : MemoryWriteFrame s t regions)
    (havoid : ∀ region ∈ regions, ∀ x ∈ code, ¬ region.Contains x.1.toNat) :
    CodeIn code t := by
  intro x hx
  refine ⟨(hcode x hx).1, ?_⟩
  rw [hframe x.1 (fun region hr ↦ havoid region hr x hx)]
  exact (hcode x hx).2

end X86Proofs

namespace Sha3.Proofs.Permutation

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {copy : Copy}

theorem pushSlot_savedRegisters (initial : RamState) (i : Fin 6) :
    pushSlot initial (i.rev.val + 1) =
      frameBase initial + BitVec.ofNat 64 (216 + 8 * i.val) := by
  finite_cases i <;>
    simp only [pushSlot, frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.add_right_inj] <;> decide +kernel

theorem pushReg_savedRegisters (initial : RamState) (i : Fin 6) :
    (Operand.reg ((pushReg i.rev).setWidth 5) : Operand 64).read initial =
      initial.regValue savedRegisters[i] := by
  finite_cases i <;> rfl

theorem PushProgress.savedRegisters {initial s : RamState} (hs : PushProgress copy initial 6 s)
    (i : Fin 6) :
    (Operand.mem (frameBase initial + BitVec.ofNat 64 (216 + 8 * i.val)) : Operand 64).read s =
      initial.regValue savedRegisters[i] := by
  rw [← pushSlot_savedRegisters]
  exact (hs.saved i.rev i.rev.isLt).trans (pushReg_savedRegisters initial i)

theorem PushProgress.memoryWriteFrame {initial s : RamState} {k : Nat}
    (hs : PushProgress copy initial k s) : MemoryWriteFrame initial s (writeRegions initial) := by
  intro address hout
  apply hs.memory address
  intro region hregion hcontains
  have hr : region = ⟨(frameBase initial).toNat, frameBytes⟩ := by simpa using hregion
  subst region
  exact hout _ (by simp [writeRegions]) hcontains

theorem read_mem_of_memoryWriteFrame {s t : RamState} {base addr : BitVec 64}
    {size n : Nat}
    (hframe : MemoryWriteFrame s t #v[⟨base.toNat, size⟩])
    (hap : RangeApart base size addr (n / 8)) :
    (Operand.mem addr : Operand n).read t = (Operand.mem addr : Operand n).read s := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  apply hframe
  intro region hregion hcontains
  have hr : region = ⟨base.toNat, size⟩ := by simpa using hregion
  subst region
  obtain ⟨hlo, hhi⟩ := hcontains
  let address := addr + BitVec.ofNat 64 j
  change base.toNat ≤ address.toNat at hlo
  change address.toNat < base.toNat + size at hhi
  let i := address.toNat - base.toNat
  have hi : i < size := by dsimp [i]; omega
  have he : base + BitVec.ofNat 64 i = address := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := address.isLt
    dsimp [i]
    omega
  exact hap i hi j hj he

theorem pushCode_subset_programImage (copy : Copy) :
    ∀ x ∈ codeRange (entryAddress copy) pushBytes, x ∈ Extracted.programImage := by
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
  exact imageSections_mem_toCodeMap_of_fetchByte (pushBytes_fetch copy i)

theorem pushes_advance_program (copy : Copy) [Bindings] (boundary : ReturnBoundary)
    (hboundary : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary 6 (EntryStackPre copy) Extracted.programImage
      (fun initial s ↦ PushProgress copy initial 6 s) := by
  intro initial hready hcode hp
  obtain ⟨s, hrun, hr, _, hs⟩ := pushes_advance copy boundary hboundary initial hready
    (hcode.mono (pushCode_subset_programImage copy)) hp
  refine ⟨s, hrun, hr, hcode.of_memoryWriteFrame hs.memory ?_, hs⟩
  intro region hregion x hx hcontains
  have he : region = ⟨(frameBase initial).toNat, frameBytes⟩ := by simpa using hregion
  subst region
  apply hp.avoid x.1 ?_ (.inl ⟨x.2, hx⟩)
  have hb : (frameBase initial).toNat = (initial.regValue .rsp).toNat - frameBytes :=
    stack_sub_toNat hp.stack.2.2.1 (Nat.le_refl frameBytes)
  have hn := hp.stack.2.2.1
  change frameBytes ≤ (initial.regValue .rsp).toNat at hn
  change (initial.regValue .rsp).toNat - frameBytes ≤ x.1.toNat ∧
    x.1.toNat < (initial.regValue .rsp).toNat - frameBytes +
      ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - frameBytes))
  obtain ⟨hl, hh⟩ := hcontains
  rw [hb] at hl hh
  change (initial.regValue .rsp).toNat - frameBytes ≤ x.1.toNat at hl
  change x.1.toNat < (initial.regValue .rsp).toNat - frameBytes + frameBytes at hh
  constructor <;> omega

end Sha3.Proofs.Permutation
