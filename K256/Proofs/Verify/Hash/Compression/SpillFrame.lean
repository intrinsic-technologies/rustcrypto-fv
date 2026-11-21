import K256.Proofs.Verify.Hash.Compression.Spills
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Verify.Hash.Compression.Values
open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine Prelude

def spillRegions (sp : BitVec 64) : List MemoryRegion :=
  [⟨sp.toNat, 192⟩, ⟨sp.toNat + 208, 80⟩]

theorem spillRun_frame (ctx : ValueContext) (ops : List Op) (s : Compression.Values) (m : Ram)
    (valid : ∀ op ∈ ops, op.validSpills) (low : ctx.stackPointer.toNat + 336 ≤ 2^32) :
    RamWriteFrame m (spillRun ctx ops s m) (spillRegions ctx.stackPointer) := by
  have contained (off bytes : Nat) (spill : ValidSpill off bytes) :
      InRegions (spillRegions ctx.stackPointer) (ctx.stackPointer + BitVec.ofNat 64 off) bytes := by
    have bounds := spill.2
    have endBound : off + bytes ≤ 288 := by
      rcases bounds with first | second <;> omega
    have addr : (ctx.stackPointer + BitVec.ofNat 64 off).toNat =
        ctx.stackPointer.toNat + off := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
    rcases bounds with first | second
    · refine ⟨_, List.mem_cons_self, ?_⟩
      change ctx.stackPointer.toNat ≤ _ ∧ _ + bytes ≤ ctx.stackPointer.toNat + 192 ∧ _
      rw [addr]
      omega
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      change ctx.stackPointer.toNat + 208 ≤ _ ∧ _ + bytes ≤ ctx.stackPointer.toNat + 208 + 80 ∧ _
      rw [addr]
      omega
  suffices runs : ∀ current, RamWriteFrame m current (spillRegions ctx.stackPointer) →
      RamWriteFrame m (spillRun ctx ops s current) (spillRegions ctx.stackPointer) from
    runs m (RamWriteFrame.refl _ _)
  induction ops generalizing s with
  | nil => exact fun _ frame => frame
  | cons op ops ih =>
      intro current frame
      have head := valid op List.mem_cons_self
      have tail (step : Op) (mem : step ∈ ops) := valid step (List.mem_cons_of_mem _ mem)
      apply ih _ tail
      cases op <;> try exact frame
      case store32 off src => exact frame.memStore _ (contained off 4 head)
      case store64 off src => exact frame.memStore _ (contained off 8 head)
      case addStack32 off src => exact frame.memStore _ (contained off 4 head)

private def decidableValidSpills (op : Op) : Decidable op.validSpills := by
  cases op <;> simp only [Op.validSpills, ValidSpill] <;> infer_instance

theorem operations_valid : ∀ op ∈ Program.operations, op.validSpills := by
  letI : DecidablePred Op.validSpills := decidableValidSpills
  have allValid : Program.operations.all (fun op => decide op.validSpills) = true := by
    decide +kernel
  intro op mem
  exact of_decide_eq_true (List.all_eq_true.mp allValid op mem)

end K256.Proofs.Verify.Hash.Compression.Values
