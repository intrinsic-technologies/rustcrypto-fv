import K256.Proofs.Verify.Hash.Compression.Groups.Range02
import K256.Proofs.Verify.Hash.Compression.Groups.Range22
import K256.Proofs.Verify.Hash.Compression.Groups.Range42
import K256.Proofs.Verify.Hash.Compression.Groups.Range62
import K256.Proofs.Verify.Hash.Compression.Groups.Range82
import K256.Proofs.Verify.Hash.Compression.Groups.Range102
import K256.Proofs.Verify.Hash.Compression.Groups.Range122
import K256.Proofs.Verify.Hash.Compression.Groups.Range142

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

def middleOperations := range02 ++ range22 ++ range42 ++ range62 ++ range82 ++ range102 ++ range122 ++ range142

set_option maxRecDepth 4096 in
private theorem middleSteps : GroupStep b_l121930_2 b_l121930_166 middleOperations registers02 registers166 spilledInput :=
  (range02_step.chain
    (range22_step.chain
    (range42_step.chain
    (range62_step.chain
    (range82_step.chain
    (range102_step.chain
    (range122_step.chain
    range142_step (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

def prefixOperations := (firstGroup ++ group01) ++ middleOperations

private theorem validPrefix : ∀ op ∈ firstGroup ++ group01, op.validSpills := by
  intro op h
  apply operations_valid op
  have split : Values.Program.operations = (firstGroup ++ group01) ++ Values.Program.operations.drop 40 := by
    decide +kernel
  rw [split]
  exact List.mem_append_left _ h

private theorem savedPointers (ctx : ValueContext) (s : Compression.Values)
    (sp : s.regs 4 = ctx.stackPointer) (ip : s.regs 6 = ctx.inputPointer) :
    let t := run ctx (firstGroup ++ group01) s
    t.regs 4 = ctx.stackPointer ∧ spilledInput ctx t := by
  refine ⟨sp, ?_⟩
  change ((s.regs 6).extractLsb' 32 32 ++ (s.regs 6).setWidth 32) = ctx.inputPointer
  exact (BitVec.extractLsb'_append_extractLsb' (x := s.regs 6) (w := 32) (len := 32)).trans ip

theorem prefixSteps : GroupStep b_l121930 b_l121930_166 prefixOperations initialRegisters registers166
    (fun c s => s.regs 6 = c.inputPointer) := by
  apply GroupStep.append (xs := firstGroup ++ group01) (right := middleSteps)
  · apply firstGroup_step.append group01_step
    · intro op h
      exact validPrefix op (List.mem_append_left _ h)
    · intro ctx s sp _
      exact ⟨sp, True.intro⟩
  · exact validPrefix
  · exact savedPointers

theorem operations_split : prefixOperations ++ group166 = Values.Program.operations := by
  decide +kernel

private def betweenPointers := (Values.Program.operations.drop 40).take 3260

private theorem between_split : ((firstGroup ++ group01) ++ betweenPointers) ++ group165 = prefixOperations := by
  decide +kernel

private theorem between_safe : chainSafe betweenPointers := by decide +kernel

attribute [local irreducible] betweenPointers prefixOperations

theorem prefixPointers (ctx : ValueContext) (s : Compression.Values)
    (sp : s.regs 4 = ctx.stackPointer) (ip : s.regs 6 = ctx.inputPointer) :
    let t := run ctx prefixOperations s
    t.regs 4 = ctx.stackPointer ∧ t.regs 6 = ctx.inputPointer := by
  have last (t : Compression.Values) (h : t.regs 4 = ctx.stackPointer ∧ spilledInput ctx t) :
      (run ctx group165 t).regs 4 = ctx.stackPointer ∧ (run ctx group165 t).regs 6 = ctx.inputPointer :=
    ⟨h.1, h.2⟩
  rw [← between_split, run_append, run_append]
  exact last _ (chainSafe_pointers between_safe ctx _ (savedPointers ctx s sp ip))

end K256.Proofs.Verify.Hash.Compression
