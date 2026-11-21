import K256.Proofs.Verify.Hash.Compression.Groups
import K256.Proofs.Verify.Hash.Compression.SpillFrame

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Values

theorem Values.spillRun_append (ctx : ValueContext) (xs ys : List Values.Op)
    (s : Compression.Values) (m : Ram) :
    spillRun ctx (xs ++ ys) s m = spillRun ctx ys (run ctx xs s) (spillRun ctx xs s m) := by
  induction xs generalizing s m with
  | nil => rfl
  | cons op xs ih => exact ih (op.eval ctx s) (op.spill ctx s m)

theorem GroupStep.append {n k j : Nat}
    {start : Block Lift.Op Label signature Reg.count n}
    {middle : Block Lift.Op Label signature Reg.count k}
    {last : Block Lift.Op Label signature Reg.count j}
    {xs ys : List Values.Op} {before between after} {p q : ValueContext → Compression.Values → Prop}
    (left : GroupStep start middle xs before between p)
    (right : GroupStep middle last ys between after q)
    (valid : ∀ op ∈ xs, op.validSpills)
    (next : ∀ ctx s, s.regs 4 = ctx.stackPointer → p ctx s →
      (run ctx xs s).regs 4 = ctx.stackPointer ∧ q ctx (run ctx xs s)) :
    GroupStep start last (xs ++ ys) before after p := by
  intro code cover orig a m ctx s stack src apart words slots sp ptr regs saved
  obtain ⟨b, _, step, rfl, regs', saved'⟩ :=
    left code cover orig a m ctx s stack src apart words slots sp ptr regs saved
  have frame := spillRun_frame ctx xs s m valid stack.readable.low
  have words' (off : Nat) (h : off + 4 ≤ 64) :
      memLoad (spillRun ctx xs s m) (ctx.inputPointer + BitVec.ofNat 64 off) 32 =
        ctx.inputWords off := by
    refine (frame.memLoad_eq ?_).trans (words off h)
    have low := src.low
    have addr : (ctx.inputPointer + BitVec.ofNat 64 off).toNat = ctx.inputPointer.toNat + off := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
    change _ + 4 ≤ 2^64 ∧ _
    refine ⟨by rw [addr]; omega, ?_⟩
    intro r hr
    simp only [spillRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [addr] <;> omega
  obtain ⟨sp', ptr'⟩ := next ctx s sp ptr
  obtain ⟨c, m', step', memory, regs'', saved''⟩ :=
    right code cover orig b _ ctx _ (stack.of_frame frame) (src.of_frame frame) apart
      words' (spillRun_matches ctx xs s m valid slots) sp' ptr' regs' saved'
  exact ⟨c, m', step.trans step', (spillRun_append ctx xs ys s m) ▸ memory,
    (run_append ctx xs ys s) ▸ regs'', saved''⟩

end K256.Proofs.Verify.Hash.Compression
