import K256.Proofs.Verify.Hash.Compression.Interface
import K256.Proofs.Verify.Hash.Compression.Setup
import K256.Proofs.Verify.Hash.Compression.Body
import K256.Proofs.Verify.Hash.Compression.Restore
import K256.Proofs.Verify.Hash.Compression.Empty

namespace K256.Proofs.Verify.Hash.Compression

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

variable {entry : CFG.Values Value Reg.count} {original : Ram} {sp dst src : BitVec 64}
    {initial : Array UInt32} {input : ByteArray}

private theorem loop (call : Call entry original sp dst src initial input) (remaining : Nat)
    {index : Nat} (total : index + remaining = input.size / 64)
    {hash : Array UInt32} {args : CFG.Values Value Reg.count} {mem : Ram}
    (ready : LoopState entry original sp dst src (input.size / 64) index hash args mem) :
    ∃ out, program.Exec (dialect Extracted.programImage)
      ⟨⟨if 0 < remaining then .l121930 else .l1240c4, args, mem⟩, []⟩ out ∧
      Returned entry original sp dst (compressBlocksFrom hash input index remaining) out := by
  induction remaining generalizing index hash args mem with
  | zero =>
    have idx : index = input.size / 64 := by omega
    subst index
    exact restore call ready
  | succ n ih =>
    obtain ⟨next, store, jump, nextReady⟩ := body call ready (by omega)
    obtain ⟨out, run, post⟩ := ih (index := index+1) (by omega) nextReady
    have h : (index + 1 < input.size / 64) ↔ 0 < n := by omega
    have labels : (if index + 1 < input.size / 64 then Label.l121930 else Label.l1240c4) =
        (if 0 < n then Label.l121930 else Label.l1240c4) := by
      by_cases left : index + 1 < input.size / 64
      · rw [ite_eq_left left, ite_eq_left (h.mp left)]
      · rw [ite_eq_right left, ite_eq_right (fun hn => left (h.mpr hn))]
    rw [labels] at jump
    exact ⟨out, .next (congrArg (Transfer.next _ []) jump) run, post⟩

theorem execute (call : Call entry original sp dst src initial input) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1218e0, entry, original⟩, []⟩ out ∧
      Returned entry original sp dst (compressBlocks initial input) out := by
  by_cases short : input.size / 64 = 0
  · simpa only [compressBlocks, short, compressBlocksFrom] using empty call short
  · have pos : 0 < input.size / 64 := by omega
    obtain ⟨args, mem, pre, ready⟩ := setup call pos
    obtain ⟨out, run, post⟩ := loop call (input.size / 64) (index := 0) (by omega) ready
    rw [ite_eq_left pos] at run
    exact ⟨out, Program.Exec.of_sem (pre.exec run.sem), post⟩

end K256.Proofs.Verify.Hash.Compression
