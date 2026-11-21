import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Call
import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Machine
import Sha2.Proofs.Wrapper.Hash.Finalize.Compress.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize.Compress

variable {v : Variant}

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

theorem setup_call [Bindings] (body : Compression.BlockCorrect) (last : Bool)
    {initial s : RamState} {inputs : Array Input} {chunk : ByteArray} {hash : Array UInt32}
    (ctx : Context initial inputs v)
    (input : HashAt initial s hash v)
    (rip : s.RIP = if last then (v.pc 0x320) else (v.pc 0x264))
    (bytes : (⟨(stackPtr initial - 240).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ t, HashAt initial t (NIST.SHA256.compress hash (NIST.Encoding.octetsToBits chunk)) v
      ∧ t.RIP = (if last then (v.pc 0x332) else (v.pc 0x276)) ∧ PreservesABI s t := by
  let pc : Nat := if last then (v.textOffset + 0x320) else (v.textOffset + 0x264)
  have bound : pc + 13 < 71757 := by cases v <;> cases last <;> decide
  have next (i : Nat) (hi : i ≤ 13) :
      (Extracted.textAddress + BitVec.ofNat 64 pc) + BitVec.ofNat 64 i ≠
        (returnBoundary initial).rip := by
    apply boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (pc+i) (by omega)
  obtain ⟨_, u, run, ready, _, effect⟩ := setup
    (Extracted.textAddress + BitVec.ofNat 64 pc) (returnBoundary initial) next s
    (supportedMachine_readyToStep input.machine)
    (programText_slice (programLoaded_codeIn input.loaded) pc setupBytes (by change pc+13 ≤ 71757; omega)
      (by cases v <;> cases last <;> decide +kernel)) (by cases last <;> exact rip)
  have frame : AgreesExcept [.reg 6,.reg 2,.reg 7,.rip] s u := by
    simpa only [setupEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.cons_append, List.nil_append] using effect.agrees
  have state := preserve ctx input run ready frame (by simp [Writes, Component.Covers]) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp)
  have memory := frame.external (by simp [Component.Covers])
  have stores := effect.writes
  change u.regValue .rsi = rspOf s+104 ∧ u.regValue .rdx = 1 ∧
    u.regValue .rdi = s.regValue .r14 at stores
  have rsi : u.regValue .rsi = stackPtr initial-240 := by
    rw [stores.1, stack_address input.rsp]
    rfl
  have ripU : u.RIP = if last then (v.pc 0x32d) else (v.pc 0x271) := by
    have h := effect.rip
    cases v <;> cases last <;> exact h
  obtain ⟨t, output, ripT, abiT⟩ := call body last ctx state ripU
    (stores.2.2.trans input.hashPointer) rsi stores.2.1
    (by simpa only [memory] using bytes)
  have abiU : PreservesABI s u := by
    apply preservesABI_of_agrees frame input.directionFlag
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact frame.read (n := 64) (r := 3) (by simp)
    · exact frame.read (n := 64) (r := 5) (by simp)
    · exact frame.read (n := 64) (r := 12) (by simp)
    · exact frame.read (n := 64) (r := 13) (by simp)
    · exact frame.read (n := 64) (r := 14) (by simp)
    · exact frame.read (n := 64) (r := 15) (by simp)
    all_goals simp
  refine ⟨t, output, ?_, ?_⟩
  · rw [ripT, ripU]
    cases v <;> cases last <;> rfl
  · exact ⟨fun reg member => (abiT.1 reg member).trans (abiU.1 reg member),
      abiT.2.1, abiT.2.2.1.trans abiU.2.2.1, abiT.2.2.2.trans abiU.2.2.2⟩

end Sha2.Proofs.Wrapper.Hash.Finalize.Compress
