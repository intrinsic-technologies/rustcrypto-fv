import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Call
import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Machine

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

 theorem setup_call [Bindings] (last : Bool)
    {initial s : RamState} {message chunk : ByteArray} {boundary : ReturnBoundary}
    {hash : Array UInt32} (pre : Message.Pre initial boundary message)
    (input : HashAt initial s boundary hash)
    (rip : s.RIP = if last then 0x10d8be else 0x10d7e5)
    (bytes : (MemoryRegion.mk (frameBase initial).toNat 64).HasBytes s.external chunk) :
    ∃ t, HashAt initial t boundary
      (SHA256.Reference.compress hash (Standards.NIST.SHA2.bytesToBits chunk)) ∧
      t.RIP = (if last then 0x10d8ce else 0x10d7f5) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.regValue r = s.regValue r) := by
  let pc : Nat := if last then 0xd8be else 0xd7e5
  have bound : pc + 11 < 118431 := by cases last <;> decide
  have next (i : Nat) (hi : i ≤ 11) :
      (Extracted.textAddress + BitVec.ofNat 64 pc) + BitVec.ofNat 64 i ≠ boundary.rip := by
    apply boundary_ne_program pre.outerBoundary
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (pc+i) (by omega)
  obtain ⟨_, u, run, ready, _, effect⟩ := Machine.setup
    (Extracted.textAddress + BitVec.ofNat 64 pc) boundary next s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) pc Machine.setupBytes
      (by change pc+11 ≤ 118431; omega) (by cases last <;> decide +kernel))
    (by cases last <;> exact rip)
  have frame : AgreesExcept [.reg 6,.reg 2,.reg 7,.rip] s u := effect.agrees
  have state := hashAt_after_registers input run ready frame
    (by simp [Component.Covers]) (by simp) (by simp)
  have memory := frame.external (by simp [Component.Covers])
  have stores := effect.writes
  change u.regValue .rsi = rspOf s ∧ u.regValue .rdx = 1 ∧
    u.regValue .rdi = s.regValue .rbx at stores
  have rsi : u.regValue .rsi = frameBase initial := by
    rw [stores.1]
    exact input.rsp
  have ripU : u.RIP = if last then 0x10d8c9 else 0x10d7f0 := by
    cases last <;> exact effect.rip
  obtain ⟨t, output, ripT, saved⟩ := call last pre state ripU
    (stores.2.2.trans input.hashPointer) rsi stores.2.1
    (by simpa only [memory] using bytes)
  refine ⟨t, output, ?_, ?_⟩
  · rw [ripT, ripU]
    cases last <;> rfl
  · intro r member
    apply (saved r member).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact frame.read (n := 64) (r := 3) (by simp)
    · exact frame.read (n := 64) (r := 5) (by simp)
    · exact frame.read (n := 64) (r := 12) (by simp)
    · exact frame.read (n := 64) (r := 13) (by simp)
    · exact frame.read (n := 64) (r := 14) (by simp)
    · exact frame.read (n := 64) (r := 15) (by simp)

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks
