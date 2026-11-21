import Sha2.Proofs.Common.SHA256.Entry.Branch
import Sha2.Proofs.Common.Memory.Copy.Return

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem compression_zero_before_ret [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray}
    (pre : CompressionPre s boundary hash input 0) :
    ∃ t, CalleeResult s t boundary 32 336 ⟨0x10dcf8, stackPtr s⟩ ∧
      stackTop t = (returnBoundary s).rip ∧ MemReadable t (stackPtr t) 8 ∧
      t.external = s.external := by
  obtain ⟨u, hu, hru, hip, hfu⟩ := entry_branch pre
  have hip' : u.RIP = 0x10dcf8 := by simpa only [ite_true] using hip
  have memory : u.external = s.external := hfu.external (by simp [Component.Covers])
  have rsp : stackPtr u = stackPtr s := hfu.read (n := 64) (r := 4) (by simp)
  have top : stackTop u = (returnBoundary s).rip := by
    change memLoad u.external (stackPtr u) 64 = memLoad s.external (stackPtr s) 64
    rw [memory, rsp]
  have readable : MemReadable u (stackPtr u) 8 := by
    rw [rsp]
    have hr : MemReadable s (stackPtr s) 8 := by
      simpa only [BitVec.sub_zero] using
        Sha2.Proofs.Common.Encoding.Serialize.stack_sub_readable pre.toCalleePre
          (offset := 0) (len := 8) (by decide) (by decide)
    exact ⟨hr.low, fun i hi => hfu.grow _ (hr.mem i hi)⟩
  refine ⟨u, ?_, top, readable, memory⟩
  refine ⟨⟨2, hu⟩, hip', rsp,
    supportedMachine_of_ready_agrees pre.machine hru hfu, ?_, ?_, ?_, hfu.grow⟩
  · apply preservesABI_of_agrees hfu pre.directionFlag
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfu.read (n := 64) (r := 3) (by simp)
    · exact hfu.read (n := 64) (r := 5) (by simp)
    · exact hfu.read (n := 64) (r := 12) (by simp)
    · exact hfu.read (n := 64) (r := 13) (by simp)
    · exact hfu.read (n := 64) (r := 14) (by simp)
    · exact hfu.read (n := 64) (r := 15) (by simp)
    all_goals simp
  · intro a _
    rw [memory]
  · intro a b hb
    rw [memory]
    exact pre.loaded a b hb

theorem compression_correct_zero [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray}
    (pre : CompressionPre s boundary hash input 0)
    (hReturn : InProgram (returnBoundary s).rip) :
    ∃ t, CompressionResult s t boundary hash input ∧ t.external = s.external := by
  obtain ⟨u, result, top, readable, memory⟩ := compression_zero_before_ret pre
  obtain ⟨t, final, memory'⟩ := result.finish top readable pre.outerBoundary hReturn
    (programText_slice (programLoaded_codeIn result.loaded) 0xdcf8 [0xc3]
      (by decide +kernel) (by decide +kernel))
  have finalMemory := memory'.trans memory
  refine ⟨t, ⟨final, ?_⟩, finalMemory⟩
  have size : input.size = 0 := pre.inputBytes.1
  have hc : compressBlocks hash input = hash := by
    simp only [compressBlocks, size, Nat.zero_div, compressBlocksFrom]
  rw [hc]
  exact ⟨pre.hashWords.1, fun i hi => by rw [finalMemory]; exact pre.hashWords.2 i hi⟩

end Sha2.Proofs.Common.SHA256
