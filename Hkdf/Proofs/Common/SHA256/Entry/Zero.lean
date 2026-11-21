import Hkdf.Proofs.Common.SHA256.Entry.Branch
import Hkdf.Proofs.Common.Memory.Copy.Return

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

theorem compression_correct_zero [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray}
    (pre : CompressionPre s boundary hash input 0) :
    ∃ t, CompressionResult s t boundary hash input ∧ t.external = s.external := by
  obtain ⟨u, hu, hru, hip, hfu⟩ := entry_branch pre
  have hip' : u.RIP = 0x10bdd8 := by simpa only [ite_true] using hip
  have memory : u.external = s.external := hfu.external (by simp [Component.Covers])
  have rsp : stackPtr u = stackPtr s := hfu.read (n := 64) (r := 4) (by simp)
  have top : stackTop u = (returnBoundary s).rip := by
    change memLoad u.external (stackPtr u) 64 = memLoad s.external (stackPtr s) 64
    rw [memory, rsp]
  have readable : MemReadable u (stackPtr u) 8 := by
    rw [rsp]
    have hr : MemReadable s (stackPtr s) 8 := by
      simpa only [BitVec.sub_zero] using
        Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_readable pre.toCalleePre
          (offset := 0) (len := 8) (by decide) (by decide)
    exact ⟨hr.low, fun i hi => hfu.grow _ (hr.mem i hi)⟩
  obtain ⟨t, ht, hrt, het⟩ := (ret_effect_step 0x10bdd8).advances hru
    (programText_slice (hfu.codeIn (by simp [Component.Covers]) (programLoaded_codeIn pre.loaded))
      0xbdd8 [0xc3] (by decide +kernel) (by decide +kernel))
    ⟨⟨hip', readable⟩, top ▸ Hkdf.Proofs.Common.Memory.Copy.inProgram_low pre.returnInProgram⟩
    (by change stackTop u ≠ boundary.rip; rw [top]; exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have hft : AgreesExcept [.reg 4, .rip] u t := het.agrees
  have agrees := hfu.trans hft
  have finalMemory : t.external = s.external := agrees.external (by simp [Component.Covers])
  have result : CalleeResult s t boundary 32 336 := by
    refine ⟨⟨3, hu.trans ht⟩, het.rip.trans top, ?_,
      supportedMachine_of_ready_agrees pre.machine hrt agrees, ?_, ?_, ?_, agrees.grow⟩
    · have hw : stackPtr t = stackPtr u + 8 := het.writes
      change stackPtr t = stackPtr s + 8
      rw [hw, rsp]
    · apply preservesABI_of_agrees agrees pre.directionFlag
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact agrees.read (n := 64) (r := 3) (by simp)
      · exact agrees.read (n := 64) (r := 5) (by simp)
      · exact agrees.read (n := 64) (r := 12) (by simp)
      · exact agrees.read (n := 64) (r := 13) (by simp)
      · exact agrees.read (n := 64) (r := 14) (by simp)
      · exact agrees.read (n := 64) (r := 15) (by simp)
      all_goals simp
    · intro a _
      rw [finalMemory]
    · intro a b hb
      rw [finalMemory]
      exact pre.loaded a b hb
  refine ⟨t, ⟨result, ?_⟩, finalMemory⟩
  have size : input.size = 0 := pre.inputBytes.1
  have hc : compressBlocks hash input = hash := by
    simp only [compressBlocks, size, Nat.zero_div, compressBlocksFrom]
  rw [hc]
  exact ⟨pre.hashWords.1, fun i hi => by rw [finalMemory]; exact pre.hashWords.2 i hi⟩

end Hkdf.Proofs.Common.SHA256
