import Sha2.Proofs.Common.Memory.Fill.Memory
import Sha2.Proofs.Common.Memory.Copy.Return
import Sha2.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open Sha2.Proofs.Program

open Sha2.Proofs.Common.Machine (CalleePre CalleeResult boundary_ne_program memoryRegion_contains_add preservesABI_of_agrees programLoaded_codeIn programText_slice stack_region_end supportedMachine_of_ready_agrees)

namespace Sha2.Proofs.Common.Memory.Fill

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem FillState.stackPtr_eq [Bindings] {s t : RamState} {count : Nat}
    (h : FillState s t count) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [fillComponents, registerComponents])

theorem stackSlot_contains [Bindings] {s : RamState} {b : ReturnBoundary} {n reserve i : Nat}
    (hp : CalleePre s b 0x10dd10 0 n reserve) (hi : i < 8) :
    (Stack.region s reserve).Contains (stackPtr s + BitVec.ofNat 64 i).toNat := by
  apply memoryRegion_contains_add hp.stack.1
  · exact Nat.sub_le _ _
  · change (stackPtr s).toNat + 8 ≤ (Stack.region s reserve).start +
      (Stack.region s reserve).size
    rw [stack_region_end]
    exact Nat.le_refl _
  · exact hi

theorem FillState.stackTop_eq [Bindings] {s t : RamState} {b : ReturnBoundary}
    {n reserve count : Nat} (hp : CalleePre s b 0x10dd10 0 n reserve)
    (h : FillState s t count) (hc : count ≤ n) : stackTop t = (returnBoundary s).rip := by
  change memLoad t.external (stackPtr t) 64 = memLoad s.external (stackPtr s) 64
  rw [h.stackPtr_eq]
  apply memLoad_congr
  intro i hi
  apply memByte_congr
  apply h.agrees.byte
  intro c hmem hcover
  simp only [fillComponents, registerComponents, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;>
    try exact hcover
  obtain ⟨j, hj, he⟩ := hcover
  have hd := hp.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
  change (registerRegion s .rdi n).Disjoint (Stack.region s reserve) at hd
  apply hd _ (destinationContains (i := j) hp (by omega))
  rw [← he]
  exact stackSlot_contains hp hi

theorem FillState.stackReadable [Bindings] {s t : RamState} {b : ReturnBoundary}
    {n reserve count : Nat} (hp : CalleePre s b 0x10dd10 0 n reserve)
    (h : FillState s t count) : MemReadable t (stackPtr t) 8 := by
  rw [h.stackPtr_eq]
  refine ⟨?_, ?_⟩
  · have hb := hp.stack.1
    change (Stack.region s reserve).start + (Stack.region s reserve).size < 2^32 at hb
    rw [stack_region_end] at hb
    omega
  · intro i hi
    exact h.agrees.grow _ (Option.isSome_iff_exists.mpr (hp.stack.2.1 _ (stackSlot_contains hp hi)))

theorem finish [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n reserve fuel : Nat} (hp : CalleePre s boundary 0x10dd10 0 n reserve)
    (h : FillState s t n) (hrip : t.RIP = 0x10dd54) (hexec : Advances boundary fuel s t)
    (hReturn : InProgram (returnBoundary s).rip) :
    ∃ final, CalleeResult s final boundary n reserve ∧
      (∀ i < n, final.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
        some 0) ∧
      AgreesExcept (fillComponents s n ++ [.reg 4, .rip]) s final := by
  have hloaded := h.loaded hp (Nat.le_refl _)
  have hret : RetPre 0x10dd54 t :=
    ⟨⟨hrip, h.stackReadable hp⟩, h.stackTop_eq hp (Nat.le_refl _) ▸ Sha2.Proofs.Common.Memory.Copy.inProgram_low hReturn⟩
  have hcode := programText_slice (programLoaded_codeIn hloaded)
    0xdd54 [0xc3] (by decide) (by decide +kernel)
  have hnext : (retEffect t).rip ≠ boundary.rip := by
    change stackTop t ≠ boundary.rip
    rw [h.stackTop_eq hp (Nat.le_refl _)]
    exact boundary_ne_program hp.outerBoundary hReturn
  obtain ⟨final, ha, hr, he⟩ := (ret_effect_step 0x10dd54).advances h.ready hcode hret hnext
  have hag : AgreesExcept (fillComponents s n ++ [.reg 4, .rip]) s final := h.agrees.trans he.agrees
  have hmem : final.external = t.external := he.agrees.external (by simp [Component.Covers])
  refine ⟨final, ?_, ?_, hag⟩
  · refine ⟨⟨fuel+1, hexec.trans ha⟩, he.rip.trans (h.stackTop_eq hp (Nat.le_refl _)), ?_,
      supportedMachine_of_ready_agrees hp.machine hr hag, ?_, ?_, ?_, hag.grow⟩
    · have hw := he.writes
      change final.regValue .rsp = stackPtr t + 8 at hw
      rw [hw, h.stackPtr_eq]
      rfl
    · apply preservesABI_of_agrees hag hp.directionFlag
      intro r hreg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hag.read (n := 64) (r := 3) (by simp [fillComponents, registerComponents])
      · exact hag.read (n := 64) (r := 5) (by simp [fillComponents, registerComponents])
      · exact hag.read (n := 64) (r := 12) (by simp [fillComponents, registerComponents])
      · exact hag.read (n := 64) (r := 13) (by simp [fillComponents, registerComponents])
      · exact hag.read (n := 64) (r := 14) (by simp [fillComponents, registerComponents])
      · exact hag.read (n := 64) (r := 15) (by simp [fillComponents, registerComponents])
      all_goals simp [fillComponents, registerComponents]

    · apply hag.memoryWriteFrame
      intro c hmem address hcover
      simp only [fillComponents, registerComponents, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) |
        (rfl | rfl) <;> try exact hcover.elim
      obtain ⟨i, hi, rfl⟩ := hcover
      exact ⟨registerRegion s .rdi n, by simp, destinationContains hp hi⟩
    · intro address byte hb
      rw [hmem]
      exact hloaded address byte hb
  · intro i hi
    rw [hmem]
    exact h.fill i hi

end Sha2.Proofs.Common.Memory.Fill
