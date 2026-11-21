import Sha2.Proofs.Common.Memory.Copy.Memory
import Sha2.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open Sha2.Proofs.Common.Machine (CalleePre CalleeResult boundary_ne_program memoryRegion_contains_add preservesABI_of_agrees programLoaded_codeIn programText_slice stack_region_end supportedMachine_of_ready_agrees)

namespace Sha2.Proofs.Common.Memory.Copy

open Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem imageSection_fetch_low {sec : ImageSection} {a : BitVec 64} {byte : UInt8}
    (hlow : sec.address.toNat + sec.bytes.size ≤ 2^32)
    (hf : sec.fetchByte a = some byte) : a.toNat < 2^32 := by
  have hoff : (a-sec.address).toNat < sec.bytes.size := by
    unfold ImageSection.fetchByte Bytes.Chunked.get? at hf
    split at hf
    · assumption
    · contradiction
  rw [BitVec.toNat_sub] at hoff
  have := a.isLt
  have := sec.address.isLt
  omega

theorem inProgram_low {a : BitVec 64} (h : InProgram a) : a.toNat < 2^32 := by
  obtain ⟨byte, hb⟩ := h
  exact Sha2.Proofs.Common.Machine.programSections_low.codeLow _ hb

theorem CopyState.stackPtr_eq [Bindings] {s t : RamState} {count : Nat}
    (h : CopyState s t count) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [copyComponents, registerComponents])

theorem stackSlot_contains [Bindings] {s : RamState} {b : ReturnBoundary} {n reserve i : Nat}
    (hp : CalleePre s b 0x10dd60 n n reserve) (hi : i < 8) :
    (Stack.region s reserve).Contains (stackPtr s + BitVec.ofNat 64 i).toNat := by
  apply memoryRegion_contains_add hp.stack.1
  · exact Nat.sub_le _ _
  · change (stackPtr s).toNat + 8 ≤ (Stack.region s reserve).start +
      (Stack.region s reserve).size
    rw [stack_region_end]
    exact Nat.le_refl _
  · exact hi

theorem CopyState.stackTop_eq [Bindings] {s t : RamState} {b : ReturnBoundary}
    {n reserve count : Nat} (hp : CalleePre s b 0x10dd60 n n reserve)
    (h : CopyState s t count) (hc : count ≤ n) : stackTop t = (returnBoundary s).rip := by
  change memLoad t.external (stackPtr t) 64 = memLoad s.external (stackPtr s) 64
  rw [h.stackPtr_eq]
  apply memLoad_congr
  intro i hi
  apply memByte_congr
  apply h.agrees.byte
  intro c hmem hcover
  simp only [copyComponents, registerComponents, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
    try exact hcover
  obtain ⟨j, hj, he⟩ := hcover
  have hd := hp.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
  change (registerRegion s .rdi n).Disjoint (Stack.region s reserve) at hd
  apply hd _ (destinationContains (i := j) hp (by omega))
  rw [← he]
  exact stackSlot_contains hp hi

theorem CopyState.stackReadable [Bindings] {s t : RamState} {b : ReturnBoundary}
    {n reserve count : Nat} (hp : CalleePre s b 0x10dd60 n n reserve)
    (h : CopyState s t count) : MemReadable t (stackPtr t) 8 := by
  rw [h.stackPtr_eq]
  refine ⟨?_, ?_⟩
  · have hb := hp.stack.1
    change (Stack.region s reserve).start + (Stack.region s reserve).size < 2^32 at hb
    rw [stack_region_end] at hb
    omega
  · intro i hi
    exact h.agrees.grow _ (Option.isSome_iff_exists.mpr (hp.stack.2.1 _ (stackSlot_contains hp hi)))

theorem finish [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n reserve fuel : Nat} (hp : CalleePre s boundary 0x10dd60 n n reserve)
    (h : CopyState s t n) (hrip : t.RIP = 0x10dd8e) (hexec : Advances boundary fuel s t)
    (hReturn : InProgram (returnBoundary s).rip) :
    ∃ final, CalleeResult s final boundary n reserve ∧
      (∀ i < n, final.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
        s.external[s.regValue .rsi + BitVec.ofNat 64 i]?) ∧
      AgreesExcept (copyComponents s n ++ [.reg 4, .rip]) s final := by
  have hloaded := h.loaded hp (Nat.le_refl _)
  have hret : RetPre 0x10dd8e t :=
    ⟨⟨hrip, h.stackReadable hp⟩, h.stackTop_eq hp (Nat.le_refl _) ▸ inProgram_low hReturn⟩
  have hcode := programText_slice (programLoaded_codeIn hloaded)
    0xdd8e [0xc3] (by decide) (by decide +kernel)
  have hnext : (retEffect t).rip ≠ boundary.rip := by
    change stackTop t ≠ boundary.rip
    rw [h.stackTop_eq hp (Nat.le_refl _)]
    exact boundary_ne_program hp.outerBoundary hReturn
  obtain ⟨final, ha, hr, he⟩ := (ret_effect_step 0x10dd8e).advances h.ready hcode hret hnext
  have hag : AgreesExcept (copyComponents s n ++ [.reg 4, .rip]) s final := h.agrees.trans he.agrees
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
      · exact hag.read (n := 64) (r := 3) (by simp [copyComponents, registerComponents])
      · exact hag.read (n := 64) (r := 5) (by simp [copyComponents, registerComponents])
      · exact hag.read (n := 64) (r := 12) (by simp [copyComponents, registerComponents])
      · exact hag.read (n := 64) (r := 13) (by simp [copyComponents, registerComponents])
      · exact hag.read (n := 64) (r := 14) (by simp [copyComponents, registerComponents])
      · exact hag.read (n := 64) (r := 15) (by simp [copyComponents, registerComponents])
      all_goals simp [copyComponents, registerComponents]

    · apply hag.memoryWriteFrame
      intro c hmem address hcover
      simp only [copyComponents, registerComponents, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
        (rfl | rfl) <;> try exact hcover.elim
      obtain ⟨i, hi, rfl⟩ := hcover
      exact ⟨registerRegion s .rdi n, by simp, destinationContains hp hi⟩
    · intro address byte hb
      rw [hmem]
      exact hloaded address byte hb
  · intro i hi
    rw [hmem]
    exact h.copy i hi

end Sha2.Proofs.Common.Memory.Copy

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem CalleeResult.finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {outputBytes reserve : Nat} {retPC : BitVec 64}
    (result : CalleeResult s t boundary outputBytes reserve ⟨retPC, stackPtr s⟩)
    (top : stackTop t = (returnBoundary s).rip) (readable : MemReadable t (stackPtr t) 8)
    (outside : ¬ InProgram boundary.rip) (hReturn : InProgram (returnBoundary s).rip)
    (code : CodeIn (codeRange retPC [0xc3]) t) :
    ∃ u, CalleeResult s u boundary outputBytes reserve ∧ u.external = t.external := by
  obtain ⟨u, run, ready, effect⟩ := (ret_effect_step retPC).advances
    (supportedMachine_readyToStep result.machine) code
    ⟨⟨result.rip, readable⟩, top ▸ Sha2.Proofs.Common.Memory.Copy.inProgram_low hReturn⟩
    (by change stackTop t ≠ boundary.rip; rw [top]; exact boundary_ne_program outside hReturn)
  have memory : u.external = t.external := effect.agrees.external (by simp [Component.Covers])
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨u, ⟨⟨fuel + 1, execution.trans run⟩, effect.rip.trans top, ?_,
    supportedMachine_of_ready_agrees result.machine ready effect.agrees, ?_, ?_, ?_, ?_⟩,
    memory⟩
  · change stackPtr u = stackPtr s + 8
    have hw : stackPtr u = stackPtr t + 8 := effect.writes
    rw [hw]
    exact congrArg (fun x => x + 8) result.rsp
  · refine ⟨?_, effect.agrees.directionFlagClear (by simp) result.abi.2.1,
      (effect.agrees.mxcsr (by simp)).trans result.abi.2.2.1,
      (effect.agrees.fcw (by simp)).trans result.abi.2.2.2⟩
    intro r hr
    have old := result.abi.1 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (effect.agrees.read (n := 64) (r := 3) (by simp)).trans old
    · exact (effect.agrees.read (n := 64) (r := 5) (by simp)).trans old
    · exact (effect.agrees.read (n := 64) (r := 12) (by simp)).trans old
    · exact (effect.agrees.read (n := 64) (r := 13) (by simp)).trans old
    · exact (effect.agrees.read (n := 64) (r := 14) (by simp)).trans old
    · exact (effect.agrees.read (n := 64) (r := 15) (by simp)).trans old
  · intro a ha
    rw [memory]
    exact result.frame a ha
  · intro a b hb
    rw [memory]
    exact result.loaded a b hb
  · intro a ha
    rw [memory]
    exact result.allocated a ha

theorem CalleeResult.finish_returns [bindings : Bindings] {s t : RamState}
    {outputBytes reserve : Nat} {retPC : BitVec 64}
    (result : CalleeResult s t (returnBoundary s) outputBytes reserve ⟨retPC, stackPtr s⟩)
    (top : stackTop t = (returnBoundary s).rip) (readable : MemReadable t (stackPtr t) 8)
    (low : (returnBoundary s).rip.toNat < 2^32)
    (code : CodeIn (codeRange retPC [0xc3]) t) :
    ∃ u, (∃ fuel, Returns (returnBoundary s) fuel s u) ∧
      SupportedMachine bindings u ∧ PreservesABI s u ∧
      MemoryWriteFrame s u #v[registerRegion s .rdi outputBytes, Stack.region s reserve] ∧
      u.external = t.external := by
  obtain ⟨u, step, ready, effect⟩ := ret_effect_step retPC t
    (supportedMachine_readyToStep result.machine) code ⟨⟨result.rip, readable⟩, top ▸ low⟩
  have run : Returns (returnBoundary s) 1 t u := Returns.of_step step
    (effect.rip.trans top) (by
      change stackPtr u = stackPtr s + 8
      have hw : stackPtr u = stackPtr t + 8 := effect.writes
      rw [hw]
      exact congrArg (fun x => x + 8) result.rsp)
  have memory : u.external = t.external := effect.agrees.external (by simp [Component.Covers])
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨u, ⟨fuel + 1, execution.returns run⟩,
    supportedMachine_of_ready_agrees result.machine ready effect.agrees, ?_, ?_, memory⟩
  · refine ⟨?_, effect.agrees.directionFlagClear (by simp) result.abi.2.1,
      (effect.agrees.mxcsr (by simp)).trans result.abi.2.2.1,
      (effect.agrees.fcw (by simp)).trans result.abi.2.2.2⟩
    intro r hr
    have old := result.abi.1 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (effect.agrees.read (n := 64) (r := 3) (by simp)).trans old
    · exact (effect.agrees.read (n := 64) (r := 5) (by simp)).trans old
    · exact (effect.agrees.read (n := 64) (r := 12) (by simp)).trans old
    · exact (effect.agrees.read (n := 64) (r := 13) (by simp)).trans old
    · exact (effect.agrees.read (n := 64) (r := 14) (by simp)).trans old
    · exact (effect.agrees.read (n := 64) (r := 15) (by simp)).trans old
  · intro a ha
    rw [memory]
    exact result.frame a ha

end Sha2.Proofs.Common.Machine
