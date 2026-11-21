import K256.Proofs.Signing.Composition.Memory
import K256.Proofs.Signing.Composition.Reach
import K256.Proofs.Signing.Hash
import K256.Proofs.Signing.Transfer.Verify

namespace K256.Proofs.Signing.Composition

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)

private theorem messageMemory {s : RamState} {secret msg : ByteArray} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (memory : Memory s m) :
    (registerRegion s .rdx msg.size).HasBytes m msg ∧
    (s.regValue .rdx).toNat + msg.size < 2^32 ∧
    (0 < msg.size → (s.regValue .rdx).toNat + msg.size ≤ (sp s).toNat - 512 ∨
      (sp s).toNat + 1160 ≤ (s.regValue .rdx).toNat) := by
  let inputRegion := registerRegion s .rdx msg.size
  let stack := Stack.region s signingKeyTrySign.minStackBytes
  have input : ValidInput s inputRegion msg := call.inputsInMemory.2.1
  have disjoint : stack.Disjoint inputRegion :=
    (call.separation.2 stack (by simp [stack, writtenRegions])).2 inputRegion (by
      simp [inputRegion, inputRegions, signingKeyTrySign, K256.Spec.Program.inputRegion])
  have frame : MemoryWriteFrame s {s with external := m} #v[stack] :=
    memory.written.memoryWriteFrame fun _ outside _ inside =>
      outside _ (Vector.mem_toList_iff.mp inside)
  refine ⟨Common.hasBytes_of_memoryWriteFrame frame input.2.2 input.2.1 ?_,
    input.2.1, ?_⟩
  · intro r hr addr hInput hStack
    obtain rfl := Vector.mem_singleton.mp hr
    exact disjoint addr hStack hInput
  · intro nonempty
    obtain ⟨room, _, spNat⟩ := stackBounds call
    have depth := Common.stackOffset (off := 11192) call.stackAvailable (by decide)
    have stackEq : stack = ⟨(stackPtr s).toNat - 11192, 11200⟩ :=
      (stackRegion call).trans (congrArg (fun base => (⟨base,11200⟩ : MemoryRegion)) depth)
    have pos : 0 < stack.size := by rw [stackEq]; exact (by decide : 0 < 11200)
    have sep := apart_of_disjoint disjoint pos nonempty
    rw [stackEq] at sep
    change (stackPtr s).toNat - 11192 + 11200 ≤ (s.regValue .rdx).toNat ∨
      (s.regValue .rdx).toNat + msg.size ≤ (stackPtr s).toNat - 11192 at sep
    omega

private theorem preserveAfterHash {s : RamState} {secret msg : ByteArray} {d : Nat} {m n : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (before : CoreMemory s d m)
    (writes : RamWriteFrame m n (Hash.regions (sp s))) : CoreMemory s d n := by
  obtain ⟨room, low, spNat⟩ := stackBounds call
  apply before.preserve writes
  · intro r hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    rw [stackRegion call]
    change (stackPtr s - 11192).toNat ≤ r.start ∧
      r.start + r.size ≤ (stackPtr s - 11192).toNat + 11200
    have bottom : (stackPtr s - 11192).toNat = (stackPtr s).toNat - 11192 :=
      Common.stackOffset (off := 11192) call.stackAvailable (by decide)
    rw [bottom]
    simp only [Hash.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  · intro i hi
    have offsets : (344 ≤ i ∧ i + 8 ≤ 488) ∨ (592 ≤ i ∧ i ≤ 1288) := by
      simp only [protectedOffsets, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    have addr : (sp s + BitVec.ofNat 64 i).toNat = (sp s).toNat + i :=
      toNat_add_ofNat _ _ (by omega)
    refine ⟨by rw [addr]; omega, fun r hr => ?_⟩
    rw [addr]
    simp only [Hash.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega

theorem hash {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} (entry : HashEntry s d msg a m) :
    ∃ b n, Reach (core .l1054a6 a m) (core .l105758 b n) ∧ Digest s d msg b n := by
  obtain ⟨room, low, spNat⟩ := stackBounds call
  obtain ⟨bytes, inputLow, apart⟩ := messageMemory call entry.toMemory
  have readable : Readable m (s.regValue .rdx) msg.size := by
    have input := Readable.of_hasBytes bytes inputLow
    change Readable m (BitVec.ofNat 64 (s.regValue .rdx).toNat) msg.size at input
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using input
  have stack : Writable Extracted.programImage m (sp s - 512) 1672 := by
    have addr : sp s - 512 = stackPtr s - 1800 := by unfold sp; bv_omega
    rw [addr]
    exact (entry.toMemory.window call).of_offsets
      (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨b,n,run,rsp,df,kept,writes,r13,widths,digest⟩ := Hash.digest
    entry.rsp entry.df entry.count entry.descriptor entry.pointer entry.size
    (entry.toMemory.image call) bytes readable stack (by omega) (by omega) inputLow apart
    entry.iv entry.buffered entry.blocks
  have transferred := Transfer.verifyReaches (src := .l1054a6) (dst := .l1054a6)
    (src' := .l105758) (dst' := .l105758) (by simp [Transfer.sharedLabels])
    (by simp [Transfer.sharedLabels]) run
  obtain ⟨mx,tag,control⟩ := entry.fp
  refine ⟨b,n,appendStack transferred [resume .l102795 0x102795],?_,rsp,df,r13,widths,?_,digest⟩
  · exact preserveAfterHash call entry.toCoreMemory writes
  · exact ⟨(congrArg Value.width (kept 39 (by decide))).trans mx,
      (congrArg Value.width (kept 50 (by decide))).trans tag,
      (congrArg Value.width (kept 51 (by decide))).trans control⟩

end K256.Proofs.Signing.Composition
