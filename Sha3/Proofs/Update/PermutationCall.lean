import Sha3.Proofs.Update.PermutationFrame
import Sha3.Proofs.Permutation.Execution

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

private theorem range_contains {base : BitVec 64} {count i : Nat}
    (hl : base.toNat + count ≤ 2 ^ 32) (hi : i < count) :
    (⟨base.toNat, count⟩ : MemoryRegion).Contains (base + BitVec.ofNat 64 i).toNat := by
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> omega

theorem permutationFrameBase {initial called : RamState}
    (hsp : called.regValue .rsp = initial.regValue .rsp - 64) :
    Permutation.frameBase called = stackBase initial := by
  simp only [Permutation.frameBase, hsp, stackBase, BitVec.sub_sub]
  rfl

theorem permutationCallPre [Bindings] {v : Variant} {initial called : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    (hsp : called.regValue .rsp = initial.regValue .rsp - 64)
    (hp : called.regValue .rdi = initial.regValue .rsi)
    (hgrows : ∀ address : BitVec 64, (initial.external[address]?).isSome →
      (called.external[address]?).isSome)
    (hip : called.RIP = Permutation.entryAddress .absorb)
    (hret : InProgram (stackTop called)) : Permutation.CallPre .absorb called := by
  have hf := permutationFrameBase hsp
  have hs : Stack.Valid called 264 :=
    stackValid_nested hc.stack (by decide) (by decide : 64 % 16 = 0) hsp hgrows
  have he : Stack.region called 264 = ⟨(stackBase initial).toNat, 272⟩ := by
    have hnat : (called.regValue .rsp).toNat = (initial.regValue .rsp).toNat - 64 := by
      rw [hsp]
      exact stack_sub_toNat hc.stack.2.2.1 (by decide)
    have hu : 328 ≤ (initial.regValue .rsp).toNat := hc.stack.2.2.1
    simp only [Stack.region, Stack.returnAddressBytes, hnat, stackBase_toNat hc.stack]
    rw [MemoryRegion.mk.injEq]
    constructor <;> omega
  refine ⟨hip, hs, ?_, ?_, ?_, ?_, hret⟩
  · change (Stack.region called 264).Avoids _
    rw [he]
    intro address ha
    change (stackBase initial).toNat ≤ address.toNat ∧ address.toNat < (stackBase initial).toNat + 272 at ha
    apply hc.avoids ⟨(stackBase initial).toNat, stackBytes⟩ (by simp [writeRegions]) address
    exact ⟨ha.1, by have := ha.2; dsimp only [stackBytes] at *; omega⟩
  · rw [hp]
    exact ⟨by have := hc.stateRead.low; omega,
      fun i hi ↦ hgrows _ (hc.stateRead.mem i (by omega))⟩
  · rw [hp, hf]
    exact fun i hi j hj ↦ hc.stateStack i (by omega) j (by omega)
  · intro i hi
    rw [hp]
    exact hc.avoids (stateRegion initial) (by simp [writeRegions]) _
      (range_contains hc.stateRead.low (by omega))

theorem permutationResult_regions {initial called final : RamState} {lanes : Keccak.Lanes}
    (hsp : called.regValue .rsp = initial.regValue .rsp - 64)
    (hp : called.regValue .rdi = initial.regValue .rsi)
    (hr : Permutation.CallResult called final lanes) :
    MemoryWriteFrame called final (permutationRegions initial) := by
  apply memoryWriteFrame_mono hr.memory
  intro region hregion address ha
  simp only [Permutation.writeRegions, Vector.mem_mk, List.mem_toArray,
    List.mem_cons, List.not_mem_nil, or_false] at hregion
  rcases hregion with rfl | rfl
  · refine ⟨⟨(stackBase initial).toNat, 272⟩, by simp [permutationRegions], ?_⟩
    rw [permutationFrameBase hsp] at ha
    change (stackBase initial).toNat ≤ address ∧ address < (stackBase initial).toNat + 264 at ha
    exact ⟨ha.1, by have := ha.2; change address < (stackBase initial).toNat + 272; omega⟩
  · refine ⟨⟨(initial.regValue .rsi).toNat, 200⟩, by simp [permutationRegions], ?_⟩
    simpa only [hp] using ha

private theorem push_address [Bindings] {initial s : RamState}
    (h : BodyInvariant initial s) :
    pushAddr s = stackBase initial + 264 := by
  change s.regValue .rsp - 8 = _
  rw [h.stack]
  simp only [frameBase, stackBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  exact congrArg (initial.regValue .rsp + ·) (by decide +kernel)

private theorem call_state_lanes [Bindings] {v : Variant} {initial s called : RamState}
    {bytes : ByteArray} {state : Incremental.State} {ret : BitVec 64}
    (hc : CallContext v initial bytes state) (h : BodyInvariant initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .absorb) ret s).Holds s called) :
    Permutation.memoryLanes (initial.regValue .rsi) called =
      Permutation.memoryLanes (initial.regValue .rsi) s := by
  funext lane
  apply memLoad_congr
  intro j hj
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  apply he.agrees.memory
  intro c hcm hcover
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl | rfl
  · exact hcover.elim
  · obtain ⟨i, hi, heq⟩ := hcover
    apply hc.stateStack (8 * lane.val + j) (by have := lane.isLt; omega)
      (264 + i) (by omega)
    simpa only [push_address h, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc] using heq
  · exact hcover.elim

theorem permutation_advance [Bindings] {v : Variant} {initial s : RamState}
    {bytes : ByteArray} {state : Incremental.State}
    (hc : CallContext v initial bytes state) (h : BodyInvariant initial s)
    (boundary : ReturnBoundary) (hb : ¬ InProgram boundary.rip)
    (pc : BitVec 64) (disp : BitVec 32) (hip : s.RIP = pc)
    (hp : s.regValue .rdi = initial.regValue .rsi)
    (hcode : ∀ byte ∈ codeRange pc (encodeCallRel32 disp),
      byte.1.toNat < userAddressLimit ∧
        Extracted.programSections.fetchByte byte.1 = some byte.2)
    (htarget : branchTarget pc 5 (disp.signExtend 64) = Permutation.entryAddress .absorb)
    (hret : InProgram (BitVec.add pc 5#64)) :
    ∃ t : RamState, Advances boundary 6340 s t ∧ BodyInvariant initial t ∧ t.RIP = BitVec.add pc 5#64 ∧
      CalleeSavedRegistersUnchanged s t ∧
      Permutation.memoryLanes (initial.regValue .rsi) t =
        Keccak.keccakLanes (Permutation.memoryLanes (initial.regValue .rsi) s) ∧
      cursor (initial.regValue .rsi) t = cursor (initial.regValue .rsi) s ∧
      (Operand.mem (frameBase initial) : Operand 64).read t =
        (Operand.mem (frameBase initial) : Operand 64).read s := by
  have hpush := push_address h
  have hpushread : MemReadable s (pushAddr s) 8 := by
    rw [hpush]
    exact readable_slice (h.readable hc.stackRead) 264 8 (by decide)
  have hpage : (pushAddr s).toNat % 4096 + 8 ≤ 4096 := by
    have hsp : pushAddr s = initial.regValue .rsp - BitVec.ofNat 64 64 := by
      change s.regValue .rsp - 8 = _
      rw [h.stack]
      simp only [frameBase, BitVec.sub_sub]
      rfl
    rw [hsp, stack_sub_toNat hc.stack.2.2.1 (by decide)]
    have halign : (initial.regValue .rsp).toNat % 16 = 8 := hc.stack.2.2.2
    have hmin : 328 ≤ (initial.regValue .rsp).toNat := hc.stack.2.2.1
    omega
  have hwrite : ∀ i, i < 8 → ∃ region ∈ permutationRegions initial,
      region.Contains (pushAddr s + BitVec.ofNat 64 i).toNat := by
    intro i hi
    refine ⟨⟨(stackBase initial).toNat, 272⟩, by simp [permutationRegions], ?_⟩
    rw [hpush]
    have he : stackBase initial + 264 + BitVec.ofNat 64 i =
        stackBase initial + BitVec.ofNat 64 (264 + i) := by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
    rw [he]
    exact range_contains (by have := stackBase_low hc.stack; omega) (by omega)
  have havoid : ∀ region ∈ permutationRegions initial, region.Avoids InPageTables := by
    intro region hr address ha htable
    obtain ⟨target, ht, hin⟩ := permutationRegions_within initial region hr address.toNat ha
    exact hc.avoids target ht address hin (.inr htable)
  have code : CodeIn (codeRange pc (encodeCallRel32 disp)) s :=
    fun byte hx ↦ ⟨(hcode byte hx).1, programLoaded_fetchByte h.loaded (hcode byte hx).2⟩
  have stepEffect := call_rel32_effect_step_of_readable
    (pre := fun t ↦ t = s) (fun _ ↦ permutationRegions initial)
    (by intro t ht; subst t; exact hwrite)
    (by intro t _; exact havoid) disp
    (by intro t ht; subst t; exact ⟨hip, hpushread⟩)
    (by intro t ht; subst t; exact hpage)
    (by rw [htarget]; decide +kernel)
  obtain ⟨called, hstep, hready, he⟩ := stepEffect s h.ready code rfl
  rw [htarget] at he
  have hcalledsp : called.regValue .rsp = initial.regValue .rsp - 64 := by
    have heq : called.regValue .rsp = pushAddr s := he.writes.1
    rw [heq]
    change s.regValue .rsp - 8 = _
    rw [h.stack]
    simp only [frameBase, BitVec.sub_sub]
    rfl
  have hcalledptr : called.regValue .rdi = initial.regValue .rsi := by
    exact (he.agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans hp
  have hgrows : ∀ address : BitVec 64, (initial.external[address]?).isSome →
      (called.external[address]?).isSome := fun address ha ↦ he.agrees.grow address (h.grows address ha)
  have hframe : MemoryWriteFrame s called (permutationRegions initial) := by
    apply he.agrees.memoryWriteFrame
    intro c hcm address ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl
    · exact ha.elim
    · obtain ⟨i, hi, rfl⟩ := ha
      exact hwrite i hi
    · exact ha.elim
  have hloaded : ProgramLoaded called := by
    apply programLoaded_of_memoryWriteFrame hframe _ h.loaded
    intro region hr address ha hprogram
    obtain ⟨target, ht, hin⟩ := permutationRegions_within initial region hr address.toNat ha
    exact hc.avoids target ht address hin (.inl hprogram)
  have hpre := permutationCallPre hc hcalledsp hcalledptr hgrows he.rip
    ((callEffect_stack he).1 ▸ hret)
  have hcodeall : CodeIn Extracted.programImage called :=
    CodeIn.of_loaded hloaded (SectionsLow.codeLow programSections_low)
  obtain ⟨t, hrun, hr, _, result⟩ :=
    Permutation.call_advance .absorb boundary hb called hready hcodeall hpre
  have hm : MemoryWriteFrame s t (permutationRegions initial) :=
    memoryWriteFrame_trans hframe (permutationResult_regions hcalledsp hcalledptr result)
  have hcallSaved : CalleeSavedRegistersUnchanged s called :=
    calleeSavedRegistersUnchanged_of_agreesExcept he.agrees (by
      intro register hregister
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hregister
      rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [pushEffect_components] <;> decide +kernel)
  have hsaved : CalleeSavedRegistersUnchanged s t :=
    fun register hr ↦ (result.saved register hr).trans (hcallSaved register hr)
  have hi : BodyInvariant initial t := by
    refine ⟨hr, ?_, ?_,
      h.saved.of_permutationRegions hc hm,
      memoryWriteFrame_trans h.memory (memoryWriteFrame_mono hm (permutationRegions_within initial)),
      fun address ha ↦ result.grows address (hgrows address ha), result.rest.trans ((he.agrees.scalarFrame_eq (by simp [Effect.components, x86_compose])).trans h.rest)⟩
    · apply programLoaded_of_memoryWriteFrame hm _ h.loaded
      intro region hregion address ha hprogram
      obtain ⟨target, ht, hin⟩ := permutationRegions_within initial region hregion address.toNat ha
      exact hc.avoids target ht address hin (.inl hprogram)
    · rw [result.stack, hcalledsp]
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      exact congrArg (initial.regValue .rsp + ·) (by decide +kernel)
  refine ⟨t, (Advances.of_step hstep (.inl ?_)).trans hrun, hi,
    result.rip.trans (callEffect_stack he).1, hsaved, ?_, permutationRegions_cursor hc hm, permutationRegions_slot hc hm⟩
  · rw [he.rip]
    intro heq
    apply hb
    rw [← heq]
    change InProgram (0x100bc0 : BitVec 64)
    exact ⟨0x55, imageSections_mem_toCodeMap_of_fetchByte (by decide +kernel)⟩
  · rw [← call_state_lanes hc h he]
    simpa only [hcalledptr] using result.lanes

end Sha3.Proofs.Update
