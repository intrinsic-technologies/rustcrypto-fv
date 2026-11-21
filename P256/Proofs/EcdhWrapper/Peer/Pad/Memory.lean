import P256.Proofs.EcdhWrapper.Peer.Guards
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.ScalarFrame.Work
import P256.Proofs.Program.Call
import P256.Proofs.Program.CalleeStackFrame
import P256.Proofs.Program.ScalarFrame.CallStep

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial s t u : RamState} {secret peer : ByteArray} {slices : Array Input}

abbrev work (initial : RamState) := ScalarFrame.Work.region initial 4104 264

theorem work_subset (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    {a : Nat} (h : (work initial).Contains a) : (Stack.region initial 4104).Contains a := by
  have bounds := stack_bounds (show Stack.Valid initial 4104 from call.stackAvailable.1)
  change (stackPtr initial).toNat-4104 ≤ a ∧ a < (stackPtr initial).toNat-4104+(4104-264) at h
  change (stackPtr initial).toNat-4104 ≤ a ∧ a < (Stack.region initial 4104).start+(Stack.region initial 4104).size
  rw [stack_region_end]
  constructor <;> omega

theorem wrapper_memory (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (frame : MemoryWriteFrame s t #v[work initial]) :
    MemoryWriteFrame s t (wrapperRegions ecdhDiffieHellman initial) := by
  intro a ha
  apply frame a
  intro r hr hin
  have eq : r=work initial := by simpa using hr
  subst r
  exact ha (callStack ecdhDiffieHellman initial) (by simp [wrapperRegions])
    (stack_contains_callStack (routine := ecdhDiffieHellman) (work_subset call hin))

theorem loaded_after (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (frame : MemoryWriteFrame s t #v[work initial]) (loaded : ProgramLoaded s) : ProgramLoaded t := by
  intro a b hb
  rw [frame a]
  · exact loaded a b hb
  · intro r hr hin
    have eq : r=work initial := by simpa using hr
    subst r
    exact call_stack_avoids call a (work_subset call hin) (.inl ⟨b,hb⟩)

omit [Bindings] in
theorem push_writes (stack : Stack.Valid initial 4104) (rsp : stackPtr s=stackPtr initial-504)
    {target : RamState → BitVec 64} {ret : BitVec 64} :
    WritesWithin (callEffect target ret s).components #v[work initial] := by
  have addr : pushAddr s=stackPtr initial-512#64 := by rw [pushAddr,rsp,BitVec.sub_sub]; rfl
  have bounds := stack_bounds stack
  intro c hc a ha
  simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl <;> try exact ha.elim
  rw [addr] at ha
  obtain ⟨i,hi,rfl⟩ := ha
  refine ⟨work initial,by simp,?_⟩
  rw [toNat_add_ofNat _ _ (by rw [stack_sub_toNat stack (by decide : 512≤4104)]; omega),
    stack_sub_toNat stack (by decide : 512≤4104)]
  change (stackPtr initial).toNat-4104 ≤ _ ∧ _ < (stackPtr initial).toNat-4104+(4104-264)
  constructor <;> omega

theorem result_memory (stack : Stack.Valid initial 4104)
    {boundary : ReturnBoundary} {target ret : BitVec 64} {offset count : Nat}
    (rsp : stackPtr s=stackPtr initial-504)
    (effect : (callEffect (fun _ ↦ target) ret s).Holds s t)
    (destination : t.regValue .rdi=stackPtr initial-BitVec.ofNat 64 offset)
    (bound : offset≤504) (extent : count+264≤offset)
    (result : CalleeResult t u boundary count 0) : MemoryWriteFrame s u #v[work initial] := by
  apply memoryWriteFrame_trans (effect.agrees.memoryWriteFrame (push_writes stack rsp))
  have sp : stackPtr t=stackPtr initial-512#64 := by
    have h : stackPtr t=pushAddr s := effect.writes.1
    rw [h,pushAddr,rsp,BitVec.sub_sub]; rfl
  have bounds := stack_bounds stack
  have st : (stackPtr t).toNat=(stackPtr initial).toNat-512 := by
    rw [sp]; exact stack_sub_toNat stack (by decide)
  have dt : (t.regValue .rdi).toNat=(stackPtr initial).toNat-offset := by
    rw [destination]; exact stack_sub_toNat stack (by omega)
  intro a ha
  apply result.frame a
  intro region hr hin
  have cases : region=registerRegion t .rdi count ∨ region=Stack.region t 0 := by simpa using hr
  apply ha (work initial) (by simp)
  change (stackPtr initial).toNat-4104 ≤ a.toNat ∧ a.toNat < (stackPtr initial).toNat-4104+(4104-264)
  rcases cases with rfl | rfl
  · change (t.regValue .rdi).toNat≤a.toNat ∧ a.toNat<(t.regValue .rdi).toNat+count at hin
    rw [dt] at hin
    constructor <;> omega
  · change (stackPtr t).toNat-0≤a.toNat ∧ a.toNat<(Stack.region t 0).start+(Stack.region t 0).size at hin
    rw [stack_region_end,st] at hin
    constructor <;> omega

theorem result_word (stack : Stack.Valid initial 4104)
    {boundary : ReturnBoundary} {target ret : BitVec 64} {outputOffset count offset : Nat}
    (rsp : stackPtr s=stackPtr initial-504)
    (effect : (callEffect (fun _ ↦ target) ret s).Holds s t)
    (destination : t.regValue .rdi=stackPtr initial-BitVec.ofNat 64 outputOffset)
    (result : CalleeResult t u boundary count 0)
    (bound : offset≤504) (apart : outputOffset+8≤offset) :
    memLoad u.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
  have sp : stackPtr t=stackPtr initial-512#64 := by
    have h : stackPtr t=pushAddr s := effect.writes.1
    rw [h,pushAddr,rsp,BitVec.sub_sub]; rfl
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?).getD 0=_
  rw [CalleeResult.stack_byte (frameOffset := 504) (len := 8) stack sp result destination
    (by decide) (by omega) bound (by omega) (.inr apart) hi]
  rw [ScalarFrame.call_byte (frameOffset := 504) (by decide) rsp effect bound (by omega) hi]
  rfl

theorem peer_disjoint (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    {address : BitVec 64} (pointer : memLoad initial.external (initial.regValue .rdi+8) 64=address) :
    (MemoryRegion.mk address.toNat peer.size).Disjoint (Stack.region initial 4104) := by
  have count : slices.size=2 := by
    have h := congrArg Array.size call.slicesHoldInputs
    simpa only [inputBytes,Array.size_map,List.size_toArray,List.length_cons,List.length_nil,Nat.reduceAdd] using h
  have index : 1<slices.size := by omega
  have bytes : slices[1].bytes=peer := by
    have h := congrArg (fun xs : Array ByteArray ↦ xs[1]?) call.slicesHoldInputs
    change (inputBytes slices)[1]?=some peer at h
    simpa only [inputBytes,Array.getElem?_map,Array.getElem?_eq_getElem index,
      Option.map_some,Option.some.injEq] using h
  have addr : slices[1].address=address := by
    have h := input_pointer_memLoad call.inputsInMemory ⟨1,index⟩
    have hp : memLoad initial.external (initial.regValue .rdi+8#64) 64=address := pointer
    simpa only [Fin.getElem_fin,Nat.mul_one,hp] using h.symm
  have member : slices[1].region ∈ readRegions initial slices := by
    simp only [readRegions,List.mem_cons]
    right; right
    simpa using (Array.mem_map.mpr ⟨slices[1],Array.getElem_mem index,rfl⟩ :
      slices[1].region ∈ slices.map Input.region)
  have apart := wrapper_read_disjoint call member (callStack ecdhDiffieHellman initial)
    (by simp [wrapperRegions])
  intro a ha hb
  apply apart a _ (stack_contains_callStack hb)
  simpa only [Input.region,bytes,addr] using ha

theorem peer_bytes (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    {address : BitVec 64} (pointer : memLoad initial.external (initial.regValue .rdi+8) 64=address)
    (bound : (MemoryRegion.mk address.toNat peer.size).Bounded)
    (frame : MemoryWriteFrame s t #v[work initial])
    (bytes : (MemoryRegion.mk address.toNat peer.size).HasBytes s.external peer) :
    (MemoryRegion.mk address.toNat peer.size).HasBytes t.external peer := by
  apply frame_hasBytes frame _ bound bytes
  intro r hr a ha hb
  have eq : r=work initial := by simpa using hr
  subst r
  exact peer_disjoint call pointer a ha (work_subset call hb)

omit [Bindings] in
theorem upper_read (stack : Stack.Valid initial 4104)
    (frame : MemoryWriteFrame s t #v[work initial]) {offset n : Nat}
    (offsetBound : offset≤264) (widthBound : n/8≤offset+8) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) n =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) n := by
  have bounds := stack_bounds stack
  have low := stack_sub_toNat stack (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?).getD 0=_
  rw [frame _]
  · rfl
  · intro region hr hin
    have eq : region=work initial := by simpa using hr
    subst region
    change _≤_ ∧ _<(stackPtr initial).toNat-4104+(4104-264) at hin
    rw [toNat_add_ofNat _ _ (by rw [low]; omega),low] at hin
    omega

end P256.Proofs.EcdhWrapper.Peer.Pad
