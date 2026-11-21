import P256.Proofs.EcdhWrapper.Multiply.Pre

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Multiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev work (initial : RamState) := ScalarFrame.Work.region initial 4104 472

theorem push_writes {initial s : RamState} (stack : Stack.Valid initial 4104)
    (rsp : stackPtr s=stackPtr initial-504)
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
  change (stackPtr initial).toNat-4104 ≤ _ ∧ _ < (stackPtr initial).toNat-4104+(4104-472)
  constructor <;> omega

theorem wrapper_memory [Bindings] {initial s t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (frame : MemoryWriteFrame s t #v[work initial]) :
    MemoryWriteFrame s t (wrapperRegions ecdhDiffieHellman initial) := by
  apply Peer.Pad.wrapper_memory call
  intro a ha
  apply frame a
  intro r hr hin
  have eq : r=work initial := by simpa using hr
  subst r
  apply ha (Peer.Pad.work initial) (by simp)
  change (stackPtr initial).toNat-4104 ≤ _ ∧ _ < (stackPtr initial).toNat-4104+(4104-264)
  change (stackPtr initial).toNat-4104 ≤ _ ∧ _ < (stackPtr initial).toNat-4104+(4104-472) at hin
  constructor <;> omega

theorem upper_read {initial s t : RamState} (stack : Stack.Valid initial 4104)
    (frame : MemoryWriteFrame s t #v[work initial]) {offset n : Nat}
    (offsetBound : offset≤472) (widthBound : n/8≤offset+8) :
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
    change _≤_ ∧ _<(stackPtr initial).toNat-4104+(4104-472) at hin
    rw [toNat_add_ofNat _ _ (by rw [low]; omega),low] at hin
    omega

end P256.Proofs.EcdhWrapper.Multiply
