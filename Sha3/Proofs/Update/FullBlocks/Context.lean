import Sha3.Proofs.Update.Layout
import Sha3.Proofs.Update.FullBlocks.Basic

namespace Sha3.Proofs.Update.FullBlocks

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program
open Keccak Permutation

theorem state_contains [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (h : CallContext v initial bytes state)
    {i : Nat} (hi : i < 201) :
    (stateRegion initial).Contains (initial.regValue .rsi + .ofNat 64 i).toNat := by
  have hl := h.stateRead.low
  simp only [stateRegion, MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> omega

theorem input_contains [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (h : CallContext v initial bytes state)
    {i : Nat} (hi : i < bytes.size) :
    (⟨(initial.regValue .rdx).toNat, bytes.size⟩ : MemoryRegion).Contains
      (initial.regValue .rdx + .ofNat 64 i).toNat := by
  have hl := h.inputRead.low
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> omega

theorem input_bytes [Bindings] {v : Variant} {initial s : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hCall : CallContext v initial bytes state)
    (hInv : BodyInvariant initial s) :
    BytesAt s (initial.regValue .rdx) bytes.data.toList := by
  intro i hi
  have hi' : i < bytes.size := by simpa only [Array.length_toList, ByteArray.size] using hi
  rw [hInv.memory]
  · have he := hCall.inputBytes i hi'
    simpa only [Array.getElem?_eq_getElem hi', Option.getD_some, List.getElem_toArray,
      Array.getElem_toList] using he
  · intro region hr hcontains
    exact hCall.inputApart region hr _ (input_contains hCall hi') hcontains

theorem Context.of_invariant [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {initial s : RamState} {bytes : ByteArray} {state : Incremental.State} {offset : Nat}
    (hCall : CallContext v initial bytes state) (hInv : BodyInvariant initial s)
    (hpointer : s.regValue .r15 = initial.regValue .rsi)
    (hinput : (Operand.reg 14 : Operand 64).read s =
      initial.regValue .rdx + .ofNat 64 offset)
    (hsize : offset + 8 * v.lanes ≤ bytes.size) (hb : ¬ InProgram boundary.rip) :
    Context boundary v (Update.frameBase initial) (initial.regValue .rsi)
      (initial.regValue .rdx + .ofNat 64 offset) s := by
  have his : MemReadable s (initial.regValue .rdx) bytes.size :=
    ⟨hCall.inputRead.low, fun i hi ↦ hInv.grows _ (hCall.inputRead.mem i hi)⟩
  have hsr : MemReadable s (initial.regValue .rsi) 200 :=
    ⟨by have := hCall.stateRead.low; omega,
      fun i hi ↦ hInv.grows _ (hCall.stateRead.mem i (by omega))⟩
  refine ⟨hInv.ready, hInv.loaded, hInv.stack, hpointer, hinput,
    readable_slice his _ _ hsize, hsr, ?_, ?_, hb⟩
  · intro i hi j hj he
    have hs := state_contains hCall (i := i) (by omega)
    have hr := input_contains hCall (i := offset + j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hr
    rw [he] at hs
    exact hCall.inputApart (stateRegion initial) (by simp [writeRegions]) _ hr hs
  · intro i hi
    exact hCall.avoids (stateRegion initial) (by simp [writeRegions]) _
      (state_contains hCall (by omega))

theorem cursor_of_frame {pointer : BitVec 64} {s t : RamState}
    (h : AgreesExcept (clobbers pointer) s t) :
    cursor pointer t = cursor pointer s := by
  unfold cursor
  congr 1
  change memLoad t.external (pointer + 200) 8 = memLoad s.external (pointer + 200) 8
  apply memLoad_congr
  intro j hj
  apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
  apply h.byte
  intro c hc hcover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨i, hi, he⟩ := hcover
  exact RangeApart.offsets pointer (a := 200) (len := 1) (b := 0) (count := 200)
    (by decide) (by decide) (Or.inr (by decide)) j hj i hi
    (by simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using he)

end Sha3.Proofs.Update.FullBlocks
