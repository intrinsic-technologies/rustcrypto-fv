import Hkdf.Proofs.Common.SHA256.State
import Hkdf.Proofs.Common.Machine.StackRegion
import Hkdf.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {hash : Array UInt32} {input : ByteArray} {count : Nat}

def LocalWrite (initial : RamState) (address : BitVec 64) : Prop :=
  (registerRegion initial .rdi 32).Contains address.toNat ∨
    (stackPtr initial).toNat - 336 ≤ address.toNat ∧
    address.toNat < (stackPtr initial).toNat - 48

omit [Bindings] in
theorem localWrite_within
    {address : BitVec 64} (h : LocalWrite initial address) :
    ∃ region ∈ #v[registerRegion initial .rdi 32, Stack.region initial 336],
      region.Contains address.toNat := by
  rcases h with h | h
  · exact ⟨_, by simp, h⟩
  · refine ⟨Stack.region initial 336, by simp, ?_⟩
    change (stackPtr initial).toNat - 336 ≤ address.toNat ∧
      address.toNat < (Stack.region initial 336).start + (Stack.region initial 336).size
    rw [stack_region_end]
    exact ⟨h.1, by omega⟩

theorem localWrite_not_saved (pre : CompressionPre initial boundary hash input count)
    {offset i : Nat} (ho : offset ≤ 48) (hi : i < 8) (hio : i ≤ offset) :
    ¬ LocalWrite initial (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
  have bound := Hkdf.Proofs.Common.Encoding.Serialize.stack_bounds pre.toCalleePre
  have sub := Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_toNat pre.toCalleePre
    (offset := offset) (by omega)
  have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [BitVec.toNat_add, sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  intro h
  rcases h with h | h
  · apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ h
    change (stackPtr initial).toNat - 336 ≤ _ ∧
      _ < (Stack.region initial 336).start + (Stack.region initial 336).size
    rw [stack_region_end, address]
    constructor <;> omega
  · rw [address] at h
    omega

theorem FrameState.after_agrees (pre : CompressionPre initial boundary hash input count)
    (state : FrameState initial s) {cs : List Component} (ready : ReadyToStep t)
    (h : AgreesExcept cs s t) (hsp : .reg 4 ∉ cs)
    (hwrite : ∀ c ∈ cs, ∀ address, c.Covers address → LocalWrite initial address)
    (hdf : .df ∉ cs) (hmxcsr : .mxcsr ∉ cs) (hfcw : .fcw ∉ cs) :
    FrameState initial t := by
  have writes : WritesWithin cs #v[registerRegion initial .rdi 32, Stack.region initial 336] := by
    intro c hc address ha
    exact localWrite_within (hwrite c hc address ha)
  refine ⟨supportedMachine_of_ready_agrees state.machine ready h, ?_,
    h.directionFlagClear hdf state.directionFlag, fun a ha => h.grow a (state.allocated a ha),
    ?_, (h.read (n := 64) (r := 4) hsp).trans state.rsp, ?_, ?_,
    (h.mxcsr hmxcsr).trans state.mxcsr,
    (h.fcw hfcw).trans state.fp87⟩
  · intro a b hb
    rw [h.memory a]
    · exact state.loaded a b hb
    · intro c hc ha
      obtain ⟨region, hr, hin⟩ := writes c hc a ha
      exact pre.avoids region (by simpa using hr) a hin (.inl ⟨b, hb⟩)
  · intro a ha
    rw [h.memoryWriteFrame writes a ha]
    exact state.frame a ha
  · intro entry he
    rw [Hkdf.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h]
    · exact state.saved entry he
    · intro i hi c hc hcov
      apply localWrite_not_saved pre (offset := entry.2) ?_ hi ?_ (hwrite c hc _ hcov)
      all_goals
        simp only [Hkdf.Proofs.Common.Encoding.Serialize.savedRegisters,
          List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  · rw [Hkdf.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h]
    · exact state.returnAddress
    · intro i hi c hc hcov
      have cov := hwrite c hc _ hcov
      change LocalWrite initial (stackPtr initial + BitVec.ofNat 64 i) at cov
      have bound := Hkdf.Proofs.Common.Encoding.Serialize.stack_bounds pre.toCalleePre
      rcases cov with cov | cov
      · apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ cov
        apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
        · exact Nat.sub_le _ _
        · rw [stack_region_end]
          omega
      · have address : (stackPtr initial + BitVec.ofNat 64 i).toNat =
            (stackPtr initial).toNat + i := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        rw [address] at cov
        omega

end Hkdf.Proofs.Common.SHA256
