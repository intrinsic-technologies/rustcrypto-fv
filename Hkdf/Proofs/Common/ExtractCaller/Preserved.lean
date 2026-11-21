import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Common.ExtractCaller.State
import Hkdf.Proofs.Standard.Memory

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common CallFrame

theorem standard_pad_preserved [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) :
    ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧ ReadyToStep t ∧
      Standard.Preserved initial t ∧
      Pad.Pre .v1014a0 (returnBoundary initial) t (stackPtr initial - 400)
        (HMAC.keyBlock (Standard.saltKey salt)) := by
  obtain ⟨s, preserved, rip, rsp, rcx, r8⟩ := standard_middle ctx
  obtain ⟨k, keyRunning, keyCtx, keyRsp, output, ret, before, _⟩ :=
    EnterKey.run false ctx.environment ctx.call preserved.toRunning rip rsp rcx r8
  obtain ⟨fuel, t, run, ready, final, rspT, pre, after, _⟩ :=
    Normalize.standard ctx.call keyRunning keyCtx keyRsp output ret
  have bounds := Standard.stack_bounds ctx
  have observed (offset size : Nat) (low : offset ≤ 520)
      (high : size ≤ offset + 8) (side : offset ≤ 48 ∨ 400 + size ≤ offset) :
      (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) size).Agrees s t := by
    have address := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := offset) (by change offset ≤ 1792; omega)
    have bounded : (stackPtr initial - BitVec.ofNat 64 offset).toNat + size ≤ 2^64 := by
      rw [address]
      omega
    have first : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) size).Agrees s k := by
      apply frame_agrees_of_disjoint before bounded
      intro region member a ha hb
      have query : (stackPtr initial).toNat - offset ≤ a ∧
          a < (stackPtr initial).toNat - offset + size := by
        simpa only [MemoryRegion.Contains, address] using ha
      have cases : region = (⟨(stackPtr initial - (224 : BitVec 64)).toNat, 32⟩ : MemoryRegion) ∨
          region = (⟨(stackPtr initial - (528 : BitVec 64)).toNat, 8⟩ : MemoryRegion) := by
        simpa [EnterKey.layout, KeyContext.standardLayout] using member
      rcases cases with rfl | rfl
      · have zeroAddress := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 224) (by decide)
        change (stackPtr initial - (224 : BitVec 64)).toNat ≤ a ∧ a < (stackPtr initial - (224 : BitVec 64)).toNat + 32 at hb
        have converted : (stackPtr initial - (224 : BitVec 64)).toNat =
            (stackPtr initial).toNat - 224 := zeroAddress
        rw [converted] at hb
        rcases side with side | side <;> omega
      · have slotAddress := Hkdf.Proofs.Common.CallFrame.stack_sub_toNat ctx.call.stack (offset := 528) (by decide)
        change (stackPtr initial - (528 : BitVec 64)).toNat ≤ a ∧ a < (stackPtr initial - (528 : BitVec 64)).toNat + 8 at hb
        have converted : (stackPtr initial - (528 : BitVec 64)).toNat =
            (stackPtr initial).toNat - 528 := slotAddress
        rw [converted] at hb
        omega
    have second : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) size).Agrees k t := by
      apply frame_agrees_of_disjoint after bounded
      apply stack_layout_disjoint ctx.call.stack KeyContext.standardLayout keyRsp output
      · rcases side with side | side
        · exact Or.inl (by change offset + 64 ≤ 400; omega)
        · exact Or.inr side
      · change offset + 8 ≤ 528
        omega
    exact first.trans second
  have saved := observed 48 56 (by decide) (by decide) (Or.inl (by decide))
  have persistent : ∀ offset ∈ ([8, 96, 104, 112] : List Nat),
      (Component.mem (Standard.frameBase initial + BitVec.ofNat 64 offset) 8).Agrees s t := by
    intro offset member
    have bound : offset ≤ 112 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    have offsetLow : 8 ≤ offset := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    have equal : Standard.frameBase initial + BitVec.ofNat 64 offset =
        stackPtr initial - BitVec.ofNat 64 (520 - offset) := by
      have e := Standard.stack_address preserved.rsp (offset := offset) (by omega)
      simpa only [show rspOf s = Standard.frameBase initial from preserved.rsp] using e
    rw [equal]
    exact observed (520 - offset) 8 (by omega) (by omega) (Or.inr (by omega))
  exact ⟨fuel, t, run, ready,
    preserved.of_observations final saved persistent rspT, pre⟩

end Hkdf.Proofs.Common.ExtractCaller
