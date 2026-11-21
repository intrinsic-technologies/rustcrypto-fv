import P256.Proofs.Signing.Wrapper.Entry.Decode.Block
import P256.Proofs.Signing.Wrapper.Entry.Decode.State
import P256.Proofs.Program.StackBuffer

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

variable [Bindings] {initial s : RamState} {secret message : ByteArray} {slices : Array Input}

theorem stack_address (state : State initial s 520) {off : Nat} (bound : off ≤ 520) :
    stackPtr s + BitVec.ofNat 64 off = stackPtr initial - BitVec.ofNat 64 (520-off) := by
  have h : BitVec.ofNat 64 (520-off) = (520 : BitVec 64)-BitVec.ofNat 64 off := by
    symm
    exact BitVec.ofNat_sub_ofNat_of_le 520 off (by omega) bound
  rw [state.rsp,h]
  simp only [BitVec.sub_eq_add_neg,BitVec.neg_add,BitVec.neg_neg,BitVec.add_assoc,BitVec.ofNat_eq_ofNat]


set_option maxRecDepth 4096 in
theorem block_pre (call : ValidCallWithSlices signingKeyTrySign initial [secret,message] slices)
    (state : State initial s 520) {p : BitVec 64} {reads writes : List (Nat × Nat)}
    (rip : s.RIP = p) (readBound : ∀ pair ∈ reads, pair.1+pair.2 ≤ 520)
    (writeBound : ∀ pair ∈ writes, pair.1+pair.2 ≤ 472 ∧ 0 < pair.2) : BlockPre p reads writes s := by
  have hs : Stack.Valid initial 5112 := call.stackAvailable.1
  have avoids : (Stack.region initial 5112).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    by simpa only [signingKeyTrySign] using call_stack_avoids call
  refine ⟨rip,?_,?_,?_⟩
  · intro pair hp
    have hb := readBound pair hp
    rw [stack_address state (by omega)]
    exact readable_of_grow (stack_sub_readable hs
      (offset := 520-pair.1) (len := pair.2) (by omega) (by omega)) state.allocated
  · intro pair hp
    have hb := writeBound pair hp
    rw [stack_address state (by omega)]
    exact stack_buffer_writable hs avoids state.allocated
      (offset := 520-pair.1) (by omega) (by omega) (by omega)
  · intro pair hp code len hc
    have hb := writeBound pair hp
    rw [stack_address state (by omega)]
    exact stack_buffer_code_apart hs avoids
      (offset := 520-pair.1) (by omega) (by omega) hc


theorem stack_work (call : ValidCallWithSlices signingKeyTrySign initial [secret,message] slices)
    (state : State initial s 520) {off len : Nat} {a : BitVec 64}
    (bound : off+len ≤ 472)
    (covered : (Component.mem (stackPtr s+BitVec.ofNat 64 off) len).Covers a) :
    (workRegion initial).Contains a.toNat := by
  have hs : Stack.Valid initial 5112 := call.stackAvailable.1
  rw [stack_address state (by omega)] at covered
  exact work_contains hs (offset := 520-off) (by omega) (by omega) covered

omit [Bindings] in
theorem stack_byte_preserved {t u : RamState} {cs : List Component} {target len i : Nat}
    (agrees : AgreesExcept cs t u) (bound : target + len ≤ 520) (hi : i < len)
    (memory : ∀ p n, Component.mem p n ∈ cs → ∃ off,
      off + n ≤ 472 ∧ (off + n ≤ target ∨ target + len ≤ off) ∧
      p = stackPtr t + BitVec.ofNat 64 off) :
    u.external[stackPtr t + BitVec.ofNat 64 target + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 target + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc covered
  cases c with
  | mem p n =>
    obtain ⟨off, size, apart, rfl⟩ := memory p n hc
    obtain ⟨j, hj, equal⟩ := covered
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add] at equal
    have h := congrArg BitVec.toNat ((BitVec.add_right_inj (stackPtr t)).mp equal)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : target + i < 2^64),
      Nat.mod_eq_of_lt (by omega : off + j < 2^64)] at h
    omega
  | _ => exact covered.elim

omit [Bindings] in
theorem stack_memLoad_preserved {t u : RamState} {cs : List Component} {target width : Nat}
    (agrees : AgreesExcept cs t u) (bound : target + width / 8 ≤ 520)
    (memory : ∀ p n, Component.mem p n ∈ cs → ∃ off,
      off + n ≤ 472 ∧ (off + n ≤ target ∨ target + width / 8 ≤ off) ∧
      p = stackPtr t + BitVec.ofNat 64 off) :
    memLoad u.external (stackPtr t + BitVec.ofNat 64 target) width =
      memLoad t.external (stackPtr t + BitVec.ofNat 64 target) width := by
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr t + BitVec.ofNat 64 target + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr t + BitVec.ofNat 64 target + BitVec.ofNat 64 i]?).getD 0
  rw [stack_byte_preserved agrees bound hi memory]



theorem after_stack {t : RamState} {cs : List Component} {fuel : Nat}
    (call : ValidCallWithSlices signingKeyTrySign initial [secret,message] slices)
    (state : State initial s 520) (run : Advances (returnBoundary initial) fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ p n, Component.mem p n ∈ cs → ∃ off,
      off+n ≤ 472 ∧ p = stackPtr s+BitVec.ofNat 64 off)
    (rsp : .reg 4 ∉ cs) (df : Component.df ∉ cs) : State initial t 520 := by
  apply state.after_effect call run ready agrees ?_
    ((agrees.read (n:=64) (r:=4) rsp).trans state.rsp) df
  intro c hc a covered
  cases c with
  | mem p n =>
    obtain ⟨off,bound,rfl⟩ := memory p n hc
    exact ⟨workRegion initial,by simp,stack_work call state bound covered⟩
  | _ => exact covered.elim

end P256.Proofs.Signing.Wrapper.Entry.Decode
