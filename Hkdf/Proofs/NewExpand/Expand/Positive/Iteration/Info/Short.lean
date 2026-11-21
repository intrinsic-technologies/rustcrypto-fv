import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Short.Call
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Short.Footprint
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Short.Instructions
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Short.State

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info.Short

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem absorb [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key previous info : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (saved : SavedFrame entry s boundary length) (positive : 0 < length) (allowed : length ≤ 8160)
    (pc : s.RIP = 0x10f6f0) (input : HmacAt s (stackPtr s + 272) key previous)
    (source : s.regValue .rbx = ptr) (count : s.regValue .rbp = BitVec.ofNat 64 info.size)
    (offset : s.regValue .r14 = BitVec.ofNat 64 previous.size) (memcpy : s.regValue .r12 = 0x10dd60)
    (short : previous.size + info.size < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ SavedFrame entry t boundary length ∧
      t.RIP = 0x10f70f ∧ HmacAt t (stackPtr t + 272) key (previous ++ info) ∧
      t.regValue .r12 = s.regValue .r12 ∧ t.regValue .r13 = s.regValue .r13 ∧
      slot t 440 = slot s 440 ∧ MemoryWriteFrame s t (footprint (stackPtr s) previous.size info.size) := by
  have avoids (r : MemoryRegion)
      (hr : r ∈ #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264]) :
      r.Avoids InProgram := by
    have member : r ∈ #v[registerRegion entry .rcx length, Stack.region entry 2264] := by
      simpa only [writtenLength, allowed, ↓reduceIte] using hr
    exact fun a ha hp ↦ ((pre.separation positive allowed).2 r member).2 a ha (.inl hp)
  obtain ⟨n, u, runU, readyU, setup⟩ := arguments (supportedMachine_readyToStep saved.machine)
    saved.loaded pre.call.outerBoundary pc
  have ag : AgreesExcept [.reg 7, .reg 6, .reg 2, .flags, .rip] s u := setup.agrees
  have nomem : ∀ c ∈ [Component.reg 7, .reg 6, .reg 2, .flags, .rip], ∀ a, ¬ c.Covers a := by
    simp [Component.Covers]
  have runningU := saved.toRunning.of_agrees runU readyU ag (fun c hc a ha ↦ (nomem c hc a ha).elim)
    avoids (by simp)
  have spU : stackPtr u = stackPtr s := ag.read (n := 64) (r := 4) (by decide)
  have dest : u.regValue .rdi = stackPtr u + 272 + BitVec.ofNat 64 previous.size := by
    have value : u.regValue .rdi = stackPtr s + s.regValue .r14 + 272 := setup.writes.1
    rw [value, spU, offset]
    ac_rfl
  obtain ⟨v, ⟨m, runV⟩, runningV, pcV, spV, abi, copied, copyFrame⟩ := copyCall pre runningU
    (spU.trans saved.sp) positive allowed setup.rip ((ag.read (n := 64) (r := 12) (by decide)).trans memcpy)
    dest (setup.writes.2.1.trans source) (setup.writes.2.2.trans count) short
  rw [spU] at copied copyFrame
  have spVS : stackPtr v = stackPtr s := spV.trans spU
  have destIndex : rspOf v + 335 = stackPtr entry - 201 := by
    change stackPtr v + 335 = _
    rw [spVS, show stackPtr s = stackPtr entry - 536 from saved.sp]
    bv_omega
  have writable : MemWritable v (rspOf v + 335) 1 := by
    rw [destIndex]
    exact stack_writable1 pre.call.stack pre.call.stackAvoid runningV.allocated (offset := 201) (by decide)
  have apart : RangeApart (rspOf v + 335) 1 0x10f707 8 := by
    rw [destIndex]
    exact stack_codeApart pre.call.stack (fun a ha hp ↦ pre.call.stackAvoid a ha (.inl hp))
      (offset := 201) (codeOffset := 0xf707) (by decide) (by decide) (by decide)
  obtain ⟨t, runT, readyT, pcT, index, store⟩ := storeLength
    (supportedMachine_readyToStep runningV.machine) runningV.loaded pre.call.outerBoundary pcV writable apart
  have addr : rspOf v + 335 = stackPtr s + 335 := congrArg (· + (335 : BitVec 64)) spVS
  rw [addr] at index store
  have writes : WritesWithin [.reg 5,.flags,.mem (stackPtr s + 335) 1,.rip]
      #v[(⟨(stackPtr s + 335).toNat, 1⟩ : MemoryRegion)] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> try exact ha.elim
    obtain ⟨i, hi, rfl⟩ := ha
    have : i = 0 := by omega
    subst i
    exact ⟨⟨(stackPtr s + 335).toNat, 1⟩, by simp, by simp [MemoryRegion.Contains]⟩
  have storeFrame := store.memoryWriteFrame writes
  have total : MemoryWriteFrame s t (footprint (stackPtr s) previous.size info.size) := by
    apply memoryWriteFrame_trans (t := u) (ag.memoryWriteFrame (fun c hc a ha ↦ (nomem c hc a ha).elim))
    apply memoryWriteFrame_trans (t := v)
    · apply frame_mono copyFrame
      intro r hr a ha
      refine ⟨r, ?_, ha⟩
      have choice : r = ⟨(stackPtr s + 272 + BitVec.ofNat 64 previous.size).toNat, info.size⟩ ∨
          r = ⟨(stackPtr s - 8).toNat, 8⟩ := by simpa using hr
      rcases choice with rfl | rfl <;> simp [footprint]
    · apply frame_mono storeFrame
      intro r hr a ha
      exact ⟨r, by rw [Vector.mem_singleton.mp hr]; simp [footprint], ha⟩
  have runningT := runningV.of_agrees runT readyT store (by
    intro c hc a ha
    obtain ⟨r, hr, hin⟩ := writes c hc a ha
    have hreg := Vector.mem_singleton.mp hr
    subst r
    refine ⟨Stack.region entry 2264, by simp, ?_⟩
    have ea : a = stackPtr s + 335 := by
      apply BitVec.eq_of_toNat_eq
      change (stackPtr s + 335).toNat ≤ a.toNat ∧ a.toNat < (stackPtr s + 335).toNat + 1 at hin
      omega
    have cov : (Component.mem (stackPtr entry - 201) 1).Covers a :=
      ⟨0, by decide, by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ea.trans (addr.symm.trans destIndex)⟩
    exact stackRegion_contains_sub pre.call.stack.2.2.1 (offset := 201) (by decide) (by decide) cov)
    avoids (by simp)
  have spT : stackPtr t = stackPtr s := (store.read (n := 64) (r := 4) (by simp)).trans spVS
  have savedT := savedFrame saved pre.call.stack runningT spT short total
    ((store.mxcsr (by simp)).trans (abi.2.2.1.trans (ag.mxcsr (by decide))))
    ((store.fcw (by simp)).trans (abi.2.2.2.trans (ag.fcw (by decide))))
  have bounds := stack_bounds pre.call.stack
  have base : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [show stackPtr s = stackPtr entry - 536 from saved.sp]
    exact stack_sub_toNat pre.call.stack (offset := 536) (by decide)
  refine ⟨_, t, (runU.trans runV).trans runT, savedT, pcT, ?_,
    (store.read (n := 64) (r := 12) (by simp)).trans ((abi.1 .r12 (by decide)).trans
      (ag.read (n := 64) (r := 12) (by decide))),
    (store.read (n := 64) (r := 13) (by simp)).trans ((abi.1 .r13 (by decide)).trans
      (ag.read (n := 64) (r := 13) (by decide))),
    slot_eq (off := 440) total spT (by omega) (by omega) short (by decide)
      (.inr (by omega)) (.inr (by decide)), total⟩
  rw [spT]
  have keep (offset : Nat) := untouched (offset := offset) total (by omega) (by omega) short
  apply hmac_append input short
  · intro i hi
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
      keep (offset := 272+i) (by omega) (.inl (by omega)) (by omega)
  · intro i lo hi
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
      keep (offset := 272+i) (by omega) (.inr (by omega)) (by omega)
  · refine frame_hasBytes storeFrame ?_ ?_ copied
    · intro r hr
      rw [Vector.mem_singleton.mp hr]
      intro a ha hb
      simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at ha hb
      omega
    · change (stackPtr s + 272 + BitVec.ofNat 64 previous.size).toNat + info.size ≤ 2^64
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
      omega
  · have bp : v.regValue .rbp = BitVec.ofNat 64 info.size :=
      (abi.1 .rbp (by decide)).trans ((ag.read (n := 64) (r := 5) (by decide)).trans count)
    have r14 : v.regValue .r14 = BitVec.ofNat 64 previous.size :=
      (abi.1 .r14 (by decide)).trans ((ag.read (n := 64) (r := 14) (by decide)).trans offset)
    rw [bp, r14] at index
    rw [BitVec.add_assoc, show (272 : BitVec 64) + 63 = 335 from rfl, index]
    congr 1
    simp only [storedByte, Nat.mul_zero, Nat.shiftRight_zero, BitVec.toNat_add,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    congr 1
    omega

end Hkdf.Proofs.NewExpand.Expand.Info.Short
