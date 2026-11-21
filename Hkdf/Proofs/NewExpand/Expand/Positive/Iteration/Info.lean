import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Dispatch
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Exit
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Footprint
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Short

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem absorb [Bindings] {entry s : RamState} {boundary : ReturnBoundary} {length : Nat}
    {key previous info : ByteArray} {ptr : BitVec 64}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f6c3)
    (count : slot s 248 = 1) (table : slot s 232 = entry.regValue .rsi)
    (tableEnd : slot s 440 = entry.regValue .rsi + 16) (memcpy : s.regValue .r12 = 0x10dd60)
    (active : HmacAt s (stackPtr s + 272) key previous) (small : previous.size < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ SavedFrame entry t boundary length ∧ t.RIP = 0x10f8a0 ∧
      HmacAt t (stackPtr t + 272) key (previous ++ info) ∧
      t.regValue .r12 = s.regValue .r12 ∧ slot t 432 = s.regValue .r15 ∧
      MemoryWriteFrame s t (regions (stackPtr s)) := by
  obtain ⟨h, startRun, savedH, pcH, cursorH, outH, activeH, head⟩ :=
    startDescriptor pre pos limit saved pc count table active
  obtain ⟨n, u, decodeRun, savedU, pcU, src, len, idx, room, rest, decoded⟩ :=
    selectUpdate pre pos limit savedH pcH cursorH activeH small
  have spH : stackPtr h = stackPtr s := savedH.sp.trans saved.sp.symm
  have spU : stackPtr u = stackPtr h := savedU.sp.trans savedH.sp.symm
  have memU : u.external = h.external := decoded.external (by simp [decodeComponents, Component.Covers])
  have activeU : HmacAt u (stackPtr u + 272) key previous :=
    activeH.of_copy (fun i _ ↦ by rw [spU, memU])
  have copyPtr : u.regValue .r12 = s.regValue .r12 :=
    (decoded.read (n := 64) (r := 12) (by decide)).trans
      (head.read (n := 64) (r := 12) (by simp [headComponents]))
  have cursorU : u.regValue .r13 = entry.regValue .rsi :=
    (decoded.read (n := 64) (r := 13) (by decide)).trans cursorH
  have boundU := workBounds pre.call.stack savedU
  have body : ∃ m v, Advances boundary m u v ∧ SavedFrame entry v boundary length ∧
      v.RIP = (if previous.size + info.size < 64 then 0x10f70f else 0x10f7de) ∧
      HmacAt v (stackPtr v + 272) key (previous ++ info) ∧
      v.regValue .r12 = u.regValue .r12 ∧ v.regValue .r13 = u.regValue .r13 ∧
      MemoryWriteFrame u v (longRegions u) := by
    by_cases short : previous.size + info.size < 64
    · have select : info.size < 64 - previous.size := by omega
      obtain ⟨m, v, run, sv, pcV, hmac, copy, cursor, _, frame⟩ := Short.absorb pre savedU pos limit
        (by simpa only [updatePc, ite_eq_left select] using pcU) activeU src len idx
        (copyPtr.trans memcpy) short
      exact ⟨m, v, run, sv, by simpa only [ite_eq_left short] using pcV, hmac, copy, cursor,
        shortFootprint boundU short frame⟩
    · have fits : 64 - previous.size ≤ info.size := by omega
      have remEq : u.regValue .r15 = BitVec.ofNat 64 (info.size - (64 - previous.size)) := by
        rw [rest, ← BitVec.ofNat_sub_ofNat_of_le info.size (64 - previous.size) (by omega) fits]
      have offset := Nat.mod_eq_of_lt small
      have start : u.RIP = if previous.size % 64 = 0 then 0x10f7f5 else 0x10f74b := by
        simpa only [updatePc, ite_eq_right (Nat.not_lt.mpr fits), offset] using pcU
      obtain ⟨v, sv, ⟨m, run⟩, pcV, copy, cursor, frame, hmac⟩ := longInput pre pos limit savedU activeU
        start src len (by simpa only [offset] using idx) (by simpa only [offset] using room)
        (by simpa only [offset] using remEq) (by simpa only [offset] using fits) (copyPtr.trans memcpy)
      exact ⟨m, v, run, sv, by simpa only [ite_eq_right short] using pcV, hmac, copy, cursor, frame⟩
  obtain ⟨m, v, bodyRun, savedV, pcV, activeV, copyV, cursorV, bodyFrame⟩ := body
  have spV : stackPtr v = stackPtr u := savedV.sp.trans savedU.sp.symm
  have keepBody (off : Nat) (lo : 376 ≤ off) (hi : off + 8 ≤ 544) :
      slot v (BitVec.ofNat 64 off) = slot u (BitVec.ofNat 64 off) := by
    change memLoad v.external (stackPtr v + _) 64 = memLoad u.external (stackPtr u + _) 64
    rw [spV]
    exact agrees_memLoad (localAgrees boundU bodyFrame (keep := off) (size := 8)
      (by decide) (by decide) hi (.inr lo))
  have tableH : slot h 440 = slot s 440 := by
    change memLoad h.external (stackPtr h + 440) 64 = memLoad s.external (stackPtr s + 440) 64
    rw [spH]
    exact agrees_memLoad ((headWrites s).agrees head (off := 440) (len := 8)
      (by decide) (by decide) (by decide))
  have slotsU (off : BitVec 64) : slot u off = slot h off := by
    change memLoad u.external (stackPtr u + off) 64 = memLoad h.external (stackPtr h + off) 64
    rw [spU, memU]
  have done : v.regValue .r13 + 16 = slot v 440 := by
    rw [cursorV, cursorU]
    exact ((keepBody 440 (by decide) (by decide)).trans ((slotsU 440).trans (tableH.trans tableEnd))).symm
  obtain ⟨k, t, exitRun, savedT, pcT, exitAg, exitMem⟩ := finishDescriptor pre pos limit savedV
    (decide (previous.size + info.size < 64)) (by simpa only [decide_eq_true_eq] using pcV) done
  have spT : stackPtr t = stackPtr v := savedT.sp.trans savedV.sp.symm
  refine ⟨_, t, ((startRun.trans decodeRun).trans bodyRun).trans exitRun, savedT, pcT,
    activeV.of_copy (fun i _ ↦ by rw [spT, exitMem]),
    (exitAg.read (n := 64) (r := 12) (by decide)).trans (copyV.trans copyPtr), ?_,
    spanFrame (workBounds pre.call.stack saved).2 head memU (spU.trans spH) bodyFrame exitMem⟩
  change memLoad t.external (stackPtr t + 432) 64 = _
  rw [spT, exitMem]
  exact (keepBody 432 (by decide) (by decide)).trans ((slotsU 432).trans outH)

end Hkdf.Proofs.NewExpand.Expand.Info
