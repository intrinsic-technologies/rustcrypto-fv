import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Prepare

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def updatePc (previous count : Nat) : BitVec 64 :=
  if count < 64 - previous then 0x10f6f0 else if previous = 0 then 0x10f7f5 else 0x10f74b

def decodeComponents : List Component := [.reg 3, .reg 5, .reg 14, .reg 2, .reg 15, .flags, .rip]

variable [Bindings] {entry s : RamState} {boundary : ReturnBoundary} {key info previous : ByteArray}
  {ptr : BitVec 64} {length : Nat}

theorem selectUpdate (pre : ExpandPre entry boundary key info ptr length)
    (pos : 0 < length) (limit : length ≤ 8160) (saved : SavedFrame entry s boundary length)
    (pc : s.RIP = 0x10f721) (cursor : s.regValue .r13 = entry.regValue .rsi)
    (active : HmacAt s (stackPtr s + 272) key previous) (small : previous.size < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ SavedFrame entry t boundary length ∧
      t.RIP = updatePc previous.size info.size ∧
      t.regValue .rbx = ptr ∧ t.regValue .rbp = BitVec.ofNat 64 info.size ∧
      t.regValue .r14 = BitVec.ofNat 64 previous.size ∧
      t.regValue .rdx = BitVec.ofNat 64 (64 - previous.size) ∧
      t.regValue .r15 = BitVec.ofNat 64 info.size - BitVec.ofNat 64 (64 - previous.size) ∧
      AgreesExcept decodeComponents s t := by
  obtain ⟨readPtr, readLen, ptrWord, lenWord⟩ := descriptorWords pre pos limit saved cursor
  have ctx := Counter.StackContext.of_pre pre pos limit
  have index : MemReadable s (rspOf s + 335) 1 := by
    rw [show rspOf s = Counter.base entry from saved.sp]
    exact Counter.read_stack ctx saved.toRunning (off := 335) (by decide) (by decide)
  obtain ⟨v, run, ready, next, src, count, position, room, rest, ag, mem⟩ :=
    readDescriptor boundary (supportedMachine_readyToStep saved.machine) saved.loaded pc
      readPtr readLen index ctx.outside
  change AgreesExcept decodeComponents s v at ag
  have noWrites : StackWrites decodeComponents (stackPtr s) [] := by
    intro c hc a cover
    simp only [decodeComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact cover.elim
  have savedV := (StackWrites.saved pre pos limit saved run ready ag noWrites (by decide) (by decide)).1
  have posWord := bufferedBytes active small
  have capacity : 64 - bufferIndex s = BitVec.ofNat 64 (64 - previous.size) := by
    rw [posWord, ← BitVec.ofNat_sub_ofNat_of_le 64 previous.size (by omega) (by omega)]
    rfl
  have lenNat : (inputLength s).toNat = info.size := by
    rw [lenWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pre.lengthFits]
  have capNat : (64 - bufferIndex s).toNat = 64 - previous.size := by
    rw [capacity, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [lenNat, capNat] at next
  rw [lenWord, capacity] at rest
  rw [posWord] at position
  rw [capacity] at room
  have src' : v.regValue .rbx = ptr := src.trans ptrWord
  have count' : v.regValue .rbp = BitVec.ofNat 64 info.size := count.trans lenWord
  by_cases short : info.size < 64 - previous.size
  · exact ⟨8, v, run, savedV, by simpa only [updatePc, ite_eq_left short] using next,
      src', count', position, room, rest, ag⟩
  · obtain ⟨t, branch, readyT, branchPc, jump, _⟩ := branchOnBufferedBytes boundary ready
      savedV.loaded (by simpa only [ite_eq_right short] using next) ctx.outside
    have combined : AgreesExcept decodeComponents s t := (ag.trans jump).mono (by decide)
    have savedT := (StackWrites.saved pre pos limit saved (run.trans branch) readyT combined
      noWrites (by decide) (by decide)).1
    have zero : (Operand.reg 14 : Operand 64).read v = 0 ↔ previous.size = 0 := by
      rw [position]
      constructor
      · intro h
        have n := congrArg BitVec.toNat h
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show previous.size < 2^64 by omega),
          BitVec.reduceToNat] using n
      · intro h
        rw [h]
        rfl
    refine ⟨10, t, run.trans branch, savedT, ?_,
      (jump.read (n := 64) (r := 3) (by decide)).trans src',
      (jump.read (n := 64) (r := 5) (by decide)).trans count',
      (jump.read (n := 64) (r := 14) (by decide)).trans position,
      (jump.read (n := 64) (r := 2) (by decide)).trans room,
      (jump.read (n := 64) (r := 15) (by decide)).trans rest, combined⟩
    simpa only [updatePc, ite_eq_right short, zero] using branchPc

end Hkdf.Proofs.NewExpand.Expand.Info
