import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Head
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Descriptor
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Frame
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.StackWrites

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def headComponents (s : RamState) : List Component :=
  [.mem (stackPtr s + 432) 8, .flags, .rip, .reg 13]

theorem headWrites (s : RamState) : StackWrites (headComponents s) (stackPtr s) [(432,8)] := by
  intro c member a covered
  simp only [headComponents, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨(432,8), by decide, covered⟩
  all_goals exact covered.elim

variable [Bindings] {entry s : RamState} {boundary : ReturnBoundary} {key info previous : ByteArray}
  {ptr : BitVec 64} {length : Nat}

theorem startDescriptor (pre : ExpandPre entry boundary key info ptr length)
    (pos : 0 < length) (limit : length ≤ 8160) (saved : SavedFrame entry s boundary length)
    (pc : s.RIP = 0x10f6c3) (count : slot s 248 = 1)
    (table : slot s 232 = entry.regValue .rsi)
    (active : HmacAt s (stackPtr s + 272) key previous) :
    ∃ t, Advances boundary 5 s t ∧ SavedFrame entry t boundary length ∧ t.RIP = 0x10f721 ∧
      t.regValue .r13 = entry.regValue .rsi ∧ slot t 432 = s.regValue .r15 ∧
      HmacAt t (stackPtr t + 272) key previous ∧ AgreesExcept (headComponents s) s t := by
  have ctx := Counter.StackContext.of_pre pre pos limit
  have sp : rspOf s = Counter.base entry := saved.sp
  have read (off : Nat) (fit : off + 8 ≤ 544) (low : off ≤ 536) :
      MemReadable s (rspOf s + BitVec.ofNat 64 off) 8 := by
    rw [sp]
    exact Counter.read_stack ctx saved.toRunning low fit
  have store : MemWritable s (rspOf s + 432) 8 := by
    rw [sp, show (432 : BitVec 64) = BitVec.ofNat 64 432 from rfl, Counter.base_add (by decide)]
    exact stack_writable8 ctx.stack ctx.stackAvoid saved.allocated (offset := 104)
      (by decide) (by decide)
  have apart : RangeApart (rspOf s + 432) 8 0x10f6c3 33 := by
    rw [sp]
    exact Counter.stack_apart ctx (off := 432) (codeOff := 0xf6c3) (by decide) (by decide) (by decide)
  have nonzero : (Operand.mem (rspOf s + 248) : Operand 64).read s ≠ 0 := by
    change slot s 248 ≠ 0
    rw [count]
    decide
  obtain ⟨t, run, ready, next, out, cursor, ag⟩ := start boundary
    (supportedMachine_readyToStep saved.machine) saved.loaded pc nonzero
    (read 248 (by decide) (by decide)) (read 232 (by decide) (by decide)) store apart ctx.outside
  change AgreesExcept (headComponents s) s t at ag
  have spT : stackPtr t = stackPtr s := ag.read (r := 4) (n := 64) (by simp [headComponents])
  have savedT := (StackWrites.saved pre pos limit saved run ready ag (headWrites s)
    (by decide) (by simp [headComponents])).1
  refine ⟨t, run, savedT, next, cursor.trans table, ?_, ?_, ag⟩
  · change memLoad t.external (stackPtr t + 432) 64 = _
    rw [spT]
    exact out
  · rw [spT]
    exact active.of_copy ((headWrites s).agrees ag (off := 272) (len := 144) (by decide) (by decide) (by decide))

end Hkdf.Proofs.NewExpand.Expand.Info
