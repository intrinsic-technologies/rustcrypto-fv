import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Cursor
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Frame
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.StackWrites

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finishDescriptor [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {length : Nat} {key info : ByteArray} {ptr : BitVec 64}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (short : Bool)
    (pc : s.RIP = if short then 0x10f70f else 0x10f7de)
    (done : s.regValue .r13 + 16 = slot s 440) :
    ∃ fuel t, Advances boundary fuel s t ∧ SavedFrame entry t boundary length ∧
      t.RIP = 0x10f8a0 ∧ AgreesExcept [.reg 13,.flags,.rip] s t ∧ t.external = s.external := by
  have ctx := Counter.StackContext.of_pre pre pos limit
  have read : MemReadable s (rspOf s + 440) 8 := by
    rw [show rspOf s = Counter.base entry from saved.sp]
    exact Counter.read_stack ctx saved.toRunning (off := 440) (by decide) (by decide)
  change (Operand.reg 13 : Operand 64).read s + 16 =
    (Operand.mem (rspOf s + 440) : Operand 64).read s at done
  have stages : ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      t.RIP = 0x10f8a0 ∧ AgreesExcept [.reg 13,.flags,.rip] s t ∧ t.external = s.external := by
    cases short
    · obtain ⟨n,t,run,ready,_,next,_,ag,m⟩ := finishCompressed boundary
        (supportedMachine_readyToStep saved.machine) saved.loaded pc read ctx.outside
      exact ⟨n,t,run,ready,by simpa only [ite_eq_left done] using next,ag,m⟩
    · obtain ⟨t,run,ready,next,_,ag,m⟩ := finishShort boundary
        (supportedMachine_readyToStep saved.machine) saved.loaded pc read ctx.outside
      exact ⟨3,t,run,ready,by simpa only [ite_eq_left done] using next,ag,m⟩
  obtain ⟨fuel,t,run,ready,next,ag,mem⟩ := stages
  have writes : StackWrites [.reg 13, .flags, .rip] (stackPtr s) [] := by
    intro c member a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact cover.elim
  exact ⟨fuel,t,run,(StackWrites.saved pre pos limit saved run ready ag writes
    (by decide) (by decide)).1,next,ag,mem⟩

end Hkdf.Proofs.NewExpand.Expand.Info
