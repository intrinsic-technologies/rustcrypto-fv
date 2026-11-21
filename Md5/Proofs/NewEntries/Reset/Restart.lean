import Md5.Proofs.NewEntries.Reset.Transition
import Md5.Proofs.NewEntries.Reset.AfterReset

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs Md5.Proofs.Block Md5.Proofs.Buffered

theorem reset_restart [Bindings] {boundary : ReturnBoundary} {initial s : RamState}
    (hOutside : ¬ InProgram boundary.rip) (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hPre : ResetPre s)
    (hStorage : Streaming.PrologueStorage 312 32 288 16 24 680 .r8 initial s)
    (hLow : (.reg 7 : Operand 64).read s = 0xefcdab8967452301)
    (hHigh : (.reg 2 : Operand 64).read s = 0x1032547698badcfe) :
    ∃ fuel u t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (resetEffect s).Holds s u ∧
      AfterResetPost (decide (((Operand.reg 12 : Operand 64).read s).toNat <
        ((Operand.reg 6 : Operand 64).read s).toNat)) u t ∧
      Streaming.PrologueStorage 312 32 288 16 24 680 .r8 initial t ∧
      Absorbed (stackPtr t + 32) ByteArray.empty t := by
  obtain ⟨n, u, hRunU, hReadyU, hCodeU, hEffect⟩ :=
    reset_core_run hOutside hReady hCode hPre
  obtain ⟨m, t, hRunT, hReadyT, hCodeT, hAfter⟩ :=
    after_reset hOutside hReadyU hCodeU hEffect.rip
  have hCount : (.reg 12 : Operand 64).read u = (.reg 12 : Operand 64).read s :=
    hEffect.agrees.read (by simp [resetEffect, Effect.components])
  have hTotal : (.reg 6 : Operand 64).read u = (.reg 6 : Operand 64).read s :=
    hEffect.agrees.read (by simp [resetEffect, Effect.components])
  have hRsp : stackPtr t = stackPtr u := hAfter.agrees.read (n := 64) (r := 4) (by simp)
  have hExt : t.external = u.external := hAfter.agrees.external (by simp [Component.Covers])
  refine ⟨n + m, u, t, hRunU.trans hRunT, hReadyT, hCodeT, hEffect, ?_, ?_, ?_⟩
  · simpa only [hCount, hTotal] using hAfter
  · exact (reset_storage hStorage hEffect).of_external_eq hRsp hExt
  · rw [hRsp]
    exact Streaming.absorbed_of_external_eq
      (reset_absorbed hPre.toStorage hEffect hLow hHigh) hExt

end Md5.Proofs.NewEntries.Reset
