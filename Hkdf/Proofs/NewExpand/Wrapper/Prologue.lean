import Hkdf.Proofs.NewExpand.Wrapper.Prologue.Push
import Hkdf.Proofs.NewExpand.Wrapper.Prologue.Prepare
import Hkdf.Proofs.NewExpand.Wrapper.CalleeFrame
import Hkdf.Proofs.NewExpand.Wrapper.Prologue.Pre
import Hkdf.Proofs.NewExpand.Wrapper.Prologue.Call

namespace Hkdf.Proofs.NewExpand.Wrapper

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prologue [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {ikm info : ByteArray} {length : Nat}
    (hCall : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    (machine : SupportedMachine bindings initial) (stride : UnitStringStride bindings) :
    ∃ s, ExtractEntry initial s salt ikm := by
  have outside := outerBoundary hCall.returnAddress
  obtain ⟨_, pushed, next, stack, saves, regs⟩ := saveRegisters hCall machine outside
  obtain ⟨u, run, ip, sp, saved, args, dest, saltPtr, saltLen, ikmPtr, ikmLen⟩ :=
    prepareExtract hCall outside pushed next stack saves regs
  obtain ⟨t, running, called, ret⟩ := callExtract hCall run ip sp
  have f : AgreesExcept [.reg 4, .mem (pushAddr u) 8, .rip] u t := by
    simpa only [callEffect, pushEffect_components] using called.agrees
  have rsp : stackPtr t = stackPtr initial - 368 := by
    rw [show stackPtr t = pushAddr u from called.writes.1, pushAddr, sp, BitVec.sub_sub]
    rfl
  have output := (f.read (n := 64) (r := 7) (by simp)).trans dest
  have pre := extractPreAtCall hCall stride running outside called.rip ret rsp output
    ((f.read (n := 64) (r := 6) (by simp)).trans saltPtr)
    ((f.read (n := 64) (r := 2) (by simp)).trans saltLen)
    ((f.read (n := 64) (r := 1) (by simp)).trans ikmPtr)
    ((f.read (n := 64) (r := 8) (by simp)).trans ikmLen)
  refine ⟨t, running, pre, ?_, ?_, rsp, output, ret⟩
  · apply savedFrame_of_frame saved (f.read (n := 64) (r := 5) (by simp)) hCall.stack
      (CallFrame.call_frame pre.call.stack called)
    intro addr lo _ region hr hin
    obtain rfl := Vector.mem_singleton.mp hr
    have top := hin.2
    rw [Common.Machine.stack_region_end, rsp] at top
    have spNat : (stackPtr initial - 368).toNat = (stackPtr initial).toNat - 368 :=
      CallFrame.stack_sub_toNat hCall.stack (show 368 ≤ hkdfSha256NewExpandMinStackBytes by decide)
    rw [spNat] at top
    have low : 2632 ≤ (stackPtr initial).toNat := hCall.stack.2.2.1
    omega
  · exact ⟨(f.read (n := 64) (r := 14) (by simp)).trans args.info,
      (f.read (n := 64) (r := 3) (by simp)).trans args.infoLength,
      (f.read (n := 64) (r := 15) (by simp)).trans args.output,
      (f.read (n := 64) (r := 12) (by simp)).trans args.length⟩

end Hkdf.Proofs.NewExpand.Wrapper
