import Sha2.Proofs.Common.Instructions.RepMovsq
import Sha2.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace Sha2.Proofs.Common.Instructions.RepMovsq

open X86 X86.Machine X86.UserProcess X86Proofs

theorem pre_of_memory {p : BitVec 64} {s : RamState} {count : Nat}
    (hrip : s.RIP = p) (hdf : DirectionFlagClear s.RFLAGS)
    (hcount : (rcx.read s).toNat = count)
    (hsrc : MemReadable s (rsi.read s) (8 * count))
    (hdst : CrossPageStore.Writable s (rdi.read s) (8 * count))
    (hdisjoint : (rsi.read s).toNat + 8 * count ≤ (rdi.read s).toNat ∨
      (rdi.read s).toNat + 8 * count ≤ (rsi.read s).toNat)
    (hcode : RangeApart (rdi.read s) (8 * count) p 3) :
    RepMovsqPre p s := by
  refine ⟨hrip, hdf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hcount] using hsrc.low
  · simpa only [hcount] using hdst.low
  · simpa only [hcount] using hsrc.mem
  · simpa only [hcount] using hdst.mem
  · simpa only [hcount] using hdisjoint
  · simpa only [hcount] using hdst.tables
  · simpa only [hcount] using hcode

theorem rep_movsq_execution [bindings : Bindings]
    (hstride : Prelude.UnitStringStride bindings) {s : RamState}
    {boundary : ReturnBoundary} {p : BitVec 64} {count : Nat}
    (hready : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xf3, 0x48, 0xa5]) s)
    (hpre : RepMovsqPre p s)
    (hcount : (rcx.read s).toNat = count)
    (hstart : p ≠ boundary.rip) (hend : p + 3 ≠ boundary.rip) :
    let t := nextStates (max count 1) s
    Advances boundary (max count 1) s t ∧ ReadyToStep t ∧
      (repMovsqEffect p s).Holds s t ∧
      ∀ i < 8 * count,
        t.external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  have hrex : RexWPrefix (0x48 : UInt8).toBitVec := by simp [RexWPrefix]
  have hr := rep_movsq_advances hstride boundary p 0x48 hrex s hready hcode hpre hstart hend
  have hs := rep_movsq_steps hstride p 0x48 hrex s hready hcode hpre
  have hc := rep_movsq_copy hstride p 0x48 hrex s hready hcode hpre
  simp only [hcount] at hr hs hc
  exact ⟨hr, hs.1, hs.2.2, hc⟩

end Sha2.Proofs.Common.Instructions.RepMovsq
