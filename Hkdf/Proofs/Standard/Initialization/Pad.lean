import Hkdf.Proofs.Common.ExtractCaller.Preserved
import Hkdf.Proofs.Common.ExtractCaller.Pad
import Hkdf.Proofs.Standard.Memory.Buffer
import Hkdf.Proofs.Common.Pad.Permissions

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Initialization

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame

theorem inner_pad [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    (ctx : Standard.Context initial salt inputs) :
    ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧ ReadyToStep t ∧
      Standard.Preserved initial t ∧ t.RIP = 0x1014be ∧
      (⟨(Standard.hmacBase initial).toNat, 64⟩ : MemoryRegion).HasBytes t.external
        (HMAC.xorPad (HMAC.keyBlock (Standard.saltKey salt)) 0x36) := by
  obtain ⟨fuel, s, run, ready, preserved, pre⟩ := ExtractCaller.standard_pad_preserved ctx
  obtain ⟨loopFuel, t, loop, readyT, ripT, _, frame, stored⟩ :=
    Pad.contract_of_loop (by rfl) pre ready pre.outside
  have writes : WritesWithin (Pad.components (stackPtr initial - 400))
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] := by
    intro c hc a ha
    simp only [Pad.components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ha.elim
    · exact ha.elim
    · exact ⟨Stack.region initial hkdfSha256Extract.minStackBytes, by simp,
        Hkdf.Proofs.Common.Machine.stackRegion_contains_sub ctx.call.stack.2.2.1
          (by decide +kernel) (by decide) ha⟩
    · exact ha.elim
  have current := preserved.toRunning.of_agrees loop readyT frame writes (by
    intro region member a contained inside
    have equal : region = Stack.region initial hkdfSha256Extract.minStackBytes := by
      simpa using member
    subst region
    exact (ctx.call.stackSeparation.2 _ (by simp)).2 a contained (.inl inside))
    (by simp [Pad.components])
  have pointer : Standard.hmacBase initial = stackPtr initial - 400 := by
    change stackPtr initial - 520 + 120 = stackPtr initial - 400
    bv_omega
  have bufferFrame : MemoryWriteFrame s t
      #v[(⟨(Standard.hmacBase initial).toNat, 64⟩ : MemoryRegion)] := by
    rw [pointer]
    exact frame.memoryWriteFrame (Pad.writesWithin pre.writable.readable.low)
  have rspT : t.regValue .rsp = Standard.frameBase initial :=
    (frame.read (n := 64) (r := 4) (by simp [Pad.components])).trans preserved.rsp
  refine ⟨fuel + loopFuel, t, run.trans loop, readyT,
    preserved.of_buffer_frame current bufferFrame rspT, ripT, ?_⟩
  rw [pointer]
  exact stored

end Hkdf.Proofs.Standard.Initialization
