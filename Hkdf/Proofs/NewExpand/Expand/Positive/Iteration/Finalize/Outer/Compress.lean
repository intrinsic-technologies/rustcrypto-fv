import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Block
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Outer.Frame

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Outer

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem compressOuter [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info block : ByteArray} {ptr : BitVec 64} {length : Nat} {hash : Array UInt32}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (bound : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f46d)
    (r13 : s.regValue .r13 = stackPtr s + 16)
    (bytes : (⟨(stackPtr s + 80).toNat, 64⟩ : MemoryRegion).HasBytes s.external block)
    (eighth : slot s 72 = slot s 136)
    (hashWords : HashStateAt s (stackPtr s + 184) hash) :
    ∃ fuel t, Advances boundary fuel s t ∧ SavedFrame entry t boundary length ∧
      t.RIP = 0x10f4cb ∧ stackPtr t = stackPtr s ∧ PreservesABI s t ∧
      MemoryWriteFrame s t (writeRegions (stackPtr s)) ∧
      HashStateAt t (stackPtr t + 184)
        (Hkdf.Proofs.NIST.SHA256.compress hash (Hkdf.Proofs.NIST.Encoding.octetsToBits block)) := by
  let regions := #v[registerRegion entry .rcx (writtenLength length), Stack.region entry 2264]
  have sp : stackPtr s = stackPtr entry - 536 := saved.sp
  have avoids : ∀ r ∈ regions, r.Avoids InProgram := by
    intro r hr a ha hp
    have member : r ∈ #v[registerRegion entry .rcx length, Stack.region entry 2264] := by
      simpa only [regions, writtenLength, bound, ↓reduceIte] using hr
    exact (pre.separation pos bound).2 r member |>.2 a ha (.inl hp)
  obtain ⟨t, run, rip, rsp, regs, mxcsr, fcw, hashT⟩ :=
    compressBlock pre saved.toRunning (by simp) avoids sp .outer pc (fun _ => r13) bytes eighth hashWords
  have frame : MemoryWriteFrame s t (writeRegions (stackPtr s)) := by
    apply frame_mono run.frame
    intro r hr a ha
    have copyAddr : (stackPtr s + 16).toNat = (stackPtr s).toNat + 16 :=
      stack_toNat pre.call.stack sp (offset := 16) (by decide)
    have hashAddr : (stackPtr s + 184).toNat = (stackPtr s).toNat + 184 :=
      stack_toNat pre.call.stack sp (offset := 184) (by decide)
    simp only [CompressionSite.blockWrites, CompressionSite.hashOffset, BitVec.ofNat_eq_ofNat,
      Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨⟨(stackPtr s).toNat + 16, 128⟩, by simp [writeRegions], ?_⟩
      change (stackPtr s + 16).toNat ≤ a ∧ a < (stackPtr s + 16).toNat + 56 at ha
      rw [copyAddr] at ha
      change (stackPtr s).toNat + 16 ≤ a ∧ a < (stackPtr s).toNat + 16 + 128
      exact ⟨ha.1, by omega⟩
    · refine ⟨⟨(stackPtr s).toNat + 184, 32⟩, by simp [writeRegions], ?_⟩
      change (stackPtr s + 184).toNat ≤ a ∧ a < (stackPtr s + 184).toNat + 32 at ha
      rw [hashAddr] at ha
      exact ha
    · exact ⟨⟨(stackPtr s).toNat - 344, 344⟩, by simp [writeRegions], ha⟩
  obtain ⟨fuel, advance⟩ := run.execution
  obtain ⟨oldFuel, oldRun⟩ := saved.execution
  have running : Running entry boundary regions t :=
    ⟨⟨oldFuel + fuel, oldRun.trans advance⟩, run.machine, run.loaded,
      fun a h => run.allocated a (saved.allocated a h), run.directionFlag,
      memoryWriteFrame_trans saved.frame (frame_mono frame (by
        intro r hr a ha
        exact ⟨Stack.region entry 2264, by simp [regions], writeRegions_inside pre.call.stack sp hr ha⟩))⟩
  have keepLen : slot t 224 = slot s 224 :=
    slot_of_frame pre.call.stack sp rsp frame (offset := 224) (by decide) (by decide) (by decide)
  have saved' := saved.of_agreement running rsp
    (frame_agrees_local pre.call.stack sp frame (offset := 488)
      (by decide) (by decide) (by decide) (by decide))
    keepLen mxcsr fcw
  have abi : PreservesABI s t := ⟨by
    intro r member
    simpa only [CompressionSite.savedReg] using regs r member,
    run.directionFlag, mxcsr, fcw⟩
  exact ⟨fuel, t, advance, saved', rip, rsp, abi, frame, rsp.symm ▸ hashT⟩

end Hkdf.Proofs.NewExpand.Expand.Finalize.Outer
