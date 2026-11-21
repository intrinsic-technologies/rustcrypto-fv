import K256.Proofs.Common.SignatureRun
import K256.Proofs.RejectLength.Return

namespace K256.Proofs.ParseSignature.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

theorem finishWrapper {initial : RamState} {bytes : ByteArray} {args : Vector Value 53}
    {mem : Ram} {n : Nat} {regions : Vector MemoryRegion n} {status : BitVec 64}
    (call : ValidCall signatureFromSlice initial [bytes])
    (hsp : args[4] = ⟨64, initial.regValue .rsp - 88⟩)
    (hstatus : args[0] = ⟨64, status⟩)
    (kept : ∀ i : Fin 53, i.val ∈ [5, 12, 13, 14, 15, 22] →
      args[i] = (Reg.ofIndex i).read initial)
    (writes : RamWriteFrame initial.external mem regions.toList)
    (saved : memLoad mem (initial.regValue .rsp - 8) 64 = initial.regValue .rbx)
    (returnSlot : memLoad mem (initial.regValue .rsp) 64 =
      memLoad initial.external (initial.regValue .rsp) 64) :
    ∃ out, LIR.program.Exec (dialect Extracted.programImage)
      ⟨⟨.l1024d0, args, mem⟩, []⟩ out ∧ Common.Returned initial regions out ∧
      out.values[0] = ⟨64, status⟩ ∧ out.store = mem := by
  let sp := initial.regValue .rsp
  obtain ⟨ret, slot, low, outside⟩ := call.returnAddress
  have hf := Common.signatureFramePre call (memLoad_returnSlot slot) low outside
  have window : Writable Extracted.programImage initial.external (sp - 656) 656 := hf.window (by decide)
  have hr : Readable mem (sp - 8) 8 :=
    (window.readable.of_offsets (addr_sub sp 8) (addr_sub sp 656) (by decide)).of_frame writes
  have hs : Readable initial.external sp 8 := hf.slot
  have hs' := hs.of_frame writes
  have slotValue : memLoad mem sp 64 = ret := returnSlot.trans (memLoad_returnSlot slot)
  obtain ⟨out, step, storeEq, tag, bx, rsp, unchanged⟩ := SignatureSlice.returnBlock
    (code := Extracted.programImage) hsp ⟨hr.low, hr.present⟩ ⟨hs'.low, hs'.present⟩
    (show (memLoad mem sp 64).toNat < 2^32 by rw [slotValue]; exact low)
  have eax := (unchanged 0 (by decide)).trans hstatus
  refine ⟨out, .done (congrArg (Transfer.next _ []) step), ?_, eax, storeEq⟩
  refine ⟨?_, rsp, ?_, ?_, storeEq ▸ writes, congrArg Value.width eax⟩
  · rw [tag, slotValue, hf.returnBoundary.1]
    rfl
  · exact (unchanged 22 (by decide)).trans
      ((kept 22 (by decide)).trans (Reg.read_df_iff.mpr call.directionFlagUnset))
  · intro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bx.trans (congrArg (fun x => (⟨64, x⟩ : Value)) saved)
    all_goals exact (unchanged _ (by decide +revert)).trans (kept _ (by decide +revert))

end K256.Proofs.ParseSignature.Wrapper
