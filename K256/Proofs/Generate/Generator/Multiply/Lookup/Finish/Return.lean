import K256.Proofs.Generate.Generator.Multiply.Lookup.Memory
import K256.Proofs.Generate.LIR.Fn11c510
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem finishReturn {fr : Activation} {a : Registers} {m : Ram} {p : Projective}
    (atoms : Atom.All Extracted.programImage a m (Fn11c510.frameAt .l11c845 fr))
    (r14 : a[14].get 64 = fr.rsp - 408) (r15 : a[15].get 64 = fr.rsp - 168)
    (widths : ParseSignature.ArgumentWidths a)
    (stored : p.Stored m (fr.rsp - 168))
    (dst : Writable Extracted.programImage m fr.rdi 120)
    (above : fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l11c845, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn11c510.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ p.Stored out.store fr.rdi ∧
      RamWriteFrame m out.store [⟨(fr.rsp - 408).toNat,120⟩, ⟨fr.rdi.toNat,120⟩] := by
  simp only [Fn11c510.frameAt, Fn11c510.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, bx, mx, ft, fc, s48, s40, s32, s24, s16, s8, retRead, retWord, retLow,
    win, lower, _, _⟩ := atoms
  have rsp : a[4].get 64 = fr.rsp - 408 := congrArg (Value.get 64) sp
  have rbx : a[3].get 64 = fr.rdi := congrArg (Value.get 64) bx
  have direction : a[22].get 1 = 0 := congrArg (Value.get 1) df
  have off (d : Word) (h : d.toNat ≤ 496) : (fr.rsp - d).toNat = fr.rsp.toNat - d.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have n408 : (fr.rsp - 408).toNat = fr.rsp.toNat - 408 := off 408 (by decide)
  have n168 : (fr.rsp - 168).toNat = fr.rsp.toNat - 168 := off 168 (by decide)
  let copied := memCopy m (fr.rsp - 408) (fr.rsp - 168) 120
  let final := memCopy copied fr.rdi (fr.rsp - 408) 120
  let areas : List MemoryRegion := [⟨(fr.rsp - 408).toNat,120⟩, ⟨fr.rdi.toNat,120⟩]
  have tempRead : Readable m (fr.rsp - 168) 120 := by slot_state region
  have copy1 : RepMovsOk Extracted.programImage m 0 (fr.rsp - 168) (fr.rsp - 408) 15 8 0x11c850 3 :=
    copyGuard tempRead (by slot_guard using code_l11c845) (Or.inr (by omega))
  have copiedFrame : RamWriteFrame m copied areas := by
    apply Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl _ _)
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by omega⟩
  have dstCopied := dst.of_frame copiedFrame
  have winCopied := win.of_frame copiedFrame
  have accRead : Readable copied (fr.rsp - 408) 120 := by slot_state region
  have copy2 : RepMovsOk Extracted.programImage copied 0 (fr.rsp - 408) fr.rdi 15 8 0x11c85e 3 :=
    copyGuard accRead (by slot_guard using code_l11c845) (Or.inl (by omega))
  have frame : RamWriteFrame m final areas := by
    apply Sec1.Wrapper.Copy.memCopy_frame copiedFrame
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _, ?_⟩
    have := dst.readable.low
    omega
  have rr := retRead.of_frame frame
  have wfinal := win.of_frame frame
  have same (d : Word) (h : d.toNat ≤ 48) :
      memLoad final (fr.rsp - d) 64 = memLoad m (fr.rsp - d) 64 := by
    have eq := off d (by omega)
    have high := retRead.low
    apply frame.memLoad_eq
    refine ⟨by rw [eq]; omega, ?_⟩
    intro r hr
    simp only [areas, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right
      change (fr.rsp - 408).toNat + 120 ≤ (fr.rsp - d).toNat
      omega
    · left
      change (fr.rsp - d).toNat + 8 ≤ fr.rdi.toNat
      omega
  have hret : memLoad final fr.rsp 64 = fr.ret := by
    have rs := same 0 (by decide)
    rw [show fr.rsp - (0 : Word) = fr.rsp by bv_omega] at rs
    exact rs.trans retWord
  have f48 := (same 48 (by decide)).trans s48
  have f40 := (same 40 (by decide)).trans s40
  have f32 := (same 32 (by decide)).trans s32
  have f24 := (same 24 (by decide)).trans s24
  have f16 := (same 16 (by decide)).trans s16
  have f8 := (same 8 (by decide)).trans s8
  suffices ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l11c845, a, m⟩ = .returned out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn11c510.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ out.store = final by
    obtain ⟨out, run, tag, done_, aw, eq⟩ := this
    refine ⟨out, .done (by simp only [Program.step, run, Transfer.next]), tag, done_, aw, ?_, ?_⟩
    · rw [eq]
      exact copyStored (copyStored stored)
    · exact eq ▸ frame
  refine ⟨?out, ?run, ?tag, ?done_, ?widths, ?store⟩
  case run =>
    dsimp only [final, copied] at rr wfinal hret f48 f40 f32 f24 f16 f8 copy2
    arithmetic_segment using code_l11c845 [rsp, direction, rbx, r14, r15, copy1, copy2, false_or,
      reduceAddOffset, reduceSubOffset,
      f48, f40, f32, f24, f16, f8, hret]
    refine Eq.trans (ite_eq_left ⟨by slot_guard using code_l11c845, retLow⟩) ?_
    rfl
  case tag => rfl
  case done_ =>
    simp only [Fn11c510.doneAt, Atom.All, Atom.Holds]
    exact ⟨congrArg (Value.mk 64) (by bv_omega), df, rfl, rfl, rfl, rfl, rfl, rfl, mx, ft, fc, trivial⟩
  case widths =>
    intro ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · exact widths 2 (by decide)
    · rfl
    · exact widths 8 (by decide)
    · exact widths 9 (by decide)
  case store => rfl

end K256.Proofs.Generate.Generator.Multiply.Lookup
