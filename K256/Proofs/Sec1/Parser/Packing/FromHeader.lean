import K256.Proofs.Sec1.Parser.Header
import K256.Proofs.Sec1.Parser.Packing.Accepted
import K256.Proofs.Sec1.LIR.Fn106390.Frame
import K256.Proofs.Sec1.Buffers

namespace K256.Proofs.Sec1.Parser.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

private theorem length_of_validTag (t : UInt8) (h : validTag t.toBitVec) :
    let n := lengthTable.get ⟨t.toNat, validTag_lt h⟩
    n = 1 ∨ n = 33 ∨ n = 65 := by
  have ht : t = 0 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by
    simp only [← UInt8.toBitVec_inj]
    exact h
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)

theorem fromHeader {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    {regs : Values Value Reg.count} (header : HeaderRegisters s regs)
    (pos : 0 < bytes.size) (valid : validTag (bytes[0]'pos).toBitVec)
    (len : s.regValue .rdx = lengthTable.get ⟨(bytes[0]'pos).toNat, validTag_lt valid⟩)
    (stack : List (StackFrame Value Label signature Reg.count)) :
    let sp := s.regValue .rsp - 600
    ∃ args m,
      (program.sem (dialect Extracted.programImage)).Reaches
        ⟨⟨.l1063d2, regs, headerMemory s⟩, stack⟩ ⟨⟨.l121480, args, m⟩, affineResume :: stack⟩ ∧
      args[3] = ⟨64, sp + 160⟩ ∧ args[4] = ⟨64, sp - 8⟩ ∧
      args[6] = ⟨64, sp + 4⟩ ∧ args[7] = ⟨64, sp + 160⟩ ∧ args[12] = ⟨64, 0⟩ ∧
      args[14] = ⟨64, s.regValue .rdx⟩ ∧ args[15] = ⟨64, s.regValue .rsp - 112⟩ ∧
      (s.regValue .rdx).toNat = bytes.size ∧ (sp - 8).toNat % 16 = 8 ∧
      (∀ i < 65, memByte m (sp + 4 + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0) ∧
      memLoad m (sp - 8) 64 = 0x1064f4 ∧ RamWriteFrame (headerMemory s) m [packingWindow sp] ∧
      (∀ r ∈ [5, 13, 22, 39, 50, 51], ∀ hr : r < Reg.count, args[r] = regs[r]) := by
  dsimp only
  let sp := s.regValue .rsp - 600
  let st := Stack.region s publicKeyFromSec1Bytes.minStackBytes
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have al : (s.regValue .rsp).toNat % 16 = 8 := call.stackAvailable.2.2.2
  have base : sp.toNat = (s.regValue .rsp).toNat - 600 :=
    BitVec.toNat_sub_of_le (by change 600 ≤ (s.regValue .rsp).toNat; omega)
  have slot : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
  have align : sp.toNat % 16 = 0 := by omega
  have size : (s.regValue .rdx).toNat = bytes.size := call.lengthArgumentsMatchInputs.1
  have hsizes := length_of_validTag bytes[0] valid
  dsimp only at hsizes
  rw [← len] at hsizes
  have frm := headerMemory_frame call
  obtain ⟨content, image⟩ := inputs_of_stackFrame call frm
  have get (i : Fin 53) (hi : i.val ∈ [2,5,6,7,12,13,22,39,50,51]) :
      regs[i] = (Wrapper.parserArgs s)[i] := header.kept i hi
  have si : regs[6].get 64 = s.regValue .rsi := by
    refine (congrArg (Value.get 64) (get 6 (by decide))).trans ?_
    simp only [Wrapper.parserArgs, Vector.getElem_set, Fin.getElem_fin,
      Lifted.locationOf, Vector.getElem_ofFn]
    rfl
  have di : regs[7].get 64 = s.regValue .rsp - 112 := by
    refine (congrArg (Value.get 64) (get 7 (by decide))).trans ?_
    simp only [Wrapper.parserArgs, Vector.getElem_set, Fin.getElem_fin,
      Lifted.locationOf, Vector.getElem_ofFn]
    rfl
  have dx : regs[2].get 64 = s.regValue .rdx := by
    refine (congrArg (Value.get 64) (get 2 (by decide))).trans ?_
    simp only [Wrapper.parserArgs, Vector.getElem_set, Fin.getElem_fin,
      Lifted.locationOf, Vector.getElem_ofFn]
    rfl
  have df : regs[22].get 1 = 0 := by
    refine (congrArg (Value.get 1) (get 22 (by decide))).trans ?_
    simp only [Wrapper.parserArgs, Vector.getElem_set, Fin.getElem_fin,
      Lifted.locationOf, Vector.getElem_ofFn]
    change ((Reg.df).read s).get 1 = 0
    exact congrArg (Value.get 1) (Reg.read_df_iff.mpr call.directionFlagUnset)
  have win : Writable Extracted.programImage (headerMemory s) (sp - 8) 233 := by
    have e : sp - 8 = stackPtr s - 608 := by change s.regValue .rsp - 600 - 8 = _; rw [BitVec.sub_sub]; rfl
    rw [e]
    exact (Wrapper.stackWritable (offset := 608) call (by decide) (by decide) (by decide)).of_frame frm
  obtain ⟨rsrc, _, _, separate⟩ := Sec1.buffers call
  have inside : st.start ≤ (sp - 8).toNat ∧ (sp - 8).toNat + 233 ≤ st.start + st.size := by
    change (s.regValue .rsp).toNat - 1928 ≤ _ ∧ _ + 233 ≤
      (s.regValue .rsp).toNat - 1928 + ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 1928))
    omega
  have sep : Outside [packingWindow sp] (s.regValue .rsi) bytes.size := by
    have h := separate pos
    refine ⟨h.1, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rcases h.2 st (List.mem_cons_self ..) with l | r <;>
      change (s.regValue .rsi).toNat + bytes.size ≤ (sp - 8).toNat ∨
        (sp - 8).toNat + 233 ≤ (s.regValue .rsi).toNat <;> omega
  have input (i : Nat) (hi : i < bytes.size) :
      memByte (headerMemory s) (s.regValue .rsi + BitVec.ofNat 64 i) = bytes[i] := by
    have h := congrArg (fun z : Option UInt8 => z.getD 0) (content.2 ⟨i, hi⟩)
    simp only [registerRegion, ofNat_toNat_add, Option.getD_some] at h
    exact h
  have rod : rodataSection ∈ Extracted.programSections := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have slots := Fn106390.callSlots_loaded rod image
  obtain ⟨sr, sv⟩ := slots (0x203e10, 0x12a700) (by decide)
  obtain ⟨cr, cv⟩ := slots (0x203dd0, 0x12a820) (by decide)
  have avoid := (call.separation.2 st (by simp [st, writtenRegions, publicKeyFromSec1Bytes])).1
  have disj := apart_of_avoids (lo := 0x203dd0) (hi := 0x203dd8) avoid (by
    intro a ha hb
    obtain ⟨b, inImage⟩ := Fn106390.callSlots_span rod a ha
      (show a.toNat < 0x203e28 by omega)
    exact Or.inl ⟨b, Common.programSections_fetchByte_of_mem inImage⟩) (by
      change 0 < (s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 1928)
      omega) (by decide) (by decide)
  have apart : Outside [packingWindow sp] 0x203dd0 8 := by
    refine ⟨by decide, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change 0x203dd0 + 8 ≤ (sp - 8).toNat ∨ (sp - 8).toNat + 233 ≤ 0x203dd0
    omega
  obtain ⟨args, m, run, bx, cs, ci, co, r12, r14, r15, words, ret, f, keep⟩ :=
    acceptedEncoding stack (sp := sp) (congrArg (Value.get 64) header.rsp) si di dx df
      size hsizes align win (rsrc.of_frame frm) sep input Common.fnCode_subset_programImage
      ⟨sr.low, sr.present⟩ sv cr cv apart
  exact ⟨args, m, run, bx, cs, ci, co, r12, r14, r15, size, by change (sp - 8).toNat % 16 = 8; omega, words, ret, f, keep⟩

end K256.Proofs.Sec1.Parser.Packing
