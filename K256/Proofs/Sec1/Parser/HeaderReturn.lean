import K256.Proofs.Sec1.Parser.Header
import K256.Proofs.Sec1.Parser.Result.Return
import K256.Proofs.Sec1.Wrapper.ParserFrame

namespace K256.Proofs.Sec1.Parser

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Sec1.LIR K256.Proofs.Refine K256.Spec.Program Prelude
open K256.Proofs.Sec1.Wrapper (parserArgs parserMemory)

private theorem header_load_high {s : RamState} {offset : BitVec 64} (small : offset.toNat ≤ 16) :
    memLoad (headerMemory s) (s.regValue .rsp - offset) 64 =
      memLoad (parserMemory s) (s.regValue .rsp - offset) 64 := by
  simp only [headerMemory, Frame.savedRegistersMemory, BitVec.sub_sub]
  repeat' (rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets (addr_sub _ _)
    (addr_sub _ _) (by bv_omega))])

theorem headerSavedSlots {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes]) :
    Result.SavedSlots s (headerMemory s) := by
  have h := Frame.savedRegistersMemory_load (parserMemory s) (s.regValue .rsp - 256) (parserArgs s)
  change memLoad (headerMemory s) _ 64 = _ ∧ _ at h
  obtain ⟨_, r12, r14, r15, ret⟩ := h
  obtain ⟨parserRet, rbx', r14', ret'⟩ := Wrapper.parserMemory_load s
  have reg (i : Fin 53) := Wrapper.parserArgs_get s i
  have v15 : (parserArgs s)[15].get 64 = s.regValue .r15 := (congrArg (Value.get 64) (reg 15)).trans (by rfl)
  have v14 : (parserArgs s)[14].get 64 = s.regValue .rdi := (congrArg (Value.get 64) (reg 14)).trans (by rfl)
  have v12 : (parserArgs s)[12].get 64 = s.regValue .r12 := (congrArg (Value.get 64) (reg 12)).trans (by rfl)
  refine ⟨?_, ?_, ?_, ret.trans parserRet, (header_load_high (offset := 16) (by decide)).trans rbx',
    (header_load_high (offset := 8) (by decide)).trans r14', ?_, headerMemory_frame call⟩
  · exact (show s.regValue .rsp - 256 - 8 = s.regValue .rsp - 264 by bv_omega) ▸ r15.trans v15
  · exact (show s.regValue .rsp - 256 - 16 = s.regValue .rsp - 272 by bv_omega) ▸ r14.trans v14
  · exact (show s.regValue .rsp - 256 - 24 = s.regValue .rsp - 280 by bv_omega) ▸ r12.trans v12
  · have h0 := header_load_high (s := s) (offset := 0) (by decide)
    rw [show s.regValue .rsp - (0 : BitVec 64) = s.regValue .rsp by bv_omega] at h0
    exact h0.trans ret'


theorem headerExitFrame {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (regs : HeaderRegisters s args) :
    Result.ExitFrame s args (headerMemory s) := by
  refine { headerSavedSlots call with
    rsp := congrArg (Value.get 64) regs.rsp, rdi := ?_, kept := ?_ }
  · have reg : args[7] = (parserArgs s)[7] := regs.kept 7 (by decide)
    exact (congrArg (Value.get 64) reg).trans ((congrArg (Value.get 64) (Wrapper.parserArgs_get s 7)).trans (by rfl))
  · intro i hi
    have h := regs.kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)
    refine h.trans ?_
    have idx := Wrapper.parserArgs_get s i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [ite_eq_right (show i.val ≠ 14 by omega), ite_eq_right (show i.val ≠ 7 by omega),
      ite_eq_right (show i.val ≠ 4 by omega)] at idx
    exact idx

theorem parserCall_or_validHeader {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) :
    Wrapper.ParserCall s bytes ∨ ∃ regs : Values Value Reg.count, HeaderRegisters s regs ∧
      Reaches Extracted.programImage .l106390 (parserArgs s) (parserMemory s) .l1063d2 regs (headerMemory s) ∧
      ∃ pos : 0 < bytes.size, ∃ valid : validTag (bytes[0]'pos).toBitVec,
        s.regValue .rdx = lengthTable.get ⟨(bytes[0]'pos).toNat, validTag_lt valid⟩ := by
  obtain ⟨regs, kept, (⟨reached, reject⟩ | ⟨reached, accepted⟩)⟩ := header call
  · exact Or.inl (Result.parserCall call (headerExitFrame call kept) (Or.inl ⟨reject, reached⟩))
  · exact Or.inr ⟨regs, kept, reached, accepted⟩

end K256.Proofs.Sec1.Parser
