import K256.Proofs.Sec1.Parser.Frame.Entry
import K256.Proofs.Sec1.Parser.Dispatch
import K256.Proofs.Sec1.Parser.Memory

namespace K256.Proofs.Sec1.Parser

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Sec1.LIR K256.Proofs.Refine K256.Spec.Program Prelude
open K256.Proofs.Sec1.Wrapper (parserArgs parserMemory)

def headerMemory (s : RamState) : Ram :=
  Frame.savedRegistersMemory (parserMemory s) (s.regValue .rsp - 256) (parserArgs s)

structure HeaderRegisters (s : RamState) (args : Values Value Reg.count) : Prop where
  rsp : args[4] = ⟨64, s.regValue .rsp - 600⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [2, 5, 6, 7, 12, 13, 22, 39, 50, 51] →
    args[i] = (parserArgs s)[i]

private theorem headerWritable {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) :
    Writable Extracted.programImage (parserMemory s) (s.regValue .rsp - 256 - 32) 32 := by
  rw [BitVec.sub_sub]
  exact (Wrapper.stackWritable (offset := 288) call (by decide) (by decide) (by decide)).of_frame
    (parserMemory_frame call)

theorem headerMemory_frame {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) :
    RamWriteFrame s.external (headerMemory s) [Stack.region s publicKeyFromSec1Bytes.minStackBytes] := by
  apply (parserMemory_frame call).trans
    (Frame.savedRegistersMemory_frame (parserArgs s) (headerWritable call) ?_)
  · intro r h
    exact ⟨r, h, Nat.le_refl _, Nat.le_refl _⟩
  · rw [BitVec.sub_sub]
    exact stackRange (off := 288) call (by decide) (by decide)

theorem header {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes]) :
    ∃ args : Values Value Reg.count, HeaderRegisters s args ∧
      ((Reaches Extracted.programImage .l106390 (parserArgs s) (parserMemory s) .l106560 args (headerMemory s) ∧
        K256.Spec.Secp256k1.decodePublicKey bytes = none) ∨
       (Reaches Extracted.programImage .l106390 (parserArgs s) (parserMemory s) .l1063d2 args (headerMemory s) ∧
        ∃ pos : 0 < bytes.size, ∃ valid : validTag (bytes[0]'pos).toBitVec,
          s.regValue .rdx = lengthTable.get ⟨(bytes[0]'pos).toNat, validTag_lt valid⟩)) := by
  have size : (s.regValue .rdx).toNat = bytes.size := call.lengthArgumentsMatchInputs.1
  have stack : (parserArgs s)[4].get 64 = s.regValue .rsp - 256 := by
    simp only [parserArgs, Vector.getElem_set]; rfl
  have len : (parserArgs s)[2].get 64 = s.regValue .rdx := by
    simp only [parserArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte, Lifted.locationOf, Vector.getElem_ofFn]; rfl
  obtain ⟨a, entry, rsp, kept⟩ := Frame.entryBlock stack len (headerWritable call)
    (fun x hx => Common.fnCode_subset_programImage x (code_l106390 x hx))
  have base : HeaderRegisters s a := by
    refine ⟨?_, fun i h => kept i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)⟩
    exact rsp.trans (congrArg (Value.mk 64) (by bv_omega))
  by_cases empty : s.regValue .rdx = 0
  · rw [ite_eq_left empty] at entry
    have zero : bytes.size = 0 := by rw [← size, empty]; rfl
    exact ⟨a, base, Or.inl ⟨reaches_jump entry, decodePublicKey_wrongLength (by omega) (by omega)⟩⟩
  · rw [ite_eq_right empty] at entry
    have pos : 0 < bytes.size := by
      rw [← size]
      exact Nat.pos_of_ne_zero (fun h => empty (BitVec.eq_of_toNat_eq h))
    obtain ⟨content, image⟩ := inputs_of_stackFrame call (headerMemory_frame call)
    have input : ValidInput s (registerRegion s .rsi bytes.size) bytes := call.inputsInMemory.1
    have bound : (s.regValue .rsi).toNat + bytes.size < 2^32 := input.2.1
    have si : a[6].get 64 = s.regValue .rsi := by
      have e : a[6] = (parserArgs s)[6] := kept 6 (by decide)
      rw [e]
      simp only [parserArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte, Lifted.locationOf, Vector.getElem_ofFn]; rfl
    have dx : a[2].get 64 = s.regValue .rdx :=
      (congrArg (Value.get 64) (kept 2 (by decide))).trans len
    obtain ⟨b, keep, path⟩ := guardDispatch si dx size pos content (Nat.le_of_lt bound) image
    refine ⟨b, ⟨(keep 4 (by decide)).trans base.rsp, fun i h => ?_⟩, ?_⟩
    · exact (keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)).trans (base.kept i h)
    · rcases path with ⟨reach, reject⟩ | ⟨reach, valid, matchLen⟩
      · exact Or.inl ⟨(reaches_jump entry).trans reach, reject⟩
      · exact Or.inr ⟨(reaches_jump entry).trans reach, pos, valid, matchLen⟩

end K256.Proofs.Sec1.Parser
