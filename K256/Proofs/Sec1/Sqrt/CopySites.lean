import K256.Proofs.Sec1.Sqrt.CallSites
import K256.Proofs.Sec1.Sqrt.Copy
import K256.Proofs.Common.Lift.Simulation
import K256.Proofs.Common.Refine.Store

set_option autoImplicit false

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.Lift K256.Proofs.Refine

private abbrev HasCopy (c : SquareCallSite) : Prop :=
  c.offset + 60 ≤ Extracted.textBytes.size ∧
  chunkedRead Extracted.textBytes (c.offset + 11) 49 = copy5Bytes

def copySites : List SquareCallSite :=
  squareCallSites.filter fun c => decide (HasCopy c)

theorem copySites_length : copySites.length = 69 := by
  decide +kernel

theorem copySites_subset {c : SquareCallSite} (hc : c ∈ copySites) : c ∈ squareCallSites :=
  (List.mem_filter.mp hc).1

theorem first44_copySite : (⟨0x18040, .r14R15⟩ : SquareCallSite) ∈ copySites := by
  decide +kernel

theorem middle88_copySite : (⟨0x184d0, .rbxR14⟩ : SquareCallSite) ∈ copySites := by
  decide +kernel

theorem last44_copySite : (⟨0x18950, .rbxR14⟩ : SquareCallSite) ∈ copySites := by
  decide +kernel

namespace SquareCallSite

theorem copyCode {c : SquareCallSite} (hc : c ∈ copySites) :
    ∀ x ∈ codeRange (c.pc + 11) copy5Bytes, x ∈ Extracted.programSections.toCodeMap := by
  have h : HasCopy c := of_decide_eq_true (List.mem_filter.mp hc).2
  apply codeRange_sub_section
    (s := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (sections := Extracted.programSections) (by simp [Extracted.programSections])
    (c.offset + 11) 49 h.2 (by decide +kernel)
  · have := h.1
    change c.offset + 11 + 49 ≤ Extracted.textBytes.size
    omega
  · change Extracted.textAddress + BitVec.ofNat 64 (c.offset + 11) = c.pc + 11
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl

theorem copyWords [Bindings] {c : SquareCallSite} {boundary : ReturnBoundary}
    {s : RamState} {words : Vector (BitVec 64) 5} (hc : c ∈ copySites)
    (hReady : ReadyToStep s) (hRip : s.RIP = c.pc + 11#64) (hRsp : stackPtr s ≠ boundary.rsp)
    (hCode : CodeIn Extracted.programSections.toCodeMap s)
    (hWrite : Writable Extracted.programSections.toCodeMap s.external (stackPtr s) 40)
    (hRead : Readable s.external (stackPtr s + 40) 40)
    (hWords : WordsAt s.external (stackPtr s + 40) 64 words) :
    ∃ t, Advances boundary 10 s t ∧ ReadyToStep t ∧ t.RIP = c.pc + 60#64 ∧
      stackPtr t = stackPtr s ∧ CodeIn Extracted.programSections.toCodeMap t ∧
      Writable Extracted.programSections.toCodeMap t.external (stackPtr s) 40 ∧
      Readable t.external (stackPtr s + 40) 40 ∧
      AgreesExcept [.reg 0, .reg 1, .rip, .mem (stackPtr s) 40] s t ∧
      WordsAt t.external (stackPtr t) 64 words := by
  have hApart : ∀ x ∈ Extracted.programSections.toCodeMap,
      ¬ Component.Covers (.mem (stackPtr s) 40) x.1 := by
    rintro x hx ⟨i, hi, he⟩
    exact hWrite.notCode x hx i hi he
  obtain ⟨t, hRun, hr, hip, hsp, hcode, hw, hread, hf, hCopied⟩ :=
    copy5 hReady hRip hRsp hCode (copyCode hc) hApart
      ⟨hWrite.readable.low, hWrite.readable.present, hWrite.tables⟩ ⟨hRead.low, hRead.present⟩
  rw [BitVec.add_assoc] at hip
  refine ⟨t, hRun, hr, hip, hsp, hcode, ⟨⟨hw.low, hw.mem⟩, hw.tables, hWrite.notCode⟩,
    ⟨hread.low, hread.mem⟩, hf, ?_⟩
  intro i hi
  rw [hsp]
  have hsrc := hWords i hi
  have hdst := hCopied ⟨i, hi⟩
  change memLoad t.external (stackPtr s + BitVec.ofNat 64 (8 * i)) 64 =
    memLoad s.external (stackPtr s + BitVec.ofNat 64 (40 + 8 * i)) 64 at hdst
  change memLoad s.external
    (stackPtr s + BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * i)) 64 = words[i] at hsrc
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at hsrc
  exact hdst.trans hsrc

end SquareCallSite

end K256.Proofs.Sec1.Sqrt
