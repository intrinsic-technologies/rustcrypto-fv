import P256.Proofs.Verifying.Wrapper.KeyCopy.Interface
import P256.Proofs.Program.Code
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.KeyCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def components (s : RamState) : List Component :=
  [.reg 0, .reg 1, .rip, .mem (stackPtr s) 65]

theorem Pre.after {s t : RamState} {pc next : BitVec 64}
    (pre : Pre pc s) (ag : AgreesExcept (components s) s t) (rip : t.RIP = next) :
    Pre next t := by
  have sp : stackPtr t = stackPtr s := ag.read (n := 64) (r := 4) (by simp [components])
  have source : t.regValue .rdx = s.regValue .rdx :=
    ag.read (n := 64) (r := 2) (by simp [components])
  refine ⟨rip, ?_, ?_, ?_, ?_⟩
  · intro off len bound
    rw [source]
    exact readable_of_grow (pre.readable off len bound) ag.grow
  · rw [sp]
    exact ⟨readable_of_grow pre.writable.toMemReadable ag.grow, pre.writable.tables⟩
  · rw [sp, source]
    exact pre.apart
  · intro off len bound offset codeLen codeBound
    rw [sp]
    exact pre.codeApart off len bound offset codeLen codeBound

theorem Pre.source_byte {s t : RamState} {pc : BitVec 64}
    (pre : Pre pc s) (ag : AgreesExcept (components s) s t) {i : Nat} (bound : i < 65) :
    t.external[s.regValue .rdx + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rdx + BitVec.ofNat 64 i]? := by
  apply ag.byte
  intro c hc covered
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j, hj, he⟩ := covered
  exact pre.apart j hj i bound he.symm

theorem Pre.source_load {s t : RamState} {pc : BitVec 64}
    (pre : Pre pc s) (ag : AgreesExcept (components s) s t)
    {off n : Nat} (bound : off+n/8 ≤ 65) :
    memLoad t.external (s.regValue .rdx + BitVec.ofNat 64 off) n =
      memLoad s.external (s.regValue .rdx + BitVec.ofNat 64 off) n := by
  apply memLoad_congr
  intro i hi
  simpa only [BitVec.ofNat_add, BitVec.add_assoc, memByte, PhysicalMemory.read] using
    congrArg (Option.getD · 0) (pre.source_byte ag (i := off+i) (by omega))

theorem Pre.code {s t : RamState} {pc : BitVec 64}
    (pre : Pre pc s) (ag : AgreesExcept (components s) s t)
    {offset : Nat} {bytes : List UInt8} (bound : offset+bytes.length ≤ 118431)
    (code : CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) s) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) t := by
  apply CodeIn.of_agreesExcept ag ?_ code
  intro x hx c hc covered
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j, hj, he⟩ := covered
  obtain ⟨i, hi⟩ := (mem_codeRange_iff _ _ _).mp hx
  have address := congrArg Prod.fst hi
  exact pre.codeApart 0 65 (by decide) offset bytes.length bound j hj i.val i.isLt
    (by simpa using he.symm.trans address)

theorem chunk_bytes {s t : RamState} {pc : BitVec 64} (pre : Pre pc s)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (off n : Nat) (bound : off+n/8 ≤ 65)
    (value : memLoad t.external (stackPtr s + BitVec.ofNat 64 off) n =
      memLoad s.external (s.regValue .rdx + BitVec.ofNat 64 off) n) :
    ∀ i < n/8, t.external[stackPtr s + BitVec.ofNat 64 (off+i)]? =
      s.external[s.regValue .rdx + BitVec.ofNat 64 (off+i)]? := by
  have source := Bytes.of_memLoad (pre.readable off (n/8) bound).mem
  have dest := Bytes.of_memLoad (a := stackPtr s + BitVec.ofNat 64 off) (n := n)
    (fun i hi => grow _ (by
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
        (pre.writable.mem (off+i) (by omega))))
  intro i hi
  have h := dest i hi
  rw [value] at h
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h.trans (source i hi).symm

end P256.Proofs.Verifying.Wrapper.KeyCopy
