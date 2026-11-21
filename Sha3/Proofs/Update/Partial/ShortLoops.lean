import Sha3.Proofs.Update.Partial.Context
import Sha3.Proofs.Update.Partial.LoopCode

namespace Sha3.Proofs.Update.Partial.Short

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def workClobbers (pointer : BitVec 64) (position : Nat) : List Component :=
  [.reg 2, .reg 6, .reg 15, .reg 8, .reg 9, .reg 3, .reg 10,
    .mem (destination pointer position) (200 - position), .flags, .rip]

theorem workFrame_trans {pointer : BitVec 64} {position : Nat} {s u t : RamState}
    (h : AgreesExcept (workClobbers pointer position) s u)
    (h' : AgreesExcept (workClobbers pointer position) u t) :
    AgreesExcept (workClobbers pointer position) s t :=
  (h.trans h').mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)

theorem workFrame_mono {pointer : BitVec 64} {position : Nat} {s t : RamState}
    (h : AgreesExcept (workClobbers pointer position) s t) :
    AgreesExcept (Partial.clobbers pointer position) s t :=
  h.mono (by simp [workClobbers, Partial.clobbers])

structure WorkResult [Bindings] (v : Variant) (pointer : BitVec 64) (position count : Nat)
    (initial input : Nat → UInt8) (s t : RamState) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = addPC v
  stateBytes : Bytes t.external (destination pointer position) (200 - position)
    (fun i ↦ initial i ^^^ (if i < count then input i else 0))
  frame : AgreesExcept (workClobbers pointer position) s t

section Composition

variable [Bindings] {v : Variant} {pointer source : BitVec 64}
  {position count : Nat} {initial input : Nat → UInt8} {s : RamState}
  (hc : Context v pointer source position count initial input s)
  (boundary : ReturnBoundary) (hb : ¬ InProgram boundary.rip)

include hc hb in
theorem byte_loop_result {u : RamState} (offset : Nat)
    (hpart : offset + count % 4 = count) (hpos : 0 < count % 4)
    (hr : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hip : u.RIP = bytePC v)
    (hframe : AgreesExcept (workClobbers pointer position) s u)
    (h1 : (Operand.reg 2 : Operand 64).read u = BitVec.ofNat 64 (count % 4))
    (h6 : (Operand.reg 6 : Operand 64).read u = 0)
    (h7 : (Operand.reg 15 : Operand 64).read u =
      destination pointer position + BitVec.ofNat 64 offset)
    (h3 : (Operand.reg 3 : Operand 64).read u = source + BitVec.ofNat 64 offset)
    (hbytes : Bytes u.external (destination pointer position) (200 - position)
      (fun i ↦ initial i ^^^ (if i < offset then input i else 0))) :
    ∃ t, Advances boundary (count % 4 * 5) u t ∧
      WorkResult v pointer position count initial input s t := by
  have hspan : offset + count % 4 ≤ 200 - position := by
    have := hc.count_le
    have := v.rate_le
    omega
  have hinput := hc.sourceBytes_of_frame (workFrame_mono hframe)
  have hsrcLow : (source + BitVec.ofNat 64 offset).toNat + count % 4 ≤ 2 ^ 32 := by
    have hl := hc.sourceLow
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hinv : ByteInvariant .short (byteLoopAddress .short v)
      (source + BitVec.ofNat 64 offset) (destination pointer position)
      offset (count % 4) (200 - position) initial input 0 u := by
    refine ⟨?_, h1, h6, h3, h7, hinput.sub offset _ (by omega), ?_⟩
    · have he : bytePC v = byteLoopAddress .short v := by cases v <;> rfl
      simpa only [he, hpos, ↓reduceIte] using hip
    · simpa only [Nat.add_zero] using hbytes
  obtain ⟨t, hrun, htready, htcode, ht, htframe⟩ :=
    byte_loop boundary Extracted.programImage .short (byteLoopAddress .short v)
      (source + BitVec.ofNat 64 offset) (destination pointer position)
      offset (count % 4) (200 - position) initial input hspan hsrcLow hc.stateLow
      (by
        intro i hi j hj he
        apply hc.apart i hi (offset + j) (by omega)
        simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using he)
      (fun i hi hp ↦ hc.avoids i hi (.inr hp))
      (by
        intro byte hbyte i hi he
        exact hc.avoids i hi (.inl (he ▸ (show InProgram byte.1 from ⟨byte.2, hbyte⟩))))
      (byteBytes_subset .short v)
      (by
        intro i hi
        apply byte_ne_boundary .short v boundary hb i
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        omega) u hr hcode hinv
  refine ⟨t, hrun, htready, htcode, ?_, ?_, ?_⟩
  · have he : byteLoopAddress .short v + 17#64 = addPC v := by cases v <;> rfl
    simpa only [Nat.lt_irrefl, ↓reduceIte, he] using ht.rip
  · simpa only [hpart] using ht.stateBytes
  · exact workFrame_trans hframe (htframe.mono
      (by simp [byteClobbers, ByteLoopKind.indexReg, workClobbers]))

include hc hb in
theorem chunk_loop_result {u : RamState}
    (hr : ReadyToStep u) (hcode : CodeIn Extracted.programImage u)
    (hframe : AgreesExcept (workClobbers pointer position) s u)
    (hinv : ChunkInvariant (chunkAddress .short v) source (destination pointer position)
      (count / 4 * 4) (200 - position) initial input 0 0 u) :
    ∃ t, Advances boundary (count / 4 * 11) u t ∧
      ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      ChunkInvariant (chunkAddress .short v) source (destination pointer position)
        (count / 4 * 4) (200 - position) initial input (count / 4 * 4) 0 t ∧
      AgreesExcept (workClobbers pointer position) s t ∧
      AgreesExcept (chunkClobbers (destination pointer position) (200 - position)) u t := by
  have hspan : count / 4 * 4 ≤ 200 - position := by
    have := hc.count_le
    have := v.rate_le
    omega
  obtain ⟨t, hrun, htready, htcode, ht, htframe⟩ :=
    chunk_loop boundary Extracted.programImage (chunkAddress .short v) source
      (destination pointer position) (count / 4 * 4) (200 - position) initial input
      hspan (by have := hc.sourceLow; omega) hc.stateLow
      (fun i hi j hj ↦ hc.apart i hi j (by omega))
      (fun i hi hp ↦ hc.avoids i hi (.inr hp))
      (by
        intro byte hbyte i hi he
        exact hc.avoids i hi (.inl (he ▸ (show InProgram byte.1 from ⟨byte.2, hbyte⟩))))
      (chunk_subset .short v) (chunk_ne_boundary .short v boundary hb)
      (count / 4) (by omega) u hr hcode hinv
  exact ⟨t, hrun, htready, htcode, ht, workFrame_trans hframe
    (htframe.mono (by simp [chunkClobbers, workClobbers])), htframe⟩

end Composition

end Sha3.Proofs.Update.Partial.Short
