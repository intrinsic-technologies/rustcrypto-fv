import P256.Proofs.HMAC.Pad.Code

set_option autoImplicit false

namespace P256.Proofs.HMAC.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.CrossPageStore

theorem buffer_of_agrees {loop : Loop} {s t : RamState}
    (agrees : AgreesExcept (footprint loop s) s t) : buffer loop t = buffer loop s := by
  have rsp : stackPtr t = stackPtr s := agrees.read (n := 64) (r := 4) (by simp [footprint])
  simp only [buffer, rsp]

theorem Memory.after {loop : Loop} {s t : RamState} (memory : Memory loop s)
    (agrees : AgreesExcept (footprint loop s) s t) : Memory loop t := by
  have eq := buffer_of_agrees agrees
  constructor
  · rw [eq]
    exact ⟨⟨memory.writable.low, fun i hi => agrees.grow _ (memory.writable.mem i hi)⟩,
      memory.writable.tables⟩
  · rw [eq]
    exact memory.avoids

theorem Memory.loaded_after {loop : Loop} {s t : RamState} (memory : Memory loop s)
    (loaded : ProgramLoaded s) (agrees : AgreesExcept (footprint loop s) s t) :
    ProgramLoaded t := by
  intro a b hb
  rw [agrees.byte]
  · exact loaded a b hb
  · intro c hc covered
    simp only [footprint, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact covered.elim
    · exact covered.elim
    · exact covered.elim
    · obtain ⟨i, hi, rfl⟩ := covered
      exact memory.avoids i hi ⟨b, hb⟩

theorem footprint_trans {loop : Loop} {s t u : RamState}
    (left : AgreesExcept (footprint loop s) s t)
    (right : AgreesExcept (footprint loop t) t u) :
    AgreesExcept (footprint loop s) s u := by
  have eq : footprint loop t = footprint loop s := by
    simp only [footprint, buffer_of_agrees left]
  rw [eq] at right
  exact (left.trans right).mono (by simp)

theorem Memory.byte_writable {loop : Loop} {s : RamState} (memory : Memory loop s)
    (i : Nat) (hi : i < 64) : MemWritable s (buffer loop s + BitVec.ofNat 64 i) 1 := by
  have w := memory.writable.add i (len := 1) (by omega)
  exact ⟨w.low, w.mem, w.tables⟩

theorem Memory.byte_code {loop : Loop} {s : RamState} (memory : Memory loop s)
    (i offset len : Nat) (hi : i < 64) (bound : offset + len ≤ loop.length) :
    RangeApart (buffer loop s + BitVec.ofNat 64 i) 1
      (BitVec.ofNat 64 (loop.entry + offset)) len := by
  intro j hj k hk eq
  have hj0 : j = 0 := by omega
  subst j
  simp only [BitVec.add_zero] at eq
  apply memory.avoids i hi
  rw [eq, ← BitVec.ofNat_add, Nat.add_assoc]
  exact address_inProgram loop (offset + k) (by omega)

theorem byte_agrees {loop : Loop} {s t : RamState} {i : Nat} (hi : i < 64)
    (agrees : AgreesExcept [.mem (buffer loop s + BitVec.ofNat 64 i) 1, .flags, .rip] s t) :
    AgreesExcept (footprint loop s) s t := by
  refine ⟨?_, ?_, agrees.rest, agrees.grow⟩
  · intro c hc hm
    exact agrees.agree c (by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · contradiction
      · exact hc (by simp [footprint])
      · exact hc (by simp [footprint])) hm
  · intro a ha
    apply agrees.memory a
    intro c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨j, hj, rfl⟩ := covered
      apply ha (.mem (buffer loop s) 64) (by simp [footprint])
      exact ⟨i+j, by omega, by simp only [BitVec.ofNat_add, BitVec.add_assoc]⟩
    · exact covered.elim
    · exact covered.elim

theorem Post.keyPad {loop : Loop} {s t : RamState} (post : Post loop s t)
    (key : ByteArray) (old : UInt8)
    (input : (MemoryRegion.mk (buffer loop s).toNat 64).HasBytes s.external (HMAC.keyPad key old)) :
    (MemoryRegion.mk (buffer loop s).toNat 64).HasBytes t.external
      (HMAC.keyPad key (old ^^^ loop.mask)) := by
  refine ⟨HMAC.keyPad_size _ _, ?_⟩
  intro i
  have hi : i.val < 64 := by simpa only [HMAC.keyPad_size] using i.isLt
  have hinput := input.2 ⟨i.val, by simpa only [HMAC.keyPad_size] using hi⟩
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hinput ⊢
  rw [post.bytes i.val hi]
  change some ((s.external[buffer loop s + BitVec.ofNat 64 i.val]?).getD 0 ^^^ loop.mask) = _
  rw [hinput]
  simp only [Option.getD_some]
  rw [HMAC.keyPad_getElem key old i.val hi,
    HMAC.keyPad_getElem key (old ^^^ loop.mask) i.val hi, UInt8.xor_assoc]

end P256.Proofs.HMAC.Pad
