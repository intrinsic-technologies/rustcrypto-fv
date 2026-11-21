import Sha1.Proofs.MemoryRoutines.Stos.Loop

namespace Sha1.Proofs.MemoryRoutines.Stos

open X86 X86.Machine X86.UserProcess X86Proofs

theorem Pre.readyLoop [Bindings] {kind : Kind} {p : BitVec 64} {s : RamState}
    (h : ReadyToStep s) (hcode : CodeIn (codeRange p kind.code) s) (hpre : Pre kind p s)
    (count : Nat) (hn : (rcx.read s).toNat = count + 1) : ReadyLoop kind s (count + 1) := by
  have hc : rcx.read s = BitVec.ofNat 64 (count + 1) := by
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcount : rcx.read s ≠ 0 := by
    intro he
    rw [he] at hn
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    omega
  refine ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt, ?_, hc,
    hn ▸ hpre.dstLow, hpre.dstAlign hcount, hn ▸ hpre.dstMem,
    hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
  rw [hpre.rip]
  exact hcode.low (by cases kind <;> simp [Kind.code]) (by cases kind <;> decide)

theorem rep_stos_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (kind : Kind) (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p kind.code) s) (hpre : Pre kind p s) :
    Done kind s (nextStates (max (rcx.read s).toNat 1) s) (rcx.read s).toNat := by
  rcases hn : (rcx.read s).toNat with _ | k
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have hs := rep_stos_step_zero kind s h.midRep (hpre.rip ▸ hcode.bytesAt)
      (hpre.rip ▸ hcode.low (by cases kind <;> simp [Kind.code]) (by cases kind <;> decide)) hz
    simp only [Nat.max_eq_right (show 0 ≤ 1 by omega), nextStates_one, nextState_of_step hs]
    have hag : AgreesExcept [.rip] (clearRep s) (repStosZeroAfter kind s) := by
      rw [← clearRep_eq (repStosZeroAfter_repeat kind s)]
      exact repStosZeroAfter_agrees kind s
    have ha : AgreesExcept [.rip] s (repStosZeroAfter kind s) := by
      simpa only [clearRep_eq h.ready.repeatClear] using hag
    refine ⟨ReadyToStep.of_agreesExcept h ha h.memory.tables,
      repStosZeroAfter_rip kind s h.ready.msr, ?_, ?_, ?_, hag.mono (by simp)⟩
    · rw [ha.read (r := 1) (n := 64) (by simp)]; exact hz
    · rw [ha.read (r := 7) (n := 64) (by simp)]; simp
    · intro i hi; simp at hi
  · rw [Nat.max_eq_left (by omega)]
    exact rep_stos_loop hstride kind k s (hpre.readyLoop h hcode k hn)

theorem Done.agrees_of_ready [Bindings] {kind : Kind} {s t : RamState} {count : Nat}
    (hd : Done kind s t count) (h : ReadyToStep s) :
    AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (kind.bytes * count), .rip] s t := by
  simpa only [clearRep_eq h.ready.repeatClear] using hd.agrees

theorem Done.codeIn [Bindings] {kind : Kind} {p : BitVec 64} {s t : RamState}
    (hd : Done kind s t (rcx.read s).toNat) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p kind.code) s) (hpre : Pre kind p s) :
    CodeIn (codeRange p kind.code) t := by
  apply CodeIn.of_agreesExcept (hd.agrees_of_ready h) _ hcode
  intro x hx c hc hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> try exact hcover
  obtain ⟨i, hi, he⟩ := hcover
  obtain ⟨j, hj, hjx⟩ := exists_of_mem_codeRange hx
  exact hpre.dstCode i hi j hj (he.symm.trans hjx)

theorem rep_stos_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (kind : Kind) (boundary : ReturnBoundary) (p : BitVec 64) (s : RamState)
    (h : ReadyToStep s) (hcode : CodeIn (codeRange p kind.code) s) (hpre : Pre kind p s)
    (hstart : p ≠ boundary.rip)
    (hend : p + BitVec.ofNat 64 kind.code.length ≠ boundary.rip) :
    Advances boundary (max (rcx.read s).toNat 1) s
      (nextStates (max (rcx.read s).toNat 1) s) := by
  rcases hn : (rcx.read s).toNat with _ | k
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have hs := rep_stos_step_zero kind s h.midRep (hpre.rip ▸ hcode.bytesAt)
      (hpre.rip ▸ hcode.low (by cases kind <;> simp [Kind.code]) (by cases kind <;> decide)) hz
    simp only [Nat.max_eq_right (show 0 ≤ 1 by omega), nextStates_one, nextState_of_step hs]
    apply Advances.of_step hs
    left
    rw [repStosZeroAfter_rip kind s h.ready.msr, hpre.rip]
    exact hend
  · rw [Nat.max_eq_left (by omega)]
    exact (hpre.readyLoop h hcode k hn).advances hstride kind boundary k s
      (hpre.rip ▸ hstart) (hpre.rip ▸ hend)

end Sha1.Proofs.MemoryRoutines.Stos
