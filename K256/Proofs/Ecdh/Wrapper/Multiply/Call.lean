import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.Wrapper.AffineCall
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Ecdh.Wrapper.Multiply

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR

def digitMemory (m : Ram) (sp : BitVec 64) : Ram :=
  let m := memStore m (sp + 184) (0 : BitVec 16)
  let m := memStore m (sp + 176) (0 : BitVec 64)
  let m := memStore m (sp + 168) (0 : BitVec 64)
  let m := memStore m (sp + 160) (0 : BitVec 64)
  let m := memStore m (sp + 152) (0 : BitVec 64)
  let m := memStore m (sp + 144) (0 : BitVec 64)
  let m := memStore m (sp + 136) (0 : BitVec 64)
  let m := memStore m (sp + 128) (0 : BitVec 64)
  let m := memStore m (sp + 120) (0 : BitVec 64)
  let m := memStore m sp (1 : BitVec 64)
  m

set_option maxHeartbeats 650000 in
set_option maxRecDepth 4096 in
theorem coreCall {a : Arguments} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (window : Writable Extracted.programImage m (sp - 8) 194)
    (push : StoreOk Extracted.programImage (digitMemory m sp) (sp - 8) 8 0x101af5 5) :
    ∃ b : Arguments,
      program.runBlock (dialect Extracted.programImage) ⟨.l101a65, a, m⟩ =
        .call ⟨.l11c880, b, memStore (digitMemory m sp) (sp - 8) (0x101afa : BitVec 64)⟩ (callFrame .l101afa 0x101afa) ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[1] = ⟨64, a[15].get 64⟩ ∧ b[2] = ⟨64, 1⟩ ∧
      b[6] = ⟨64, a[14].get 64⟩ ∧ b[7] = ⟨64, sp + 344⟩ ∧
      b[8] = ⟨64, 1⟩ ∧ b[9] = ⟨64, sp + 120⟩ ∧
      b[12] = ⟨64, sp + 344⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,13,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp]
    segment_words [digitMemory]
    iterate 10 (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l101a65)
    refine Eq.trans (ite_eq_left push) ?_
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem coreCallFrame {m : Ram} {sp : BitVec 64}
    (window : Writable Extracted.programImage m (sp - 8) 194) :
    RamWriteFrame m (digitMemory m sp) [⟨(sp - 8).toNat, 194⟩] := by
  have room := window.readable.low
  have store {o : Ram} {w : Nat} {a k : BitVec 64} (v : BitVec w)
      (frame : RamWriteFrame m o [⟨(sp - 8).toNat, 194⟩])
      (eq : a = sp + k) (fits : (k - (0 - 8)).toNat + w / 8 ≤ 194) :
      RamWriteFrame m (memStore o a v) [⟨(sp - 8).toNat, 194⟩] := by
    have offset := toNat_of_offsets eq (addr_sub sp 8) room fits
    apply frame.memStore
    exact ⟨_, List.mem_singleton_self _, by change (sp - 8).toNat ≤ a.toNat; omega,
      by change a.toNat + w / 8 ≤ (sp - 8).toNat + 194; omega, by omega⟩
  unfold digitMemory
  repeat' refine store _ ?_ (by first | apply addr_sub | apply addr_self | rfl) (by decide)
  exact RamWriteFrame.refl _ _

theorem digitCount (m : Ram) (sp : BitVec 64) :
    memLoad (digitMemory m sp) sp 64 = 1 :=
  memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Ecdh.Wrapper.Multiply
