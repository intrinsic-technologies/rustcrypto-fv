import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.Generator.Multiply.State

namespace K256.Proofs.Generate.Generator.Multiply.Caller

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def coreCallMemory (m : Ram) (sp : BitVec 64) : Ram :=
  let m := memStore m (sp + 72) (0 : BitVec 16)
  let m := memStore m (sp + 64) (0 : BitVec 64)
  let m := memStore m (sp + 56) (0 : BitVec 64)
  let m := memStore m (sp + 48) (0 : BitVec 64)
  let m := memStore m (sp + 40) (0 : BitVec 64)
  let m := memStore m (sp + 32) (0 : BitVec 64)
  let m := memStore m (sp + 24) (0 : BitVec 64)
  let m := memStore m (sp + 16) (0 : BitVec 64)
  let m := memStore m (sp + 8) (0 : BitVec 64)
  let m := memStore m sp (1 : BitVec 64)
  memStore m (sp - 8) (0x10f12f : BitVec 64)

theorem coreCall {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (window : Writable Extracted.programImage m (sp - 8) 82) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l10f0ba, a, m⟩ =
        .call ⟨.l11c880, b, coreCallMemory m sp⟩ (callFrame .l10f12f 0x10f12f) ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[1] = ⟨64, a[15].get 64⟩ ∧ b[2] = ⟨64, 1⟩ ∧
      b[6] = ⟨64, a[14].get 64⟩ ∧ b[7] = ⟨64, a[3].get 64⟩ ∧
      b[8] = ⟨64, 1⟩ ∧ b[9] = ⟨64, sp + 8⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l10f0ba [rsp, coreCallMemory]
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem coreCallFrame {m : Ram} {sp : BitVec 64}
    (window : Writable Extracted.programImage m (sp - 8) 82) :
    RamWriteFrame m (coreCallMemory m sp) [⟨(sp - 8).toNat, 82⟩] := by
  have room := window.readable.low
  have store {o : Ram} {w : Nat} {a k : BitVec 64} (v : BitVec w)
      (frame : RamWriteFrame m o [⟨(sp - 8).toNat, 82⟩])
      (eq : a = sp + k) (fits : (k - (0 - 8)).toNat + w / 8 ≤ 82) :
      RamWriteFrame m (memStore o a v) [⟨(sp - 8).toNat, 82⟩] := by
    have offset := toNat_of_offsets eq (addr_sub sp 8) room fits
    apply frame.memStore
    exact ⟨_, List.mem_singleton_self _, by change (sp - 8).toNat ≤ a.toNat; omega,
      by change a.toNat + w / 8 ≤ (sp - 8).toNat + 82; omega, by omega⟩
  unfold coreCallMemory
  repeat' refine store _ ?_ (by first | apply addr_sub | apply addr_self | rfl) (by decide)
  exact RamWriteFrame.refl _ _

theorem coreCallSlots (m : Ram) (sp : BitVec 64) :
    memLoad (coreCallMemory m sp) (sp - 8) 64 = 0x10f12f ∧
    memLoad (coreCallMemory m sp) sp 64 = 1 := by
  unfold coreCallMemory
  constructor <;> segment_words [] <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Caller
