import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Serialize.Transfer
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Flag
import K256.Proofs.Generate.Generator.Multiply.State

namespace K256.Proofs.Generate.Generator.Multiply.Caller

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

abbrev memcpyPreserved := [3,5,9,10,11,12,13,14,15,22,39,50,51]

private theorem resumeCopy {l next : Label} {a b : Registers} {initial m : Ram}
    {sp src dst ret n : BitVec 64}
    (call : program.runBlock (dialect Extracted.programImage) ⟨l, a, initial⟩ =
      .call ⟨.l12a820, b, memStore m (sp - 8) ret⟩ (callFrame next ret))
    (rsp : b[4].get 64 = sp - 8) (rdi : b[7].get 64 = dst) (rsi : b[6].get 64 = src)
    (rdx : b[2].get 64 = n) (df : b[22].get 1 = 0)
    (hsrc : Readable m src n.toNat) (hdst : Writable Extracted.programImage m dst n.toNat)
    (slot : Readable m (sp - 8) 8) (low : ret.toNat < 2^32)
    (disj : src.toNat + n.toNat ≤ dst.toNat ∨ dst.toNat + n.toNat ≤ src.toNat)
    (apart : RangeApart dst n.toNat (sp - 8) 8) :
    ∃ c, Reaches l a initial next c (memCopy (memStore m (sp - 8) ret) dst src n.toNat) ∧
      c[4] = ⟨64, sp⟩ ∧ ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → c[i] = b[i] := by
  have tag := memLoad_memStore_same m (sp - 8) ret (by decide) (by decide)
  obtain ⟨out, run, store, gate, _, back, keep⟩ := Serialize.memcpy rdi rsi rdx rsp df
    (hsrc.memStore _ ret) (hdst.memStore _ ret) disj apart (slot.memStore _ ret) (tag ▸ low)
  have path := Sample.reachesAfterSampleCall call run (tag ▸ gate) []
  refine ⟨out.values, store ▸ path, ?_, keep⟩
  simpa only [BitVec.sub_add_cancel] using back

def tableCopyMemory (m : Ram) (sp : BitVec 64) : Ram :=
  let first := memCopy (memStore m (sp - 8) (0x10f0a4 : BitVec 64)) (sp + 968) (sp + 2888) 960
  memCopy (memStore first (sp - 8) (0x10f0ba : BitVec 64)) (sp + 4000) (sp + 8) 1920

private theorem copyRightCall {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (target : a[13].get 64 = 0x12a820)
    (src : a[15].get 64 = sp + 2888) (slot : Writable Extracted.programImage m (sp - 8) 8) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10f091, a, m⟩ =
        .call ⟨.l12a820, b, memStore m (sp - 8) (0x10f0a4 : BitVec 64)⟩ (callFrame .l10f0a4 0x10f0a4) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 968 ∧ b[6].get 64 = sp + 2888 ∧
      b[2].get 64 = 960 ∧ ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp - 8) 8 0x10f0a1 3 := by slot_guard using code_l10f091
  refine ⟨?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l10f091 [rsp, target, src, push]
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h
    simp only [memcpyPreserved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem copyTableCall {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (target : a[13].get 64 = 0x12a820)
    (src : a[12].get 64 = sp + 8) (slot : Writable Extracted.programImage m (sp - 8) 8) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10f0a4, a, m⟩ =
        .call ⟨.l12a820, b, memStore m (sp - 8) (0x10f0ba : BitVec 64)⟩ (callFrame .l10f0ba 0x10f0ba) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 4000 ∧ b[6].get 64 = sp + 8 ∧
      b[2].get 64 = 1920 ∧ b[15] = ⟨64, sp + 4000⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → i.val ≠ 15 → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp - 8) 8 0x10f0b7 3 := by slot_guard using code_l10f0a4
  refine ⟨?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l10f0a4 [rsp, target, src, push]
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h ne
    simp only [memcpyPreserved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | contradiction

theorem stackCopy {l next : Label} {a b : Registers} {initial m : Ram}
    {sp src dst n ret : BitVec 64} {size : Nat}
    (window : Writable Extracted.programImage m (sp - 8) size)
    (sfit : (src - (0 - 8)).toNat + n.toNat ≤ size)
    (dfit : (dst - (0 - 8)).toNat + n.toNat ≤ size)
    (sep : (src - (0 - 8)).toNat + n.toNat ≤ (dst - (0 - 8)).toNat ∨
      (dst - (0 - 8)).toNat + n.toNat ≤ (src - (0 - 8)).toNat)
    (afterSlot : 8 ≤ (dst - (0 - 8)).toNat) (low : ret.toNat < 2^32)
    (call : program.runBlock (dialect Extracted.programImage) ⟨l,a,initial⟩ =
      .call ⟨.l12a820, b, memStore m (sp - 8) ret⟩ (callFrame next ret))
    (rsp : b[4].get 64 = sp - 8) (rdi : b[7].get 64 = sp + dst) (rsi : b[6].get 64 = sp + src)
    (rdx : b[2].get 64 = n) (df : b[22].get 1 = 0) :
    ∃ c, Reaches l a initial next c (memCopy (memStore m (sp - 8) ret) (sp + dst) (sp + src) n.toNat) ∧
      c[4] = ⟨64, sp⟩ ∧ ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → c[i] = b[i] := by
  have room := window.readable.low
  have sn := toNat_of_offsets (rfl : sp + src = _) (addr_sub sp 8) window.readable.low sfit
  have dn := toNat_of_offsets (rfl : sp + dst = _) (addr_sub sp 8) window.readable.low dfit
  apply resumeCopy call rsp rdi rsi rdx df (window.readable.of_offsets rfl (addr_sub sp 8) sfit)
    (window.of_offsets rfl (addr_sub sp 8) dfit) (window.readable.sub (Nat.le_refl _) (by omega)) low
  · omega
  · apply RangeApart.of_toNat
    · omega
    · omega
    · omega

theorem tableCopies {a : Registers} {m : Ram} {sp : BitVec 64}
    (window : Writable Extracted.programImage m (sp - 8) 5928)
    (rsp : a[4].get 64 = sp) (target : a[13].get 64 = 0x12a820)
    (right : a[15].get 64 = sp + 2888) (left : a[12].get 64 = sp + 8)
    (df : a[22].get 1 = 0) :
    ∃ c, Reaches .l10f091 a m .l10f0ba c (tableCopyMemory m sp) ∧
      c[4] = ⟨64, sp⟩ ∧ c[15] = ⟨64, sp + 4000⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → i.val ≠ 15 → c[i] = a[i] := by
  have slot : Writable Extracted.programImage m (sp - 8) 8 := by slot_state region
  obtain ⟨b, call, bsp, bdst, bsrc, bn, kept⟩ := copyRightCall rsp target right slot
  have bdf := congrArg (Value.get 1) (kept 22 (by decide))
  obtain ⟨c, run, csp, saved⟩ := stackCopy window (by decide) (by decide) (by decide)
    (by decide) (by decide) call bsp bdst bsrc bn (bdf.trans df)
  let m' := memCopy (memStore m (sp - 8) (0x10f0a4 : BitVec 64)) (sp + 968) (sp + 2888) 960
  have window' : Writable Extracted.programImage m' (sp - 8) 5928 :=
    (window.memStore _ (0x10f0a4 : BitVec 64)).memStore _ _
  have slot' : Writable Extracted.programImage m' (sp - 8) 8 := by slot_state region
  have unchanged (i : Fin Reg.count) (hi : i.val ∈ memcpyPreserved) : c[i] = a[i] :=
    (saved i hi).trans (kept i hi)
  obtain ⟨e, call', esp, edst, esrc, en, e15, keep'⟩ := copyTableCall
    (congrArg (Value.get 64) csp) ((congrArg (Value.get 64) (unchanged 13 (by decide))).trans target)
    ((congrArg (Value.get 64) (unchanged 12 (by decide))).trans left) slot'
  have df' := (congrArg (Value.get 1) (keep' 22 (by decide) (by decide))).trans
    ((congrArg (Value.get 1) (unchanged 22 (by decide))).trans df)
  obtain ⟨f, run', fsp, saved'⟩ := stackCopy window' (by decide) (by decide) (by decide)
    (by decide) (by decide) call' esp edst esrc en df'
  exact ⟨f, run.trans run', fsp, (saved' 15 (by decide)).trans e15,
    fun i hi ne => (saved' i hi).trans ((keep' i hi ne).trans (unchanged i hi))⟩

end K256.Proofs.Generate.Generator.Multiply.Caller
