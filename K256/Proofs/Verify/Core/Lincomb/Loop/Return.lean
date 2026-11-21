import K256.Proofs.Verify.Core.Lincomb.Loop.State
import K256.Proofs.Verify.Core.Lincomb.Recode.Stack
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Generate.Generator.Multiply.Lookup.Memory
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve
open Generate.Generator.Multiply.Lookup (copyGuard copyStored)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem finish {a b : Registers} {m n : Ram} {sp dst : BitVec 64} {q : Projective}
    (entry : RoutineEntry a m sp 0x478) (state : SavedFrame a m sp dst b n)
    (write : Writable Extracted.programImage m dst 120)
    (dest : Outside [scratch sp 0x478, ⟨sp.toNat, 8⟩] dst 120)
    (point : q.Stored n (baseSp sp + 0x130)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l11075a, b, n⟩, []⟩ out ∧
      RoutineReturn a m sp 0x478 [⟨dst.toNat, 120⟩] out ∧ q.Stored out.store dst := by
  let src := baseSp sp + 0x130
  let buffer : MemoryRegion := ⟨dst.toNat, 120⟩
  let final := memCopy n dst src 120
  have room := entry.room
  have returnLow := entry.returnSlot.low
  have dstApart : dst.toNat + 120 ≤ sp.toNat - 0x478 ∨ sp.toNat + 8 ≤ dst.toNat := by
    have outsideStack := dest.2 (scratch sp 0x478) (.head _)
    have outsideReturn := dest.2 (⟨sp.toNat, 8⟩ : MemoryRegion) (.tail _ (.head _))
    change dst.toNat + 120 ≤ sp.toNat - 0x478 ∨ sp.toNat - 0x478 + 0x478 ≤ dst.toNat at outsideStack
    change dst.toNat + 120 ≤ sp.toNat ∨ sp.toNat + 8 ≤ dst.toNat at outsideReturn
    omega
  have srcAddr : src = sp - 0xa8 := by dsimp only [src, baseSp]; bv_omega
  have srcNat : src.toNat = sp.toNat - 0xa8 := by
    rw [srcAddr]
    exact Recode.subNat (by change 0xa8 ≤ sp.toNat; omega)
  have srcRead : Readable n src 120 := by
    rw [srcAddr]
    exact ((Recode.stackSlot entry (by decide) (by decide)).of_frame state.frame).readable
  have copy : RepMovsOk Extracted.programImage n 0 src dst 15 8 0x110772 3 := by
    apply copyGuard srcRead
      (Recode.storeGuard (off := 24) (write.of_frame state.frame) code_l11075a (by decide))
    rw [srcNat]
    rcases dstApart with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have copiedFrame : RamWriteFrame n final [buffer] := by
    apply Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl _ _)
    exact ⟨buffer, .head _, Nat.le_refl _, Nat.le_refl _, dest.1⟩
  have finalFrame : RamWriteFrame m final [scratch sp 0x478, buffer] := by
    have extended : RamWriteFrame m n [scratch sp 0x478, buffer] :=
      ⟨fun x h => state.frame.outside x ⟨h.1, fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact h.2 _ (.head _)⟩, state.frame.present⟩
    apply extended.trans copiedFrame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨buffer, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩
  have stackRead (off : BitVec 64) (fits : off.toNat ≤ 0x478) (top : 8 ≤ off.toNat) :
      LoadOk final (sp - off) 8 :=
    let h := ((Recode.stackSlot entry fits top).of_frame finalFrame).readable
    ⟨h.low, h.present⟩
  have dstRead : LoadOk n (baseSp sp + 0xd0) 8 := by
    have addr : baseSp sp + 0xd0 = sp - 0x108 := by dsimp only [baseSp]; bv_omega
    rw [addr]
    let h := ((Recode.stackSlot entry (off := 0x108) (len := 8)
      (by decide) (by decide)).of_frame state.frame).readable
    exact ⟨h.low, h.present⟩
  have same (off : BitVec 64) (fits : off.toNat ≤ 48) :
      memLoad final (sp - off) 64 = memLoad n (sp - off) 64 := by
    have addr : (sp - off).toNat = sp.toNat - off.toNat := Recode.subNat (by omega)
    apply copiedFrame.memLoad_eq
    refine ⟨by rw [addr]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (sp - off).toNat + 8 ≤ dst.toNat ∨ dst.toNat + 120 ≤ (sp - off).toNat
    rw [addr]
    rcases dstApart with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have ret : memLoad final sp 64 = memLoad m sp 64 := by
    have h := same 0 (by decide)
    rw [show sp - (0 : BitVec 64) = sp from BitVec.sub_zero _] at h
    exact h.trans (state.frame.memLoad_eq (Recode.outsideReturn returnLow room))
  have retRead : LoadOk final sp 8 := ⟨returnLow, (entry.returnSlot.of_frame finalFrame).present⟩
  have pop3 := stackRead 48 (by decide) (by decide)
  have pop12 := stackRead 40 (by decide) (by decide)
  have pop13 := stackRead 32 (by decide) (by decide)
  have pop14 := stackRead 24 (by decide) (by decide)
  have pop15 := stackRead 16 (by decide) (by decide)
  have pop5 := stackRead 8 (by decide) (by decide)
  have mem3 := (same 48 (by decide)).trans state.rbx
  have mem12 := (same 40 (by decide)).trans state.r12
  have mem13 := (same 32 (by decide)).trans state.r13
  have mem14 := (same 24 (by decide)).trans state.r14
  have mem15 := (same 16 (by decide)).trans state.r15
  have mem5 := (same 8 (by decide)).trans state.rbp
  have rsp : b[4].get 64 = baseSp sp := congrArg (Value.get 64) state.rsp
  have df : b[22].get 1 = 0 :=
    congrArg (Value.get 1) ((state.control 22 (by decide)).trans entry.df)
  have stack3 : baseSp sp + 0x1a8 = sp - 48 := by dsimp only [baseSp]; bv_omega
  have stack12 : sp - 48 + 8 = sp - 40 := by bv_omega
  have stack13 : sp - 40 + 8 = sp - 32 := by bv_omega
  have stack14 : sp - 32 + 8 = sp - 24 := by bv_omega
  have stack15 : sp - 24 + 8 = sp - 16 := by bv_omega
  have stack5 : sp - 16 + 8 = sp - 8 := by bv_omega
  have stackEnd : sp - 8 + 8 = sp := by bv_omega
  refine ⟨?_, Recode.done ?run, ?post, ?stored⟩
  case run =>
    dsimp only [src, final] at copy pop3 pop12 pop13 pop14 pop15 pop5 retRead ret
    dsimp only [src, final] at mem3 mem12 mem13 mem14 mem15 mem5
    cfg_eval [rsp, df, state.dest, dstRead, stack3, stack12, stack13, stack14, stack15,
      stack5, stackEnd, false_or]
    simp only [copy, pop3, pop12, pop13, pop14, pop15, pop5, retRead, ret, entry.returnLow,
      mem3, mem12, mem13, mem14, mem15, mem5, and_self, ite_true]
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_, finalFrame⟩
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Recode.saveValue entry (i := 3) (by decide)
    · exact Recode.saveValue entry (i := 5) (by decide)
    · exact Recode.saveValue entry (i := 12) (by decide)
    · exact Recode.saveValue entry (i := 13) (by decide)
    · exact Recode.saveValue entry (i := 14) (by decide)
    · exact Recode.saveValue entry (i := 15) (by decide)
    · exact state.control 22 (by decide)
    · exact state.control 39 (by decide)
    · exact state.control 50 (by decide)
    · exact state.control 51 (by decide)
  case stored => exact copyStored point

end K256.Proofs.Verify.Core.Lincomb.Loop
