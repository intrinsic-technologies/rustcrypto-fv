import K256.Proofs.Verify.Core.Lincomb.Recode.Stack

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def ControlSaved (a b : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]

theorem ControlSaved.trans {a b c : Registers} (ab : ControlSaved a b)
    (bc : ControlSaved b c) : ControlSaved a c :=
  fun i h => (bc i h).trans (ab i h)

abbrev writes (sp dst : BitVec 64) : List MemoryRegion :=
  [scratch sp 0x110, ⟨dst.toNat, 257⟩]

theorem returnDigits {a b : Registers} {m m' : Ram} {sp dst : BitVec 64} {ds : List Int}
    (entry : RoutineEntry a m sp 0x110)
    (frame : RamWriteFrame m m' (writes sp dst))
    (dest : Outside [scratch sp 0x110, ⟨sp.toNat, 8⟩] dst 257)
    (saved : SavedAt a sp m') (control : ControlSaved a b)
    (rsp : b[4].get 64 = sp-136) (length : b[14].get 64 = BitVec.ofNat 64 ds.length)
    (bytes : DigitBytes m' dst ds) :
    ∃ out, program.Exec machine ⟨⟨.l110955, b, m'⟩, []⟩ out ∧
      RoutineReturn a m sp 0x110 [⟨dst.toNat,257⟩] out ∧
      out.values[0] = ⟨64, BitVec.ofNat 64 ds.length⟩ ∧ DigitBytes out.store dst ds := by
  have stackRead (off : BitVec 64) (fits : off.toNat ≤ 0x110) (top : 8 ≤ off.toNat) :
      LoadOk m' (sp-off) 8 :=
    let read := ((stackSlot entry fits top).of_frame frame).readable
    ⟨read.low, read.present⟩
  have endpoint : Outside (writes sp dst) sp 8 := by
    have h := outsideReturn entry.returnSlot.low entry.room
    refine ⟨h.1, fun reg hr => ?_⟩
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2 _ (List.mem_singleton_self _)
    · rcases dest.2 ⟨sp.toNat, 8⟩ (by simp) with h | h
      · exact Or.inr h
      · exact Or.inl h
  have retWord := frame.memLoad_eq (k := 64) endpoint
  have retRead : LoadOk m' sp 8 :=
    ⟨entry.returnSlot.low, (entry.returnSlot.of_frame frame).present⟩
  have pop3 := stackRead 48 (by decide) (by decide)
  have pop12 := stackRead 40 (by decide) (by decide)
  have pop13 := stackRead 32 (by decide) (by decide)
  have pop14 := stackRead 24 (by decide) (by decide)
  have pop15 := stackRead 16 (by decide) (by decide)
  have pop5 := stackRead 8 (by decide) (by decide)
  have mem3 : memLoad m' (sp-48) 64 = a[3].get 64 := saved 5
  have mem12 : memLoad m' (sp-40) 64 = a[12].get 64 := saved 4
  have mem13 : memLoad m' (sp-32) 64 = a[13].get 64 := saved 3
  have mem14 : memLoad m' (sp-24) 64 = a[14].get 64 := saved 2
  have mem15 : memLoad m' (sp-16) 64 = a[15].get 64 := saved 1
  have mem5 : memLoad m' (sp-8) 64 = a[5].get 64 := saved 0
  have stack3 : sp-136+88 = sp-48 := by bv_omega
  have stack12 : sp-48+8 = sp-40 := by bv_omega
  have stack13 : sp-40+8 = sp-32 := by bv_omega
  have stack14 : sp-32+8 = sp-24 := by bv_omega
  have stack15 : sp-24+8 = sp-16 := by bv_omega
  have stack5 : sp-16+8 = sp-8 := by bv_omega
  have stackEnd : sp-8+8 = sp := by bv_omega
  refine ⟨?_, ?exec, ?post, ?length, ?bytes⟩
  case exec =>
    apply done
    cfg_eval [rsp, length, stack3, stack12, stack13, stack14, stack15, stack5, stackEnd,
      pop3, pop12, pop13, pop14, pop15, pop5, retRead, retWord, entry.returnLow,
      mem3, mem12, mem13, mem14, mem15, mem5]
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_, frame⟩
    intro ⟨i, bound⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact saveValue entry (i := 3) (by decide)
    · exact saveValue entry (i := 5) (by decide)
    · exact saveValue entry (i := 12) (by decide)
    · exact saveValue entry (i := 13) (by decide)
    · exact saveValue entry (i := 14) (by decide)
    · exact saveValue entry (i := 15) (by decide)
    · exact control 22 (by decide)
    · exact control 39 (by decide)
    · exact control 50 (by decide)
    · exact control 51 (by decide)
  case length => rfl
  case bytes => exact bytes

end K256.Proofs.Verify.Core.Lincomb.Recode
