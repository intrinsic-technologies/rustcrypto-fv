import Sha1.Proofs.Compress.Machine.Interface
import X86Proofs.Instructions.Movs.Execution

namespace Sha1.Proofs.MemoryRoutines

open X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program

abbrev rdx : Operand 64 := .reg 2

def destination (s : RamState) : Prelude.MemoryRegion :=
  ⟨(rdi.read s).toNat, (rdx.read s).toNat⟩

structure WritableRange (s : RamState) (address : BitVec 64) (length : Nat) : Prop where
  readable : MemReadable s address length
  tables : ∀ i < length, ¬ InPageTables (address + BitVec.ofNat 64 i)
  code : ∀ i < length, ¬ InProgram (address + BitVec.ofNat 64 i)

structure CallPre (entry : BitVec 64) (codeLength : Nat) (s : RamState) : Prop where
  rip : s.RIP = entry
  df : DirectionFlagClear s.RFLAGS
  dst : WritableRange s (rdi.read s) (rdx.read s).toNat
  returnSlot : MemReadable s (stackPtr s) 8
  dstReturn : RangeApart (rdi.read s) (rdx.read s).toNat (stackPtr s) 8
  returnLow : (returnBoundary s).rip.toNat < 2^32
  returnOutside : (returnBoundary s).rip.toNat < entry.toNat ∨
    entry.toNat + codeLength ≤ (returnBoundary s).rip.toNat

structure MemcpyPre (s : RamState) : Prop extends CallPre 0x103730 47 s where
  src : MemReadable s (rsi.read s) (rdx.read s).toNat
  disjoint : (rsi.read s).toNat + (rdx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + (rdx.read s).toNat ≤ (rsi.read s).toNat

abbrev MemsetPre (s : RamState) := CallPre 0x1036e0 69 s

def callChanges (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (rdi.read s) (rdx.read s).toNat]

structure CallResult [Bindings] (s t : RamState) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = stackPtr s + 8
  result : rax.read t = rdi.read s
  agrees : AgreesExcept (callChanges s) s t

structure MemcpyResult [Bindings] (s t : RamState) : Prop extends CallResult s t where
  copy : ∀ i < (rdx.read s).toNat,
    t.external[rdi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]?

structure MemsetResult [Bindings] (s t : RamState) : Prop extends CallResult s t where
  fill : ∀ i < (rdx.read s).toNat,
    t.external[rdi.read s + BitVec.ofNat 64 i]? =
      some (UInt8.ofBitVec ((rsi.read s).setWidth 8))

theorem WritableRange.of_agrees {s t : RamState} {address : BitVec 64} {length : Nat}
    {changes : List Component} (h : WritableRange s address length)
    (ha : AgreesExcept changes s t) : WritableRange t address length :=
  ⟨⟨h.readable.low, fun i hi ↦ ha.grow _ (h.readable.mem i hi)⟩, h.tables, h.code⟩

theorem CallResult.directionFlagClear [Bindings] {s t : RamState} (h : CallResult s t)
    (hdf : DirectionFlagClear s.RFLAGS) : DirectionFlagClear t.RFLAGS :=
  (h.agrees.directionFlagClear (by simp [callChanges]) ⟨hdf⟩).df

theorem CallResult.calleeSaved [Bindings] {s t : RamState} (h : CallResult s t) :
    CalleeSavedRegistersUnchanged s t := by
  intro register hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.agrees.read (r := 3) (n := 64) (by simp [callChanges])
  · exact h.agrees.read (r := 5) (n := 64) (by simp [callChanges])
  · exact h.agrees.read (r := 12) (n := 64) (by simp [callChanges])
  · exact h.agrees.read (r := 13) (n := 64) (by simp [callChanges])
  · exact h.agrees.read (r := 14) (n := 64) (by simp [callChanges])
  · exact h.agrees.read (r := 15) (n := 64) (by simp [callChanges])

theorem CallResult.frame [Bindings] {s t : RamState} (h : CallResult s t)
    (hlow : (rdi.read s).toNat + (rdx.read s).toNat ≤ 2^32) :
    Prelude.MemoryWriteFrame s t #v[destination s] := by
  apply h.agrees.memoryWriteFrame
  intro c hc address hcover
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨i, hi, rfl⟩ := hcover
  refine ⟨destination s, by simp, ?_⟩
  change (rdi.read s).toNat ≤ _ ∧ _ < (rdi.read s).toNat + (rdx.read s).toNat
  rw [toNat_add_ofNat _ _ (by omega)]
  omega

theorem CallResult.codeIn [Bindings] {s t : RamState} (h : CallResult s t)
    (hw : WritableRange s (rdi.read s) (rdx.read s).toNat)
    (hc : CodeIn Extracted.programImage s) : CodeIn Extracted.programImage t := by
  apply CodeIn.of_agreesExcept h.agrees _ hc
  intro x hx c hc hcover
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover
  obtain ⟨i, hi, he⟩ := hcover
  exact hw.code i hi ⟨x.2, he ▸ hx⟩

end Sha1.Proofs.MemoryRoutines
