import Sha3.Proofs.Finalize.Reset.Prefix
import Sha3.Proofs.Memset

namespace Sha3.Proofs.Finalize.Reset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def changes (ptr : BitVec 64) : List Component := scalarChanges ++ Memset.clobbers ptr

structure Pre (boundary : ReturnBoundary) (v : Variant) (ptr sp target : BitVec 64)
    (s : RamState) (keccak : Bool := false) (fullState : Bool := false)
    extends PrefixPre (epilogueAddress v true (keccak := keccak) (fullState := fullState)) ptr sp s
        where
  aligned : ptr.toNat % 8 = 0
  direction : DirectionFlagUnset s
  destination : MemReadable s ptr 201
  tables : (MemoryRegion.mk ptr.toNat 201).Avoids InPageTables
  program : (MemoryRegion.mk ptr.toNat 201).Avoids InProgram
  returnRead : MemReadable s sp 8
  returnSlot : (Operand.mem sp : Operand 64).read s = target
  targetInProgram : InProgram target
  disjoint : RangeApart ptr 201 sp 8
  inside : sp ≠ boundary.rsp

structure Done [Bindings] (ptr sp target : BitVec 64) (s t : RamState) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = target
  stack : stackPtr t = sp + 8
  rbx : (Operand.reg 3 : Operand 64).read t = (Operand.mem (sp - 16) : Operand 64).read s
  r14 : (Operand.reg 14 : Operand 64).read t = (Operand.mem (sp - 8) : Operand 64).read s
  zero : ∀ i < 201, t.external[ptr + BitVec.ofNat 64 i]? = some 0
  agrees : AgreesExcept (changes ptr) s t

theorem changes_writesWithin {ptr : BitVec 64} {regions : Vector MemoryRegion n}
    (h : ∀ i < 201, ∃ region ∈ regions,
      region.Contains (ptr + BitVec.ofNat 64 i).toNat) : WritesWithin (changes ptr) regions := by
  intro c hc x hcover
  rcases List.mem_append.mp hc with hc | hc
  · simp only [scalarChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hcover.elim
  · exact Memset.clobbers_writesWithin h c hc x hcover

theorem Done.read {bindings : Bindings} {ptr sp target : BitVec 64} {s t : RamState}
    (h : Done ptr sp target s t) (r : BitVec 5)
    (hr : r ∈ ([5, 12, 13, 15] : List (BitVec 5))) :
    (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s := by
  apply h.agrees.read
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp [changes, scalarChanges, Memset.clobbers]

theorem finish {keccak fullState : Bool} [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) (hboundary : ¬ InProgram boundary.rip)
    {v : Variant} {ptr sp target : BitVec 64} {s a : RamState}
    (hp : Pre (keccak := keccak) (fullState := fullState) boundary v ptr sp target s) (ha :
        ReadyToStep a)
    (hc : CodeIn Extracted.programImage a)
    (hprefix : PrefixDone ptr sp s a)
    (hip : a.RIP = 0x106a20) :
    ∃ t, Advances boundary 45 a t ∧ Done ptr sp target s t := by
  have hm := scalarChanges_external hprefix.agrees
  have htop : stackTop a = target := by
    change memLoad a.external (stackPtr a) 64 = target
    rw [hprefix.stack, hm]
    exact hp.returnSlot
  have htarget : target.toNat < 2^32 := by
    obtain ⟨byte, hbyte⟩ := hp.targetInProgram
    exact (hc (target, byte) hbyte).1
  have pre : Memset.Pre boundary a := {
    rip := hip
    length := hprefix.length
    value := hprefix.value
    aligned := by rw [hprefix.pointer]; exact hp.aligned
    direction := hprefix.agrees.directionFlagClear hp.direction
    destination := by rw [hprefix.pointer]; exact hp.destination.of_external_eq hm
    tables := by rw [hprefix.pointer]; exact hp.tables
    program := by rw [hprefix.pointer]; exact hp.program
    stack := by rw [hprefix.stack]; exact hp.returnRead.of_external_eq hm
    returnLow := htop ▸ htarget
    disjoint := by rw [hprefix.pointer, hprefix.stack]; exact hp.disjoint
    inside := hprefix.stack ▸ hp.inside
    afterReturn := .inl (by rw [htop]; exact fun he ↦ hboundary (he ▸ hp.targetInProgram)) }
  obtain ⟨t, hat, ht⟩ := Memset.memset201_steps hstride boundary a ha hc pre
  refine ⟨t, hat, ht.ready, ht.code, ht.rip.trans htop, ?_, ?_, ?_, ?_, ?_⟩
  · exact ht.rsp.trans (congrArg (· + 8) hprefix.stack)
  · exact (ht.agrees.read (n := 64) (r := 3) (by simp [Memset.clobbers])).trans hprefix.rbx
  · exact (ht.agrees.read (n := 64) (r := 14) (by simp [Memset.clobbers])).trans hprefix.r14
  · simpa only [hprefix.pointer] using ht.zero
  · have hf := ht.agrees
    rw [hprefix.pointer] at hf
    exact hprefix.agrees.trans hf

end Sha3.Proofs.Finalize.Reset
