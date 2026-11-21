import P256.Proofs.Verifying.Message.Hash.Initial
import P256.Proofs.Verifying.Message.Hash.Branch
import P256.Proofs.Verifying.Message.Hash.Setup
import P256.Proofs.Verifying.Message.Hash.Head

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Entered [Bindings] (initial s t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Frame initial t where
  execution : ∃ fuel, Advances boundary fuel initial t
  memory : t.external = s.external
  rip : t.RIP = 0x10d65d
  current : t.regValue .r13 = initial.regValue .rdx
  endPointer : t.regValue .r12 = initial.regValue .rdx + 16
  source : t.regValue .r14 = memLoad initial.external (initial.regValue .rdx) 64
  length : t.regValue .r15 = BitVec.ofNat 64 message.size
  position : t.regValue .rbx = 0
  capacity : t.regValue .rdx = 64
  remaining : t.regValue .rbp = BitVec.ofNat 64 message.size - 64
  carry : (StatusFlags.ofRFLAGS t.RFLAGS).CF =
    (subSpec (BitVec.ofNat 64 message.size) 64).2.CF

theorem enter [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (initialized : Initialized initial s boundary) :
    ∃ t, Entered initial s t boundary message := by
  have regs := initialized_registers initialized
  obtain ⟨a, runA, readyA, ripA, agreesA⟩ := entry_branch
    (readyToStep initialized.machine initialized.bindingsSupported) initialized.loaded
    initialized.rip (regs.1.trans pre.count) pre.outerBoundary
  have stateA := initialized.toFrameState.after_registers readyA agreesA
    (by simp [Component.Covers]) (by simp)
  obtain ⟨fuelB, b, runB, readyB, _, effectB⟩ := setup_run boundary pre.outerBoundary a readyA
    (programText_slice (programLoaded_codeIn stateA.loaded) 0xd5fe setupBytes
      (by decide) (by decide +kernel)) ripA
  have agreesB : AgreesExcept [.reg 12, .reg 13, .flags, .rip] a b := effectB.agrees
  have stateB := stateA.after_registers readyB agreesB (by simp [Component.Covers]) (by simp)
  have memoryB : b.external = s.external :=
    (agreesB.external (by simp [Component.Covers])).trans
      (agreesA.external (by simp [Component.Covers]))
  have currentB : b.regValue .r13 = initial.regValue .rdx := by
    have h : b.regValue .r13 = a.regValue .rdx := effectB.writes.2
    exact h.trans ((agreesA.read (n := 64) (r := 2) (by simp)).trans regs.2)
  have endB : b.regValue .r12 = initial.regValue .rdx + 16 := by
    have h : b.regValue .r12 = (a.regValue .rcx <<< 4) + a.regValue .rdx := effectB.writes.1
    have countA : a.regValue .rcx = 1 :=
      (agreesA.read (n := 64) (r := 1) (by simp)).trans (regs.1.trans pre.count)
    have descA : a.regValue .rdx = initial.regValue .rdx :=
      (agreesA.read (n := 64) (r := 2) (by simp)).trans regs.2
    rw [h, countA, descA]
    exact BitVec.add_comm _ _
  have descriptor (offset : Nat) (bound : offset + 8 ≤ 16) :
      MemReadable b (initial.regValue .rdx + BitVec.ofNat 64 offset) 8 := by
    apply readable_of_grow _ stateB.allocated
    apply memoryRegion_memReadable pre.descriptorBounded pre.descriptorAllocated
    all_goals
      have bounded : (initial.regValue .rdx).toNat + 16 < 2^32 := pre.descriptorBounded
      simp only [registerRegion]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]
      omega
  have hp : Head.Pre b := by
    refine ⟨effectB.rip, ?_, ?_, ?_⟩
    · change MemReadable b (b.regValue .r13) 8
      rw [currentB]
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using descriptor 0 (by decide)
    · change MemReadable b (b.regValue .r13 + 8) 8
      rw [currentB]
      simpa only [BitVec.ofNat_eq_ofNat] using descriptor 8 (by decide)
    · exact ScalarFrame.stack_readable pre.toCalleePre stateB (by decide) (by decide)
  have pointer : memLoad b.external (b.regValue .r13) 64 =
      memLoad initial.external (initial.regValue .rdx) 64 := by
    rw [currentB, memoryB]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      descriptor_read pre initialized.stackFrame (offset := 0) (by decide)
  have length : Head.length b = BitVec.ofNat 64 message.size := by
    change memLoad b.external (b.regValue .r13 + 8) 64 = _
    rw [currentB, memoryB]
    have h := descriptor_read pre initialized.stackFrame (offset := 8) (by decide)
    have h' : memLoad s.external (initial.regValue .rdx + 8) 64 =
        memLoad initial.external (initial.regValue .rdx + 8) 64 := by
      simpa only [BitVec.ofNat_eq_ofNat] using h
    exact h'.trans pre.messageLength
  have position : Head.position b = 0 := by
    have pos := initialized.hash.position
    change s.external[frameBase initial + 472 + 63]? = some 0 at pos
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at pos
    change (memLoad b.external (stackPtr b + 535) 8).setWidth 64 = _
    rw [memoryB, stateB.rsp, memLoad_8]
    change ((s.external[frameBase initial + 535]?).getD 0).toBitVec.setWidth 64 = _
    change s.external[frameBase initial + 535]? = some 0 at pos
    rw [pos]
    rfl
  obtain ⟨fuelT, t, runT, readyT, _, effectT⟩ := Head.run boundary pre.outerBoundary b readyB
    (Head.code stateB.loaded) hp
  have agreesT : AgreesExcept [.reg 14,.reg 15,.reg 3,.reg 2,.reg 5,.flags,.rip] b t :=
    effectT.agrees
  have stateT := stateB.after_registers readyT agreesT (by simp [Component.Covers]) (by simp)
  have writes := effectT.writes
  change t.regValue .r14 = memLoad b.external (b.regValue .r13) 64 ∧
    t.regValue .r15 = Head.length b ∧ t.regValue .rbx = Head.position b ∧
    t.regValue .rdx = 64 - Head.position b ∧
    t.regValue .rbp = Head.length b - (64 - Head.position b) at writes
  rw [pointer, length, position] at writes
  refine ⟨t, stateT, ?_, (agreesT.external (by simp [Component.Covers])).trans memoryB,
    effectT.rip, (agreesT.read (n := 64) (r := 13) (by simp)).trans currentB,
    (agreesT.read (n := 64) (r := 12) (by simp)).trans endB,
    writes.1, writes.2.1, writes.2.2.1, writes.2.2.2.1, writes.2.2.2.2, ?_⟩
  · obtain ⟨fuel, run⟩ := initialized.execution
    exact ⟨fuel + 2 + fuelB + fuelT, ((run.trans runA).trans runB).trans runT⟩
  · have flags := effectT.flags.1
    change (StatusFlags.ofRFLAGS t.RFLAGS).CF =
      (subSpec (Head.length b) (64 - Head.position b)).2.CF at flags
    rw [length, position] at flags
    exact flags

end P256.Proofs.Verifying.Message.Hash
