import Sha3.Proofs.Update.EntryExit.Setup
import Sha3.Proofs.Update.Frame

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem CallContext.inputBytes_of_memoryWriteFrame [Bindings]
    {v : Variant} {initial final : RamState} {bytes : ByteArray} {state : Incremental.State}
    (h : CallContext v initial bytes state)
    (hf : MemoryWriteFrame initial final (writeRegions initial)) :
    Bytes final.external (initial.regValue .rdx) bytes.size
      (fun i ↦ (bytes.data[i]?).getD 0) := by
  intro i hi
  rw [hf]
  · exact h.inputBytes i hi
  · intro region hr hcontains
    apply h.inputApart region hr _ ?_ hcontains
    have hl := h.inputRead.low
    simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
    constructor <;> omega

theorem pushedState_state [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (h : CallContext v initial bytes state)
    {n : Nat} (hn : n ≤ 7) : StateAt (initial.regValue .rsi) state (pushedState initial n) := by
  apply h.state.of_bytes_eq
  intro i hi
  apply (pushedState_agrees initial hn).byte
  intro c hc hcover
  simp only [pushChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcover.elim
  · exact hcover.elim
  · obtain ⟨j, hj, he⟩ := hcover
    exact h.stateStack i hi j (by omega) he

theorem pushedState_rdi (initial : RamState) (n : Nat) :
    (pushedState initial n).regValue .rdi = initial.regValue .rdi :=
  pushedState_register initial n 7 (by decide)

theorem pushedState_rsi (initial : RamState) (n : Nat) :
    (pushedState initial n).regValue .rsi = initial.regValue .rsi :=
  pushedState_register initial n 6 (by decide)

theorem pushedState_rdx (initial : RamState) (n : Nat) :
    (pushedState initial n).regValue .rdx = initial.regValue .rdx :=
  pushedState_register initial n 2 (by decide)

theorem entry_advance [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (h : CallContext v initial bytes state)
    {boundary : ReturnBoundary} (hb : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 10 initial t ∧ BodyInvariant initial t ∧
      t.RIP = partialAddress v ∧ t.regValue .r15 = initial.regValue .rsi ∧
      t.regValue .rbx = initial.regValue .rdx ∧ t.regValue .rcx = initial.regValue .rcx ∧
      t.regValue .rax = BitVec.ofNat 64 state.cursor ∧
      t.regValue .rdi = initial.regValue .rdi ∧ StateAt (initial.regValue .rsi) state t := by
  let start := pushedState initial 7
  have ha := pushedState_agrees initial (by decide : 7 ≤ 7)
  have hip : start.RIP = v.updateAddress + 11#64 := pushedState_rip h (by decide : 7 ≤ 7)
  have hread : MemReadable start (start.regValue .rdi) 1 := by
    rw [show start.regValue .rdi = initial.regValue .rdi from pushedState_rdi initial 7, h.cursorPointer]
    have hm := readable_slice h.stateRead 200 1 (by decide)
    exact ⟨hm.low, fun i hi ↦ ha.grow _ (hm.mem i hi)⟩
  obtain ⟨t, hrun, hready, hcode, ht, hinput, hlanes, hrax, hsetup⟩ :=
    setup_advance v hb (pushedState_ready h (by decide : 7 ≤ 7))
      (pushedState_code h (by decide : 7 ≤ 7)) hip hread
  have hex := hsetup.external setupChanges_noMem
  have hstate := pushedState_state h (by decide : 7 ≤ 7)
  have hstate' : StateAt (initial.regValue .rsi) state t := hstate.of_bytes_eq (by
    intro i hi
    rw [hex])
  have hframe := ha.memoryWriteFrame (pushChanges_writesWithin h.stack)
  have hframe' : MemoryWriteFrame start t (writeRegions initial) := by
    intro address hout
    rw [hex]
  have hsaved : SavedFrame initial t := by
    have hs := pushedState_savedFrame h.stack
    exact hs.of_memory_eq (by intro i j hj; rw [hex]) (by intro j hj; rw [hex])
  refine ⟨t, (pushedState_advances h hb (by decide : 7 ≤ 7)).trans hrun,
    ⟨hready, ?_, ?_, hsaved, memoryWriteFrame_trans hframe hframe',
      fun a hm ↦ hsetup.grow a (ha.grow a hm), (hsetup.scalarFrame_eq (by rfl)).trans (ha.scalarFrame_eq (by rfl))⟩,
    ht, ?_, ?_, ?_, ?_, ?_, hstate'⟩
  · intro a b hab
    exact (hcode (a, b) hab).2
  · exact (hsetup.read (n := 64) (r := 4) (by decide +kernel)).trans (pushedState_rsp initial 7)
  · exact hlanes.trans (pushedState_rsi initial 7)
  · exact hinput.trans (pushedState_rdx initial 7)
  · exact (hsetup.read (n := 64) (r := 1) (by decide +kernel)).trans
      (pushedState_register initial 7 1 (by decide))
  · rw [show start.regValue .rdi = initial.regValue .rdi from pushedState_rdi initial 7, h.cursorPointer] at hrax
    rw [hrax]
    have hc := hstate.cursor
    unfold Update.cursor at hc
    rw [← hc]
    exact (BitVec.ofNat_toNat 64 _).symm
  · exact (hsetup.read (n := 64) (r := 7) (by decide +kernel)).trans
      (pushedState_rdi initial 7)

end Sha3.Proofs.Update
