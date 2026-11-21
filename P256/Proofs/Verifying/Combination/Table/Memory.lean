import P256.Proofs.Verifying.Combination.Table.Frame

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Table

open P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev Slot := Fin 11

def offset (slot : Slot) : Nat := 1088 - 96 * slot.val

theorem offset_bounds (slot : Slot) : 128 ≤ offset slot ∧ offset slot ≤ 1088 := by
  have := slot.isLt
  simp only [offset]
  omega

theorem offset_apart {a b : Slot} (h : a ≠ b) :
    offset a + 96 ≤ offset b ∨ offset b + 96 ≤ offset a := by
  have := a.isLt
  have := b.isLt
  have ne : a.val ≠ b.val := fun he => h (Fin.ext he)
  simp only [offset]
  omega

abbrev Cells := Slot → Option Projective

def writeCell (cells : Cells) (slot : Slot) (value : Projective) : Cells :=
  fun index => if index = slot then some value else cells index

def CellsAt (s t : RamState) (cells : Cells) : Prop :=
  ∀ slot value, cells slot = some value →
    ProjectiveAt t (stackPtr s - BitVec.ofNat 64 (offset slot)) value

structure Memory [Bindings] (s t : RamState) (cursor point : BitVec 64) (cells : Cells) : Prop extends FrameState s t cursor where
  cells : CellsAt s t cells
  cursorValue : memLoad t.external cursor 64 = point + 128

theorem Memory.registers [Bindings] {s t u : RamState} {cursor point : BitVec 64} {cells : Cells} {cs : List Component}
    (state : Memory s t cursor point cells) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (hm : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (hsp : .reg 4 ∉ cs)
    (hbp : .reg 5 ∉ cs) (h13 : .reg 13 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : Memory s u cursor point cells := by
  have ext := agrees.external hm
  refine ⟨state.toFrameState.after_registers ready agrees hm hsp hbp h13, ?_, ?_⟩
  · intro slot value hv
    apply (state.cells slot value hv).of_bytes_eq
    intro i hi
    rw [ext]
  · change memLoad u.external _ 64 = _
    rw [ext]
    exact state.cursorValue

theorem Memory.update [Bindings] {s t u : RamState} {cursor point : BitVec 64} {cells : Cells} {slot : Slot}
    {value : Projective} (state : Memory s t cursor point cells) (frame : FrameState s u cursor)
    (hpoint : ProjectiveAt u (stackPtr s - BitVec.ofNat 64 (offset slot)) value)
    (kept : ∀ off len : Nat, off ≤ 1096 → len ≤ off + 8 →
      (off + 96 ≤ offset slot ∨ offset slot + len ≤ off) →
      ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]?)
    (keptCursor : memLoad u.external cursor 64 = memLoad t.external cursor 64) :
    Memory s u cursor point (writeCell cells slot value) := by
  refine ⟨frame, ?_, ?_⟩
  · intro index val hv
    by_cases he : index = slot
    · subst index
      have hv : value = val := by simpa [writeCell] using hv
      exact hv ▸ hpoint
    · have hv : cells index = some val := by simpa [writeCell, he] using hv
      apply (state.cells index val hv).of_bytes_eq
      intro i hi
      exact kept _ _ (by have := offset_bounds index; omega)
        (by have := offset_bounds index; omega) (offset_apart he) i hi
  · exact keptCursor.trans state.cursorValue

theorem input_byte [Bindings] {s t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {so : BitVec 64} (pre : TablePre s boundary cursor point) (state : FrameState s t cursor so)
    {i : Nat} (hi : i < 96) :
    t.external[point + BitVec.ofNat 64 i]? =
      s.external[point + BitVec.ofNat 64 i]? := by
  have hb : (point).toNat + 96 < 2^32 := pre.pointBounded
  have hin : (pointRegion point).Contains (point + BitVec.ofNat 64 i).toNat := by
    change (point).toNat ≤ _ ∧ _ < (point).toNat + 96
    rw [toNat_add_ofNat _ _ (by omega)]
    constructor <;> omega
  apply state.frame
  intro region hr ha
  have hr' : region = registerRegion s .rdi 768 ∨ region = cursorRegion cursor ∨ region = Stack.region s 2120 := by simpa using hr
  rcases hr' with rfl | rfl | rfl
  · exact pre.pointOutput _ hin ha
  · exact pre.cursorApart _ (by simp) _ ha hin
  · exact pre.pointStack _ hin ha

theorem input_at [Bindings] {s t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {so : BitVec 64} {value : Projective} (pre : TablePre s boundary cursor point)
    (state : FrameState s t cursor so) (input : ProjectiveAt s point value) :
    ProjectiveAt t point value :=
  input.of_bytes_eq (fun _ hi => input_byte pre state hi)

theorem agrees_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {cs : List Component} {destination off len : Nat}
    (pre : TablePre s boundary cursor point) (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, c.Covers a →
      (Component.mem (stackPtr s - BitVec.ofNat 64 destination) 96).Covers a)
    (hd : destination ≤ 1096) (ho : off ≤ 1096) (hl : len ≤ off + 8)
    (apart : off + 96 ≤ destination ∨ destination + len ≤ off) {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
  have hb := P256.Proofs.Program.stack_bounds pre.stack
  have hdn := P256.Proofs.Program.stack_sub_toNat pre.stack (offset := destination) (by omega)
  have hon := P256.Proofs.Program.stack_sub_toNat pre.stack (offset := off) (by omega)
  apply agrees.byte
  intro c hc ha
  obtain ⟨j, hj, he⟩ := memory c hc _ ha
  have hh := congrArg BitVec.toNat he
  rw [toNat_add_ofNat _ _ (by rw [hon]; omega),
    toNat_add_ofNat _ _ (by rw [hdn]; omega), hon, hdn] at hh
  omega

theorem cursor_read_of_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : TablePre s boundary cursor point)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi 768, Stack.region s 2120]) :
    memLoad u.external cursor 64 = memLoad t.external cursor 64 := by
  apply memLoad_congr
  intro i hi
  have hb : cursor.toNat + 8 < 2^32 := pre.cursorBounded
  have hin : (cursorRegion cursor).Contains (cursor + BitVec.ofNat 64 i).toNat := by
    change cursor.toNat ≤ _ ∧ _ < cursor.toNat + 8
    rw [toNat_add_ofNat _ _ (by omega)]
    constructor <;> omega
  change (u.external[cursor + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[cursor + BitVec.ofNat 64 i]?).getD 0
  rw [memory _]
  intro region hr ha
  have hr' : region = registerRegion s .rdi 768 ∨ region = Stack.region s 2120 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.cursorApart _ (by simp) _ hin ha
  · exact pre.cursorApart _ (by simp) _ hin ha


end P256.Proofs.Verifying.Combination.Table
