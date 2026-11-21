import K256.Proofs.Verify.Wrapper.Inputs
import K256.Proofs.Sec1.LIR.Labels

namespace K256.Proofs.Verify.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

def childActivation (s : RamState) (m : Ram) (a : Vector Value 53) (window : Nat)
    (ret : BitVec 64) : Activation where
  original := m
  rsp := s.regValue .rsp - 544
  ret := ret
  low := s.regValue .rsp - BitVec.ofNat 64 (544 + window)
  rcx := a[1].get 64
  rdx := a[2].get 64
  rbx := a[3].get 64
  rbp := a[5].get 64
  rsi := a[6].get 64
  rdi := a[7].get 64
  r8 := a[8].get 64
  r9 := a[9].get 64
  r12 := a[12].get 64
  r13 := a[13].get 64
  r14 := a[14].get 64
  r15 := a[15].get 64
  mxcsr := a[39].get 32
  ftw := a[50].get 16
  fcw := a[51].get 16
  fs := s.FS

structure ChildRegisters (s : RamState) (a : Vector Value 53) : Prop where
  rsp : a[4] = ⟨64, s.regValue .rsp - 544⟩
  df : a[22] = ⟨1, 0⟩
  gp : ∀ r : Fin 53, r.val ∈ [1,2,3,5,6,7,8,9,12,13,14,15] → a[r].width = 64
  mxcsr : a[39].width = 32
  ftw : a[50].width = 16
  fcw : a[51].width = 16

private theorem value_get (v : Value) {width : Nat} (h : v.width = width) :
    v = ⟨width, v.get width⟩ := by
  cases v
  subst width
  simp [Value.get]

theorem childEntry {s : RamState} {key message sig : ByteArray} {m : Ram} {a : Vector Value 53}
    (call : ValidCall verifyingKeyVerify s [key,message,sig]) (state : Memory s m)
    (regs : ChildRegisters s a) (info : FrameInfo) {room : Nat}
    (fits : info.window ≤ room) (depth : 544 + room ≤ 13000) (pos : 0 < info.window)
    (slots : info.CallSlotsIn Sec1.LIR.rodataSection)
    (span : info.CallSlotSpanIn Sec1.LIR.rodataSection)
    {ret : BitVec 64} (small : ret.toNat < 2^32)
    (saved : memLoad m (stackPtr s - 544) 64 = ret) :
    Atom.All Extracted.programImage a m (info.entryAtoms (childActivation s m a room ret)) := by
  let fr := childActivation s m a room ret
  have top := Common.stackOffset (off := 544) call.stackAvailable (by decide)
  change fr.rsp.toNat = (stackPtr s).toNat - 544 at top
  have floor := Common.stackOffset call.stackAvailable depth
  change fr.low.toNat = (stackPtr s).toNat - (544 + room) at floor
  have enough : 13000 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have align : (stackPtr s).toNat % 16 = 8 := call.stackAvailable.2.2.2
  have read := ((Common.stackWritable (off := 544) (len := 8) call (by decide)
    (by decide) (by decide)).of_frame state.frame).readable
  have write := (Common.stackWritable (off := 544 + info.window) (len := info.window)
    call (by change 544 + info.window ≤ 13000; omega) (by omega) pos).of_frame state.frame
  have wr : Writable Extracted.programImage m (fr.rsp - BitVec.ofNat 64 info.window) info.window := by
    change Writable _ m (stackPtr s - 544 - _) _
    rw [BitVec.sub_sub]
    rw [BitVec.ofNat_add] at write
    exact write
  have ro : Sec1.LIR.rodataSection ∈ Extracted.programSections := by
    simp [Sec1.LIR.rodataSection, Extracted.programSections]
  have image := (inputMemory call state.frame).2.2.2
  have loaded := FrameInfo.callSlots_of_section ro slots image
  have spanBytes := FrameInfo.callSlotSpan_of_section ro span
  have slotAtoms : Atom.All Extracted.programImage a m (info.callSlotAtoms info.callSlots fr) := by
    have allReads : ∀ cs : List (BitVec 64 × BitVec 64), (∀ c ∈ cs, c ∈ info.callSlots) →
        Atom.All Extracted.programImage a m
          (cs.flatMap fun c => [.readable c.1 8, .mem c.1 64 c.2]) := by
      intro cs
      induction cs with
      | nil => intro _; trivial
      | cons c cs ih =>
        intro sub
        rw [List.flatMap_cons, Atom.all_append]
        obtain ⟨rd, val⟩ := loaded c (sub _ List.mem_cons_self)
        exact ⟨⟨rd,val,trivial⟩, ih fun x hx => sub x (List.mem_cons_of_mem _ hx)⟩
    unfold FrameInfo.callSlotAtoms
    split
    · trivial
    next c cs eq =>
      rw [Atom.all_append]
      refine ⟨allReads _ (by rw [eq]; exact fun _ h => h), ?_⟩
      have ne : info.callSlots ≠ [] := by rw [eq]; exact List.cons_ne_nil _ _
      have low := FrameInfo.slotsLow_lt_slotsHigh ne
      have high := span.2
      have lim : FrameInfo.slotsHigh info.callSlots ≤ 2^64 :=
        Nat.le_trans high (by decide +kernel)
      have range := apart_of_avoids (call.separation.2 (stack s) (by simp [stack,writtenRegions])).1
        (fun b hb he => by obtain ⟨v,hv⟩ := spanBytes b hb he
                           exact Or.inl ⟨v, Common.programSections_fetchByte_of_mem hv⟩)
        (by change 0 < (stackPtr s).toNat + 8 - ((stackPtr s).toNat - 13000); omega) low lim
      change (stackPtr s).toNat - 13000 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 13000)) ≤ _ ∨
        _ ≤ (stackPtr s).toNat - 13000 at range
      refine ⟨?_, trivial⟩
      change FrameInfo.slotsHigh info.callSlots + info.window ≤ fr.rsp.toNat ∨
        fr.rsp.toNat ≤ FrameInfo.slotsLow info.callSlots
      omega
  change Atom.All _ a m (info.entryAtoms fr)
  simp only [FrameInfo.entryAtoms, FrameInfo.frameAtoms, FrameInfo.entryFrame, FrameInfo.entryRegs,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, Atom.All, Atom.Holds,
    FrameInfo.stackAtoms, Activation.below, Nat.ne_of_gt pos, ↓reduceIte,
    Activation.entryValue, Activation.entryReg]
  refine ⟨regs.rsp, regs.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    value_get _ regs.mxcsr, value_get _ regs.ftw, value_get _ regs.fcw, read, saved, small,
    wr, by omega, by omega, slotAtoms⟩
  all_goals exact value_get _ (regs.gp _ (by decide))

end K256.Proofs.Verify.Wrapper
