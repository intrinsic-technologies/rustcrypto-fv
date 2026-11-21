import K256.Proofs.Generate.Generator.Activation
import K256.Proofs.Generate.LIR.Fn10ee80.Frame
import K256.Proofs.Generate.LIR.Fn10fe50.Frame

namespace K256.Proofs.Generate.Generator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def childActivation (s : RamState) (m : Ram) (a : Vector Value 53) (window : Nat)
    (ret : BitVec 64) : Activation where
  original := m
  rsp := s.regValue .rsp - 688
  ret := ret
  low := s.regValue .rsp - BitVec.ofNat 64 (688 + window)
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
  rsp : a[4] = ⟨64, s.regValue .rsp - 688⟩
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

private theorem childSlotApart {s : RamState} {random : ByteArray}
    (call : ValidCall signingKeyGenerateFromRng s [random]) {window : Nat} (room : 688 + window ≤ 10584) :
    0x203e28 + window ≤ (s.regValue .rsp - 688).toNat ∨ (s.regValue .rsp - 688).toNat ≤ 0x203de0 := by
  let stk := Stack.region s signingKeyGenerateFromRng.minStackBytes
  have hs : stk ∈ writtenRegions signingKeyGenerateFromRng s := by simp [stk, writtenRegions]
  have depth : 10584 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have pos : 0 < stk.size := by change 0 < (s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 10584); omega
  have hr : rodataSection ∈ Extracted.programSections := by simp [Extracted.programSections, rodataSection]
  have apart := apart_of_avoids (call.separation.2 stk hs).1 (lo := 0x203de0) (hi := 0x203e28) (by
    intro a ha hb
    obtain ⟨b, hb⟩ := Fn105f30.callSlots_span hr a ha hb
    exact Or.inl ⟨b, Common.programSections_fetchByte_of_mem hb⟩) pos (by decide) (by decide)
  change (s.regValue .rsp).toNat - 10584 + ((s.regValue .rsp).toNat + 8 -
    ((s.regValue .rsp).toNat - 10584)) ≤ _ ∨ _ ≤ (s.regValue .rsp).toNat - 10584 at apart
  have sp := stackOffset (off := 688) call (by decide)
  change (s.regValue .rsp - 688).toNat = (s.regValue .rsp).toNat - 688 at sp
  omega

theorem childEntryAtoms {s : RamState} {random : ByteArray} {m : Ram} {a : Vector Value 53}
    (call : ValidCall signingKeyGenerateFromRng s [random])
    (frame : RamWriteFrame s.external m [Stack.region s signingKeyGenerateFromRng.minStackBytes])
    (info : FrameInfo) (slots : info.callSlots = [(0x203de0, 0x129770), (0x203e20, 0x100a20)])
    (room : 688 + info.window ≤ 10584) (pos : 0 < info.window) (regs : ChildRegisters s a)
    {ret : BitVec 64} (retLow : ret.toNat < 2^32) (saved : memLoad m (s.regValue .rsp - 688) 64 = ret) :
    Atom.All Extracted.programImage a m (info.entryAtoms (childActivation s m a info.window ret)) := by
  let sp := s.regValue .rsp
  have hr : rodataSection ∈ Extracted.programSections := by simp [Extracted.programSections, rodataSection]
  have loaded := Fn105f30.callSlots_loaded hr (loaded_of_stackFrame call frame)
  obtain ⟨r1, v1⟩ := loaded (0x203de0, 0x129770) (by decide)
  obtain ⟨r2, v2⟩ := loaded (0x203e20, 0x100a20) (by decide)
  have hRead := ((stackWritable (off := 688) (len := 8) call (by decide) (by decide) (by decide)).of_frame frame).readable
  have hWrite := (stackWritable (off := 688 + info.window) (len := info.window) call room (by omega) pos).of_frame frame
  have haddr : sp - 688 - BitVec.ofNat 64 info.window = sp - BitVec.ofNat 64 (688 + info.window) := by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl
  have depth : 10584 ≤ sp.toNat := call.stackAvailable.2.2.1
  have low := stackOffset call room
  have top := stackOffset (off := 688) call (by decide)
  change (sp - BitVec.ofNat 64 (688 + info.window)).toNat = sp.toNat - (688 + info.window) at low
  change (sp - 688).toNat = sp.toNat - 688 at top
  have align : sp.toNat % 16 = 8 := call.stackAvailable.2.2.2
  have bound : (sp - BitVec.ofNat 64 (688 + info.window)).toNat + info.window ≤ (sp - 688).toNat := by omega
  have aligned : (sp - 688).toNat % 16 = 8 := by omega
  have apart := childSlotApart call room
  simp only [FrameInfo.entryAtoms, FrameInfo.frameAtoms, FrameInfo.entryFrame, FrameInfo.entryRegs,
    FrameInfo.stackAtoms, FrameInfo.callSlotAtoms, slots, Activation.below, ↓reduceIte, Nat.ne_of_gt pos,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, Atom.All, Atom.Holds, Activation.entryValue, Activation.entryReg, childActivation]
  refine ⟨regs.rsp, regs.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    value_get _ regs.mxcsr, value_get _ regs.ftw, value_get _ regs.fcw, hRead, saved, retLow,
    ?_, bound, aligned, r1, v1, r2, v2, apart, trivial⟩
  any_goals apply value_get _ (regs.gp _ (by decide))
  rw [haddr]
  exact hWrite

end K256.Proofs.Generate.Generator
