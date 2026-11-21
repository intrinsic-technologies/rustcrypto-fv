import K256.Proofs.Signing.Composition.Attempt.Memory
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Frame
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)
open Generate.Generator.Sample (nonzeroPreserved preservedValue sampleChildEntry)

def activation (s : RamState) (m : Ram) (a : Registers) (depth : Nat) (ret : BitVec 64) : Activation where
  original := m
  rsp := sp s - 8
  low := sp s - 8 - BitVec.ofNat 64 depth
  ret := ret
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

theorem value_eq {v : Value} {w : Nat} (width : v.width = w) : v = ⟨w,v.get w⟩ := by
  obtain ⟨width',bits⟩ := v
  cases width
  simp [Value.get]

theorem childAtoms {s : RamState} {secret msg : ByteArray} {a : Registers} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (memory : Memory s m)
    (info : FrameInfo) (slots : info.callSlots = []) (positive : 0 < info.window)
    (room : info.window ≤ 9896) (rsp : a[4] = ⟨64,sp s-8⟩) (df : a[22] = ⟨1,0⟩)
    (gp : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64)
    (fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16)
    (args : ParseSignature.ArgumentWidths a) {ret : BitVec 64} (tag : memLoad m (sp s-8) 64 = ret)
    (small : ret.toNat < 2^32) :
    Atom.All Extracted.programImage a m (info.entryAtoms (activation s m a info.window ret)) := by
  obtain ⟨roomTotal,_,_⟩ := stackBounds call
  have aligned : (stackPtr s).toNat % 16 = 8 := call.stackAvailable.2.2.2
  have top : sp s-8 = stackPtr s - 1296 := by unfold sp; bv_omega
  have topNat : (stackPtr s - (1296 : BitVec 64)).toNat = (stackPtr s).toNat - 1296 :=
    Common.stackOffset (off := 1296) call.stackAvailable (by decide)
  have fit : 1296 + info.window ≤ signingKeyTrySign.minStackBytes := by
    change 1296 + info.window ≤ 11192
    omega
  have low : sp s-8-BitVec.ofNat 64 info.window =
      stackPtr s - BitVec.ofNat 64 (1296 + info.window) := by
    rw [top,BitVec.ofNat_add,BitVec.sub_sub]
    rfl
  have lowNat := Common.stackOffset (off := 1296+info.window) call.stackAvailable fit
  apply sampleChildEntry (base := activation s m a info.window ret)
    info slots positive rsp ?_ args ?_ tag small ?_ ?_ ?_
  · intro ⟨i,hi⟩ member
    simp only [nonzeroPreserved,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact df
      | exact value_eq (gp 3 (by decide))
      | exact value_eq (gp 5 (by decide))
      | exact value_eq (gp 12 (by decide))
      | exact value_eq (gp 13 (by decide))
      | exact value_eq (gp 14 (by decide))
      | exact value_eq (gp 15 (by decide))
      | exact value_eq fp.1
      | exact value_eq fp.2.1
      | exact value_eq fp.2.2
  · change Readable m (sp s-8) 8
    rw [addr_sub]
    exact (stackWindow call memory (by decide)).readable
  · change Writable Extracted.programImage m (sp s-8-BitVec.ofNat 64 info.window) info.window
    rw [low]
    exact (Common.stackWritable call (off := 1296+info.window) fit
      (by omega) positive).of_frame memory.written
  · change (sp s-8-BitVec.ofNat 64 info.window).toNat + info.window ≤ (sp s-8).toNat
    rw [low,top,lowNat,topNat]
    omega
  · change (sp s-8).toNat % 16 = 8
    rw [top,topNat]
    omega

theorem callReaches {site child after : LIR.Label} {a b : Registers} {m n : Ram}
    {ret : BitVec 64} {out : Output Value Ram Reg.count}
    (call : LIR.program.runBlock (dialect Extracted.programImage) ⟨site,a,m⟩ =
      .call ⟨child,b,n⟩ (resume after ret))
    (run : LIR.program.Exec (dialect Extracted.programImage) ⟨⟨child,b,n⟩,[]⟩ out)
    (tag : out.tag = some ⟨64,ret⟩) :
    Reach (core site a m) (core after out.values out.store) := by
  refine .step (b := ⟨⟨child,b,n⟩,[resume after ret,resume .l102795 0x102795]⟩) ?_ ?_
  · change (LIR.program.runBlock (dialect Extracted.programImage) ⟨site,a,m⟩).next
      (dialect Extracted.programImage) [resume .l102795 0x102795] = _
    rw [call]
    rfl
  · exact ParseSignature.exec_reaches_resume run _ _
      (by rw [tag]; exact decide_eq_true (rfl : Value.mk 64 ret = Value.mk 64 ret))

end K256.Proofs.Signing.Composition.Attempt
