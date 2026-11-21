import AesGcm.Proofs.Machine.Runtime.Contracts

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine

theorem atoms_append (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (left right : List Atom) :
    Atom.All code args mem (left ++ right) ↔
      Atom.All code args mem left ∧ Atom.All code args mem right := by
  induction left with
  | nil => simp only [List.nil_append, Atom.All, true_and]
  | cons atom left ih => simp only [List.cons_append, Atom.All, ih, and_assoc]

theorem frame_entryAtoms (m : FrameInfo) (fr : Activation) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hregs : ∀ r : Fin Reg.count, r.val ∈ Activation.entryNumbers →
      args[r] = ⟨64, fr.entryReg r.val⟩)
    (h39 : args[39] = ⟨32, fr.mxcsr⟩)
    (h50 : args[50] = ⟨16, fr.ftw⟩)
    (h51 : args[51] = ⟨16, fr.fcw⟩)
    (hdf : args[22] = ⟨1, 0⟩)
    (hread : Readable mem fr.rsp 8)
    (hret : memLoad mem fr.rsp 64 = fr.ret)
    (hretLow : fr.ret.toNat < 2 ^ 32)
    (hwindow : 0 < m.window →
      Writable code mem (fr.rsp - BitVec.ofNat 64 m.window) m.window)
    (hroom : fr.low.toNat + m.window ≤ fr.rsp.toNat)
    (halign : fr.rsp.toNat % 16 = 8)
    (hslots : Atom.All code args mem (m.callSlotAtoms m.callSlots fr)) :
    Atom.All code args mem (m.entryAtoms fr) := by
  have hstack : Atom.All code args mem (m.stackAtoms fr) := by
    unfold FrameInfo.stackAtoms
    rw [atoms_append, atoms_append]
    refine ⟨⟨⟨hread, hret, hretLow, trivial⟩, ?_⟩, halign, trivial⟩
    split
    · rename_i hw
      refine ⟨?_, trivial⟩
      change fr.low.toNat ≤ fr.rsp.toNat
      simpa only [hw, Nat.add_zero] using hroom
    · rename_i hw
      exact ⟨hwindow (by omega), hroom, trivial⟩
  unfold FrameInfo.entryAtoms FrameInfo.frameAtoms FrameInfo.entryFrame
  rw [atoms_append, atoms_append, atoms_append]
  refine ⟨⟨⟨⟨hregs 4 (by decide), hdf, ?_⟩, trivial⟩, hstack⟩, hslots⟩
  simp only [FrameInfo.entryRegs, List.map_cons, List.map_nil, Atom.All, Atom.Holds]
  exact ⟨hregs 1 (by decide), hregs 2 (by decide), hregs 3 (by decide),
    hregs 5 (by decide), hregs 6 (by decide), hregs 7 (by decide), hregs 8 (by decide),
    hregs 9 (by decide), hregs 12 (by decide), hregs 13 (by decide), hregs 14 (by decide),
    hregs 15 (by decide), h39, h50, h51, trivial⟩

def activationOfValues (mem : Ram) (args : Values Value Reg.count)
    (ret low : BitVec 64) : Activation where
  original := mem
  rsp := args[4].get 64
  ret := ret
  low := low
  rbx := args[3].get 64
  rbp := args[5].get 64
  r12 := args[12].get 64
  r13 := args[13].get 64
  r14 := args[14].get 64
  r15 := args[15].get 64
  rdi := args[7].get 64
  rsi := args[6].get 64
  rdx := args[2].get 64
  rcx := args[1].get 64
  r8 := args[8].get 64
  r9 := args[9].get 64
  mxcsr := args[39].get 32
  ftw := args[50].get 16
  fcw := args[51].get 16
  fs := default

section CallContractValues

variable (P : Lifted) (code : CodeMap) (label : P.Label) (m : FrameInfo)
  (footprint : Activation → List MemoryRegion) (pre post : Activation → Ram → Prop)

theorem callContract_exec_values
    (hcontract : CallContract P code label m footprint pre post)
    (mem : Ram) (args : Values Value Reg.count) (ret low : BitVec 64)
    (hTypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hDF : args[22] = ⟨1, 0⟩)
    (hRead : Readable mem (args[4].get 64) 8)
    (hRet : memLoad mem (args[4].get 64) 64 = ret)
    (hRetLow : ret.toNat < 2 ^ 32)
    (hWindow : 0 < m.window →
      Writable code mem (args[4].get 64 - BitVec.ofNat 64 m.window) m.window)
    (hRoom : low.toNat + m.window ≤ (args[4].get 64).toNat)
    (hAlign : (args[4].get 64).toNat % 16 = 8)
    (hSlots : Atom.All code args mem
      (m.callSlotAtoms m.callSlots (activationOfValues mem args ret low)))
    (hPre : pre (activationOfValues mem args ret low) mem) :
    ∃ output : Output Value Ram Reg.count,
      P.program.Exec (dialect code) ⟨⟨label, args, mem⟩, []⟩ output ∧
      output.tag = some ⟨64, ret⟩ ∧
      Atom.All code output.values output.store
        (m.doneAtoms (activationOfValues mem args ret low)) ∧
      GPRsTyped output.values ∧
      RamWriteFrame mem output.store
        ((activationOfValues mem args ret low).region ::
          footprint (activationOfValues mem args ret low)) ∧
      post (activationOfValues mem args ret low) output.store := by
  let fr := activationOfValues mem args ret low
  have hEntry : Atom.All code args mem (m.entryAtoms fr) := by
    apply frame_entryAtoms m fr code args mem
    · rintro ⟨r, hr⟩ hin
      simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hin
      have hr16 : r < 16 := by omega
      have hv := hTypes.value ⟨r, hr16⟩
      refine hv.trans ?_
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      all_goals rfl
    · exact h39
    · exact h50
    · exact h51
    · exact hDF
    · exact hRead
    · exact hRet
    · exact hRetLow
    · exact hWindow
    · exact hRoom
    · exact hAlign
    · exact hSlots
  exact hcontract fr ⟨label, args, mem⟩ rfl rfl hEntry hTypes hPre

end CallContractValues

end AesGcm.Proofs.Machine.Runtime
