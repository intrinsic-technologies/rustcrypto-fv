import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Result

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

section CallResultContractValues

variable (P : Lifted) (code : CodeMap) (label : P.Label) (m : FrameInfo)
  (footprint : Activation → List MemoryRegion) (pre : Activation → Ram → Prop)
  (post : Activation → Output Value Ram Reg.count → Prop)

theorem callResultContract_exec_values
    (hcontract : CallResultContract P code label m footprint pre post)
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
      post (activationOfValues mem args ret low) output := by
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

end CallResultContractValues

end AesGcm.Proofs.Machine.Runtime
