import K256.Proofs.Signing.UpdateV.Finalize.Padding.Compress.Memory
import K256.Proofs.Signing.UpdateV.Finalize.Padding.State
import K256.Proofs.Verify.LIR.Fn107a50

namespace K256.Proofs.Signing.UpdateV.Finalize.Compress

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash

def returnAddress (outer : Bool) : Word := if outer then 0x107f2b else 0x107c66

def resumeFrame (outer : Bool) : StackFrame Value Label signature Reg.count :=
  ⟨padEnd outer, #v[], rfl, some ⟨64,returnAddress outer⟩⟩

def callMemory (outer : Bool) (m : Ram) (sp : Word) (msg : ByteArray) : Ram :=
  let length := bswapSpec (BitVec.ofNat 64 (8 * msg.size))
  stage (memStore m (sp + 64) length) sp length (returnAddress outer)

set_option maxHeartbeats 900000 in
theorem prepareCall (outer : Bool) {a : Registers} {m : Ram} {sp : Word} {msg : ByteArray}
    (h : Marked outer a m sp msg) (stack : Writable Extracted.programImage m (sp - 8) 184) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨compressStart outer,a,m⟩ =
        .call ⟨.l1218e0,b,callMemory outer m sp msg⟩ (resumeFrame outer) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 72 ∧ b[6].get 64 = sp + 112 ∧
      b[2].get 64 = 1 ∧ (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → b[i].width = 64) ∧
      ∀ i : Fin Reg.count, i.val ∈ savedRegs → b[i] = a[i] := by
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) h.rsp
  cases outer
  case' false => refine ⟨?_, ?innerStep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case' true => refine ⟨?_, ?outerStep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case innerStep =>
    have hp : a[15].get 64 = sp+72 := congrArg (Value.get 64) h.hashPtr
    have hc : a[5].get 64 = BitVec.ofNat 64 (msg.size / 64) := congrArg (Value.get 64) h.count
    have hu : a[13].get 64 = BitVec.ofNat 64 (msg.size % 64) := congrArg (Value.get 64) h.used
    change program.runBlock (dialect Extracted.programImage) ⟨.l107be4,a,m⟩ = _
    cfg_eval [rsp,hp,hc,hu]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l107be4)
    simp (disch := store_disch) only [callMemory,stage,memLoad_memStore_of_rangeApart,length_word msg.size] <;> rfl
  case outerStep =>
    have hp : a[14].get 64 = sp+72 := congrArg (Value.get 64) h.hashPtr
    have hc : a[13].get 64 = BitVec.ofNat 64 (msg.size / 64) := congrArg (Value.get 64) h.count
    have hu : a[12].get 64 = BitVec.ofNat 64 (msg.size % 64) := congrArg (Value.get 64) h.used
    change program.runBlock (dialect Extracted.programImage) ⟨.l107ea9,a,m⟩ = _
    cfg_eval [rsp,hp,hc,hu]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l107ea9)
    simp (disch := store_disch) only [callMemory,stage,memLoad_memStore_of_rangeApart,length_word msg.size] <;> rfl
  all_goals try rfl
  all_goals
    intro ⟨i,_⟩ hi
    simp only [savedRegs,List.mem_cons,List.not_mem_nil,or_false] at hi
    first
    | (rcases hi with rfl | rfl | rfl | rfl | rfl | rfl)
    | (rcases hi with rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | rfl
      | exact h.widths 3 (by decide)
      | exact h.widths 5 (by decide)
      | exact h.widths 12 (by decide)
      | exact h.widths 14 (by decide)
      | exact h.widths 15 (by decide)

end K256.Proofs.Signing.UpdateV.Finalize.Compress
