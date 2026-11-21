import K256.Proofs.Sec1.Wrapper.Stack
import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.Finish
import K256.Proofs.RejectLength.Return
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Sec1.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine Sec1.LIR

structure CallerFrame (initial : RamState) (regions : List MemoryRegion) (args : Vector Value 53)
    (mem : Ram) : Prop where
  rsp : args[4] = ⟨64, initial.regValue .rsp - 248⟩
  dst : args[14] = ⟨64, initial.regValue .rdi⟩
  kept : ∀ i : Fin 53, i.val ∈ [5, 12, 13, 15, 22] → args[i] = (Reg.ofIndex i).read initial
  rbx : memLoad mem (initial.regValue .rsp - 16) 64 = initial.regValue .rbx
  r14 : memLoad mem (initial.regValue .rsp - 8) 64 = initial.regValue .r14
  ret : memLoad mem (initial.regValue .rsp) 64 = (X86Proofs.returnBoundary initial).rip
  writes : RamWriteFrame initial.external mem regions

theorem CallerFrame.of_registers {initial : RamState} {regions : List MemoryRegion}
    {args next : Vector Value 53} {mem : Ram} (h : CallerFrame initial regions args mem)
    (same : ∀ i : Fin 53, i.val ∈ [4,5,12,13,14,15,22] → next[i] = args[i]) :
    CallerFrame initial regions next mem := by
  refine { h with rsp := (same 4 (by decide)).trans h.rsp, dst := (same 14 (by decide)).trans h.dst,
                  kept := ?_ }
  intro i hi
  exact (same i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)).trans
    (h.kept i hi)

theorem finish {initial : RamState} {bytes : ByteArray} {n : Nat} {regions : Vector MemoryRegion n}
    {args : Vector Value 53} {mem : Ram} {status : BitVec 32}
    (call : ValidCall publicKeyFromSec1Bytes initial [bytes]) (h : CallerFrame initial regions.toList args mem)
    (statusEq : (Value.get 64 args[3]).setWidth 32 = status) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l101e62, args, mem⟩, []⟩ out ∧
      Common.Returned initial regions out ∧ out.values[0] = ⟨64, status.setWidth 64⟩ ∧ out.store = mem := by
  let sp := initial.regValue .rsp
  obtain ⟨ret, slot, low, _⟩ := call.returnAddress
  have retVal : (X86Proofs.returnBoundary initial).rip = ret := memLoad_returnSlot slot
  have hlow : (memLoad mem sp 64).toNat < 2 ^ 32 := by rw [h.ret, retVal]; exact low
  have readable (offset : Nat) (depth : offset ≤ 1928) :
      LoadOk mem (sp - BitVec.ofNat 64 offset) 8 := by
    have hr := ((stackWritable (len := 8) call depth (by omega) (by decide)).readable.of_frame h.writes)
    exact ⟨hr.low, hr.present⟩
  have rbx : LoadOk mem (sp - 16) 8 := readable 16 (by decide)
  have r14 : LoadOk mem (sp - 8) 8 := readable 8 (by decide)
  have pop : LoadOk mem sp 8 := by simpa only [BitVec.sub_zero] using readable 0 (by decide)
  have rsp : Value.get 64 args[4] = sp - 248 := by rw [h.rsp]; rfl
  have h16 : sp - 248 + 232 = sp - 16 := by bv_omega
  have h8 : sp - 248 + 240 = sp - 8 := by bv_omega
  have hplus : sp - 248 + 256 = sp + 8 := by bv_omega
  have block : ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l101e62, args, mem⟩ =
      .returned out ∧ Common.Returned initial regions out ∧
        out.values[0] = ⟨64, status.setWidth 64⟩ ∧ out.store = mem := by
    refine ⟨?_, ?eval, ?post⟩
    case eval =>
      cfg_eval
      simp only [rsp, h16, h8, hplus, BitVec.sub_add_cancel, rbx, r14, pop, hlow, and_self,
        ↓reduceIte]
      rfl
    case post =>
      refine ⟨⟨?_, ?_, ?_, ?_, h.writes, rfl⟩, ?_, rfl⟩
      · exact congrArg (fun b => some (⟨64,b⟩ : Value)) h.ret
      · rfl
      · exact (h.kept 22 (by decide)).trans (Reg.read_df_iff.mpr call.directionFlagUnset)
      · intro ⟨i, hi⟩ hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
        · exact congrArg (fun b => (⟨64,b⟩ : Value)) h.rbx
        · exact h.kept 5 (by decide)
        · exact h.kept 12 (by decide)
        · exact h.kept 13 (by decide)
        · exact congrArg (fun b => (⟨64,b⟩ : Value)) h.r14
        · exact h.kept 15 (by decide)
      · subst status
        rfl
  obtain ⟨out, he, post⟩ := block
  exact ⟨out, .done (congrArg (Transfer.next _ []) he), post⟩

end K256.Proofs.Sec1.Wrapper
