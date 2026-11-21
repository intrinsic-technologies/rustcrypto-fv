import K256.Proofs.Ecdh.Decode.Affine.Entry
import K256.Proofs.Ecdh.Decode.Affine.Frame

import K256.Proofs.Ecdh.Decode.Affine.Selection

namespace K256.Proofs.Ecdh.Decode.Affine

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Sec1.Affine

private theorem identityEntryWidths {args next : Vector Value 53} {m n : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨.l121480,args,m⟩ = .jump ⟨.l1214d0,next,n⟩)
    (r8 : args[8].width = 64) (r9 : args[9].width = 64) : CallerWidths next := by
  cfg_eval [b_l121480] at step
  repeat' (split at step)
  all_goals simp only [Transfer.jump.injEq,Location.mk.injEq,reduceCtorEq] at step
  all_goals
    obtain ⟨_,rfl,rfl⟩ := step
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl <;> first | rfl | exact r8 | exact r9

theorem identityExecution {fr : Activation} {args m bytes} (e : Entry fr args m bytes)
    (zero : bytes.data[0]?.getD 0 = 0) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l121480,args,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ out.values[4] = ⟨64,fr.rsp+8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = args[i]) ∧
      RamWriteFrame m out.store (writes fr) ∧ memLoad out.store (fr.rdi+88) 8 = 1 ∧
      AffinePointAt out.store fr.rdi .infinity ∧ CallerWidths out.values := by
  obtain ⟨next,entry,_,cx,_,atoms,saved,_⟩ := e.start
  rw [zero] at entry cx
  change program.runBlock _ _ = .jump ⟨.l1214d0,next,saveRegisters args m⟩ at entry
  have w := e.output.of_frame saved
  obtain ⟨out,run,tag,done_,_,written,words,flag⟩ := finishIdentity Common.fnCode_subset_programImage
    fr next _ atoms (by rw [cx]; rfl) (e.savedImage saved) w (identityWords_apart w) (.inr e.dstAbove)
  let yes := next.set 19 (.ofBool true)
  have ptr : yes[3].get 64 = fr.rdi := by
    simp only [yes, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
    exact congrArg (Value.get 64) atoms.2.2.1
  have df : yes[22].get 1 = 0 := by
    simp only [yes, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
    exact congrArg (Value.get 1) atoms.2.1
  obtain ⟨endRegs,after,write,_,_,_,keeps⟩ := writeIdentity Common.fnCode_subset_programImage
    yes _ fr.rdi (e.savedImage saved) ptr df w (identityWords_apart w)
  have zeroTest : (next[1].get 64).setWidth 32 = 0 := by rw [cx]; rfl
  have returned := afterJump (afterJump run (dispatchIdentity _ _ zeroTest)) write
  have baseWidths := identityEntryWidths entry e.r8 e.r9
  have widths := (returnState returned).2 (by
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl
    all_goals rw [keeps _ (by simp)]
    all_goals simp only [yes,Fin.getElem_fin,Vector.getElem_set,Nat.reduceEqDiff, ↓reduceIte]
    · exact baseWidths 2 (by decide)
    · exact baseWidths 8 (by decide)
    · exact baseWidths 9 (by decide))
  obtain ⟨sp,kept⟩ := e.returnedRegisters done_
  refine ⟨out, Program.Exec.of_sem ((Sec1.Parser.reaches_jump entry).exec run.sem), tag,sp,kept,
    withOutput (e.afterSaves saved) written,flag,?_,widths⟩
  have word : memLoad out.store (fr.rdi+80) 64 = 1 := words 10 (by decide)
  have byte := extractLsb'_memLoad out.store (fr.rdi+80) (n := 64) 0 8 (by decide) (by decide) (by decide)
  rw [word, BitVec.add_zero] at byte
  exact byte.symm

end K256.Proofs.Ecdh.Decode.Affine
