import K256.Proofs.Generate.Generator.Affine.Products.Input
import K256.Proofs.Sec1.Serialize.Choice
import K256.Proofs.Common.SignatureRun

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

def inverseReturn : StackFrame Value Label signature Reg.count :=
  ⟨.l10eda1, #v[], rfl, some ⟨64, 0x10eda1⟩⟩

theorem inverseCall {sp : Word} {a : Registers} {m : Ram}
    (rsp : a[4] = ⟨64, sp⟩) (win : Writable Extracted.programImage m (sp - 8) 136) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10ed84, a, m⟩ =
      .call ⟨.l127d50, b, memStore m (sp - 8) (0x10eda1 : Word)⟩ inverseReturn ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[7] = ⟨64, (memLoad m (sp + 120) 32).setWidth 64⟩ ∧
      b[15] = ⟨64, memLoad m (sp + 88) 64⟩ ∧ b[12] = ⟨64, memLoad m (sp + 96) 64⟩ ∧
      b[13] = ⟨64, memLoad m (sp + 104) 64⟩ ∧ b[5] = ⟨64, memLoad m (sp + 112) 64⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,14,22,39,50,51] → b[i] = a[i] := by
  have push : StoreOk Extracted.programImage m (sp - 8) 8 0x10ed9c 5 :=
    ParseSignature.storeOk_of_codeRange (off := 24)
      (win.of_offsets (addr_sub sp 8) (addr_sub sp 8) (by decide))
      (fun x hx => Common.fnCode_subset_programImage x (code_l10ed84 x hx)) (by decide)
  refine ⟨?b, ?run, ?post⟩
  case run =>
    cfg_eval
    simp only [rsp, Value.get_mk, push]
    repeat' (refine (ite_eq_left ?_).trans ?_
             apply LoadOk.of_offsets win.readable rfl (addr_sub sp 8) (by decide))
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Generate.Generator.Affine
