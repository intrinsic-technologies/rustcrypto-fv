import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.Wrapper.Stack
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.SignatureRun
import K256.Proofs.RejectLength.Return

namespace K256.Proofs.Sec1.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine Sec1.LIR

def parserMemory (initial : RamState) : Ram :=
  let sp := initial.regValue .rsp
  memStore (memStore (memStore initial.external (sp - 8) (initial.regValue .r14))
    (sp - 16) (initial.regValue .rbx)) (sp - 256) (0x101dea : BitVec 64)

def parserArgs (initial : RamState) : Vector Value Reg.count :=
  let sp := initial.regValue .rsp
  let args : Vector Value 53 := (lifted.locationOf .l101dd0 initial).arguments
  ((args.set 4 ⟨64, sp - 256⟩).set 7 ⟨64, sp - 112⟩).set 14 ⟨64, initial.regValue .rdi⟩

def callFrame (target : Label) (rip : BitVec 64) : StackFrame Value Label signature Reg.count :=
  { target, kept := #v[], arity := rfl, guard := some ⟨64, rip⟩ }

private theorem parserCallBlock {code : CodeMap} {a : Vector Value 53} {mem : Ram}
    {sp dst bx old14 : BitVec 64} (rsp : Value.get 64 a[4] = sp)
    (rdi : Value.get 64 a[7] = dst) (rbx : Value.get 64 a[3] = bx)
    (r14 : Value.get 64 a[14] = old14)
    (g₁ : StoreOk code mem (sp - 8) 8 0x101dd0 2)
    (g₂ : StoreOk code (memStore mem (sp - 8) old14) (sp - 16) 8 0x101dd2 1)
    (g₃ : StoreOk code (memStore (memStore mem (sp - 8) old14) (sp - 16) bx)
      (sp - 256) 8 0x101de5 5) :
    program.runBlock (dialect code) ⟨.l101dd0, a, mem⟩ = .call
      ⟨.l106390, ((a.set 4 ⟨64, sp - 256⟩).set 7 ⟨64, sp - 112⟩).set 14 ⟨64, dst⟩,
        memStore (memStore (memStore mem (sp - 8) old14) (sp - 16) bx) (sp - 256)
          (0x101dea : BitVec 64)⟩ (callFrame .l101dea 0x101dea) := by
  cfg_eval
  simp only [rsp, r14, rbx, rdi, g₁, g₂, g₃, ↓reduceIte]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
    fun he => Vector.ext fun i hi => he ⟨i, hi⟩)
  intro j
  finite_cases j <;> simp only [Vector.getElem_set] <;> rfl

theorem entryBlock {initial : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes initial [bytes]) :
    program.runBlock (dialect Extracted.programImage) (lifted.locationOf .l101dd0 initial) =
      .call ⟨.l106390, parserArgs initial, parserMemory initial⟩ (callFrame .l101dea 0x101dea) := by
  let sp := initial.regValue .rsp
  let a : Vector Value 53 := (lifted.locationOf .l101dd0 initial).arguments
  let m₁ := memStore initial.external (sp - 8) (initial.regValue .r14)
  let m₂ := memStore m₁ (sp - 16) (initial.regValue .rbx)
  have inc := fun x hx => Common.fnCode_subset_programImage x (code_l101dd0 x hx)
  have w₁ := stackWritable (offset := 8) (len := 8) call (by decide) (by decide) (by decide)
  have w₂ := (stackWritable (offset := 16) (len := 8) call (by decide) (by decide)
    (by decide)).memStore (sp - 8) (initial.regValue .r14)
  have w₃ := ((stackWritable (offset := 256) (len := 8) call (by decide) (by decide)
    (by decide)).memStore (sp - 8) (initial.regValue .r14)).memStore (sp - 16) (initial.regValue .rbx)
  have g₁ : StoreOk Extracted.programImage initial.external (sp - 8) 8 0x101dd0 2 :=
    ParseSignature.storeOk_of_codeRange (off := 0) w₁ inc (by decide)
  have g₂ : StoreOk Extracted.programImage m₁ (sp - 16) 8 0x101dd2 1 :=
    ParseSignature.storeOk_of_codeRange (off := 2) w₂ inc (by decide)
  have g₃ : StoreOk Extracted.programImage m₂ (sp - 256) 8 0x101de5 5 :=
    ParseSignature.storeOk_of_codeRange (off := 21) w₃ inc (by decide)
  apply parserCallBlock (sp := sp) (a := a) (mem := initial.external)
    (dst := initial.regValue .rdi) (bx := initial.regValue .rbx) (old14 := initial.regValue .r14)
    _ _ _ _ g₁ g₂ g₃
  all_goals simp only [a, Lifted.locationOf, Vector.getElem_ofFn]; rfl

end K256.Proofs.Sec1.Wrapper
