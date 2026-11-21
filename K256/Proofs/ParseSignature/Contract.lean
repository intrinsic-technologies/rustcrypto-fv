import K256.Proofs.Common.ScalarWords
import K256.Proofs.LIR.Program
import K256.Proofs.Common.Refine.Frame

namespace K256.Proofs.ParseSignature

open K256.Spec K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

def buffer (base : BitVec 64) (size : Nat) : MemoryRegion := ⟨base.toNat, size⟩

def callStack (fr : Activation) : MemoryRegion :=
  ⟨fr.low.toNat, fr.rsp.toNat + 8 - fr.low.toNat⟩

def ArgumentWidths (args : Values Value Reg.count) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ Activation.argumentNumbers → args[i].width = 64

def withArguments (fr : Activation) (args : Values Value Reg.count) : Activation :=
  { fr with
    rdi := args[7].get 64
    rsi := args[6].get 64
    rdx := args[2].get 64
    rcx := args[1].get 64
    r8 := args[8].get 64
    r9 := args[9].get 64 }

theorem entryArgument {args : Values Value Reg.count} (widths : ArgumentWidths args)
    (fr : Activation) (i : Fin Reg.count) (hi : i.val ∈ Activation.argumentNumbers) :
    args[i] = (withArguments fr args).entryValue i := by
  have eq64 (v : Value) (h : v.width = 64) : v = ⟨64, v.get 64⟩ := by
    obtain ⟨w, b⟩ := v
    change w = 64 at h
    subst w
    rfl
  have hwidth := widths i hi
  obtain ⟨i, bound⟩ := i
  simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact eq64 _ hwidth

def Call (code : CodeMap) (entry : LIR.Label) (frame : FrameInfo)
    (fr : Activation) (footprint : List MemoryRegion)
    (post : Output Value Ram Reg.count → Prop) : Prop :=
  ∀ args : Values Value Reg.count,
    Atom.All code args fr.original (frame.entryAtoms fr) →
    ∃ out, LIR.program.Exec (dialect code) ⟨⟨entry, args, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (frame.doneAtoms fr) ∧
      RamWriteFrame fr.original out.store (fr.region :: footprint) ∧ ArgumentWidths out.values ∧ post out

def scalarValue (m : Ram) (base : BitVec 64) : Nat :=
  let w := scalarWord m base
  ((w 3).toNat * 2^64 + (w 2).toNat) * 2^128 + (w 1).toNat * 2^64 + (w 0).toNat

def scalarLimbsAt (m : Ram) (dest : BitVec 64) (original : Ram) (src : BitVec 64) : Prop :=
  ∀ i < 4, memLoad m (wordAddr dest 64 i) 64 = scalarWord original src i

end K256.Proofs.ParseSignature
