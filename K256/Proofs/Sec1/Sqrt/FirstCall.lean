import K256.Proofs.Common.Field.Multiply.Words
import K256.Proofs.Common.Refine.Layout
import K256.Proofs.Sec1.LIR.Program

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open K256.Proofs.Sec1.LIR (lifted)

def savedLimbs (m : Ram) (sp : Word) (v : Limbs) (p q r s t : Word) : Prop :=
  memLoad m (sp + p) 64 = v[0] ∧ memLoad m (sp + q) 64 = v[1] ∧
  memLoad m (sp + r) 64 = v[2] ∧ memLoad m (sp + s) 64 = v[3] ∧ memLoad m (sp + t) 64 = v[4]

def firstFrame (sp : Word) : MemoryRegion := ⟨(sp - 8).toNat, 368⟩

def squareArguments (next : lifted.Location) (h : next.label = .l1145f0) : Values Value Reg.count :=
  next.arguments.cast (by rw [h])

structure FirstCall (m : Ram) (args : Values Value Reg.count) (sp : Word) (a b : Limbs)
    (next : lifted.Location) (frame : lifted.StackFrame) : Prop where
  callee : next.label = .l1145f0
  updatedWidths : (squareArguments next callee)[1].width = 64 ∧
    (squareArguments next callee)[2].width = 64 ∧
    (squareArguments next callee)[3].width = 64 ∧
    (squareArguments next callee)[5].width = 64 ∧
    (squareArguments next callee)[8].width = 64 ∧
    (squareArguments next callee)[9].width = 64 ∧
    (squareArguments next callee)[12].width = 64 ∧
    (squareArguments next callee)[13].width = 64 ∧
    (squareArguments next callee)[14].width = 64 ∧
    (squareArguments next callee)[15].width = 64
  continuation : frame = ⟨.l115e4d, #v[], rfl, some ⟨64, 0x115e4d⟩⟩
  rsp : (squareArguments next callee)[4] = ⟨64, sp - 8⟩
  rsi : (squareArguments next callee)[6] = ⟨64, sp⟩
  rdi : (squareArguments next callee)[7] = ⟨64, sp + 40⟩
  saved : (squareArguments next callee)[22] = args[22] ∧
    (squareArguments next callee)[39] = args[39] ∧
    (squareArguments next callee)[50] = args[50] ∧
    (squareArguments next callee)[51] = args[51]
  returnSlot : memLoad next.store (sp - 8) 64 = 0x115e4d
  words : WordsAt next.store sp 64 (mulWords a b)
  inputSaved : savedLimbs next.store sp a 352 328 304 336 320
  outputSaved : savedLimbs next.store sp (mulWords a b) 240 288 312 256 248
  rbp : (squareArguments next callee)[5].get 64 = (mulWords a b)[0]
  r13 : (squareArguments next callee)[13].get 64 = (mulWords a b)[3]
  r12 : (squareArguments next callee)[12].get 64 = (mulWords a b)[4]
  writes : RamWriteFrame m next.store [firstFrame sp]

end K256.Proofs.Sec1.Sqrt
