import K256.Proofs.Signing.Composition.Attempt.Return.State

namespace K256.Proofs.Signing.Composition.Attempt.Return.Constructor

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

abbrev inside (l : LIR.Label) (a : Registers) (m : Ram) : LIR.lifted.State :=
  ⟨⟨l,a,m⟩,[resume .l105d35 0x105d35, resume .l102795 0x102795]⟩

structure Entry (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (r sigS : Nat)
    (a : Registers) (m : Ram) : Prop extends LoopMemory s d msg st m where
  regs : RegistersAt s (a.set 4 ⟨64,sp s⟩) (sp s+456) (sp s+192) (sp s+192) (sp s+456)
  rsp : a[4] = ⟨64,sp s-8⟩
  dst : a[7] = ⟨64,sp s+8⟩
  first : a[6] = ⟨64,sp s+160⟩
  second : a[2] = ⟨64,sp s+456⟩
  r14 : a[14] = ⟨64,sp s+160⟩
  constructorReturn : memLoad m (sp s-8) 64 = 0x105d35
  rWords : WordsAt m (sp s+160) 64 (scalarWords r)
  sWords : WordsAt m (sp s+456) 64 (scalarWords sigS)

structure Active (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (second : Bool)
    (r sigS : Nat) (a : Registers) (m : Ram) : Prop extends LoopMemory s d msg st m where
  rsp : a[4] = ⟨64,sp s-224⟩
  df : a[22] = ⟨1,0⟩
  bx : a[3] = ⟨64,sp s+8⟩
  bp : a[5] = ⟨64,sp s+192⟩
  r12 : a[12] = ⟨64,sp s+8⟩
  r13 : a[13] = ⟨64,sp s+192⟩
  r14 : a[14] = ⟨64,if second then sp s-64 else sp s+456⟩
  r15 : a[15] = ⟨64,sp s-96⟩
  widths : ParseSignature.ArgumentWidths a
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16
  savedBx : memLoad m (sp s-32) 64 = sp s+456
  constructor14 : memLoad m (sp s-24) 64 = sp s+160
  constructor15 : memLoad m (sp s-16) 64 = sp s+456
  constructorReturn : memLoad m (sp s-8) 64 = 0x105d35
  other : if second then WordsAt m (sp s-160) 64 (scalarWords r)
    else WordsAt m (sp s+456) 64 (scalarWords sigS)

abbrev encoded (s : RamState) (second : Bool) (m : Ram) (x : Nat) :=
  ∀ i (hi : i < 4), Common.scalarWord m (if second then sp s-64 else sp s-96) i = (scalarWords x)[i]

end K256.Proofs.Signing.Composition.Attempt.Return.Constructor
