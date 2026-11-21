import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.State
import K256.Proofs.Verify.Core.Lincomb.CopyCall
import K256.Proofs.Generate.Generator.Multiply.Split.Caller.Blocks
import K256.Proofs.Generate.Generator.Multiply.Split.Caller.Operands

namespace K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Multiply.Split.Caller (Site)

def pc : Site → Label
  | .roundFirst => .l10f150
  | .mulFirst => .l10f188
  | .roundSecond => .l10f1a2
  | .mulSecond => .l10f1b9
  | .addSecond => .l10f1d3
  | .mulLambda => .l10f1f0
  | .addFirst => .l10f20a

def afterPc : Site → Label
  | .roundFirst => .l10f188
  | .mulFirst => .l10f1a2
  | .roundSecond => .l10f1b9
  | .mulSecond => .l10f1d3
  | .addSecond => .l10f1f0
  | .mulLambda => .l10f20a
  | .addFirst => .l10f221

def ret : Site → BitVec 64
  | .roundFirst => 0x10f188
  | .mulFirst => 0x10f1a2
  | .roundSecond => 0x10f1b9
  | .mulSecond => 0x10f1d3
  | .addSecond => 0x10f1f0
  | .mulLambda => 0x10f20a
  | .addFirst => 0x10f221

def callee : Site → Label
  | .roundFirst => .l11b8f0
  | .mulFirst => .l1099c0
  | .roundSecond => .l11b8f0
  | .mulSecond => .l1099c0
  | .addSecond => .l1109b0
  | .mulLambda => .l1099c0
  | .addFirst => .l1109b0

def destination : Site → Nat
  | .roundFirst => 0x38
  | .mulFirst => 0x268
  | .roundSecond => 0x38
  | .mulSecond => 0xe0
  | .addSecond => 0xb0
  | .mulLambda => 0x100
  | .addFirst => 0x38

abbrev slot (sp : BitVec 64) (i : Nat) := frameSp sp + BitVec.ofNat 64 i

def left (sp scalar : BitVec 64) : Site → BitVec 64
  | .roundFirst => scalar
  | .mulFirst => slot sp 0x38
  | .roundSecond => scalar
  | .mulSecond => slot sp 0x38
  | .addSecond => slot sp 0x268
  | .mulLambda => slot sp 0xb0
  | .addFirst => scalar

def right (sp : BitVec 64) : Site → BitVec 64
  | .roundFirst => 0x202200
  | .mulFirst => 0x202220
  | .roundSecond => 0x202240
  | .mulSecond => 0x202260
  | .addSecond => slot sp 0xe0
  | .mulLambda => 0x202280
  | .addFirst => slot sp 0x100

def bp (sp : BitVec 64) (a : Registers) : Site → BitVec 64
  | .roundFirst => a[5].get 64
  | .mulFirst => slot sp 0x268
  | .roundSecond => slot sp 0x268
  | .mulSecond => slot sp 0x268
  | .addSecond => slot sp 0x268
  | .mulLambda => slot sp 0x268
  | .addFirst => slot sp 0x268

def r13 (sp : BitVec 64) : Site → BitVec 64
  | .roundFirst => slot sp 0x38
  | .mulFirst => slot sp 0x38
  | .roundSecond => slot sp 0x38
  | .mulSecond => slot sp 0x38
  | .addSecond => slot sp 0xb0
  | .mulLambda => slot sp 0xb0
  | .addFirst => slot sp 0xb0

def r15 (sp : BitVec 64) (a : Registers) : Site → BitVec 64
  | .roundFirst => a[15].get 64
  | .mulFirst => a[15].get 64
  | .roundSecond => a[15].get 64
  | .mulSecond => slot sp 0xe0
  | .addSecond => slot sp 0xe0
  | .mulLambda => slot sp 0x100
  | .addFirst => slot sp 0x100


structure Returned (site : Site) (a : Registers) (m : Ram) (sp src scalar tables digits : BitVec 64)
    (b : Registers) (n : Ram) : Prop extends SplitFrame a m sp src tables digits b n where
  rbpReg : b[5] = ⟨64,bp sp a site⟩
  scalarReg : b[12] = ⟨64,scalar⟩
  r13Reg : b[13] = ⟨64,SplitCalls.r13 sp site⟩
  r15Reg : b[15] = ⟨64,SplitCalls.r15 sp a site⟩

structure ChildRegs (site : Site) (a : Registers) (sp scalar tables : BitVec 64)
    (c : Registers) : Prop where
  rsp : c[4] = ⟨64,frameSp sp - 8⟩
  di : c[7] = ⟨64,slot sp (destination site)⟩
  si : c[6] = ⟨64,left sp scalar site⟩
  dx : c[2] = ⟨64,right sp site⟩
  order : site = .addFirst ∨ site = .addSecond → c[1].get 64 = 0x2021a0
  args : ParseSignature.ArgumentWidths c
  bx : c[3] = ⟨64,tables⟩
  bpReg : c[5] = ⟨64,bp sp a site⟩
  scalarReg : c[12] = ⟨64,scalar⟩
  r13Reg : c[13] = ⟨64,SplitCalls.r13 sp site⟩
  r14Width : c[14].width = 64
  r15Reg : c[15] = ⟨64,SplitCalls.r15 sp a site⟩
  ctrl : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = a[i]

end K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls
