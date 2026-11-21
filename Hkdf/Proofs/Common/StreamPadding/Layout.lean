import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Streaming

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program

inductive Variant where
  | key
  | hmac
  | simpleInner
  | simpleOuter
  deriving DecidableEq

inductive Point where
  | entry | mark | fillCall | branch | firstHead | firstWords | firstSetup | firstCall
  | zero | length | lastHead | lastWords | lastSetup | lastCall | exit
  deriving DecidableEq

def Variant.frame : Variant → Nat
  | .key => 376
  | .hmac => 408
  | .simpleInner | .simpleOuter => 328

def Variant.tail : Variant → Nat
  | .key => 64
  | .hmac => 72
  | .simpleInner | .simpleOuter => 72

def Variant.hash (v : Variant) : Nat := v.tail + 64

def Variant.counter (v : Variant) : Nat := v.tail + 96

def Variant.scratch : Variant → Nat
  | .key => 168
  | .hmac => 8
  | .simpleInner | .simpleOuter => 8

def Variant.reserve : Variant → Nat
  | .key => 720
  | .hmac => 1264
  | .simpleInner | .simpleOuter => 672

def Variant.outputBytes : Variant → Nat
  | .key => 64
  | .hmac => 176
  | .simpleInner | .simpleOuter => 0

def Variant.helperEntry : Variant → BitVec 64
  | .key => 0x116320
  | .hmac => 0x10dd90
  | .simpleInner | .simpleOuter => 0x1171f0

def Variant.pc : Variant → Point → BitVec 64
  | .key, .entry => 0x116442
  | .key, .mark => 0x11645f
  | .key, .fillCall => 0x116472
  | .key, .branch => 0x116478
  | .key, .firstHead => 0x116482
  | .key, .firstWords => 0x11648f
  | .key, .firstSetup => 0x1164ea
  | .key, .firstCall => 0x1164fa
  | .key, .zero => 0x1164ff
  | .key, .length => 0x11653e
  | .key, .lastHead => 0x116551
  | .key, .lastWords => 0x116559
  | .key, .lastSetup => 0x1165b4
  | .key, .lastCall => 0x1165c4
  | .key, .exit => 0x1165c9
  | .hmac, .entry => 0x10ddb3
  | .hmac, .mark => 0x10ddd3
  | .hmac, .fillCall => 0x10dde6
  | .hmac, .branch => 0x10ddec
  | .hmac, .firstHead => 0x10ddf6
  | .hmac, .firstWords => 0x10de03
  | .hmac, .firstSetup => 0x10de49
  | .hmac, .firstCall => 0x10de56
  | .hmac, .zero => 0x10de5b
  | .hmac, .length => 0x10de9a
  | .hmac, .lastHead => 0x10deb0
  | .hmac, .lastWords => 0x10deb5
  | .hmac, .lastSetup => 0x10defb
  | .hmac, .lastCall => 0x10df08
  | .hmac, .exit => 0x10df0d
  | .simpleInner, .entry => 0x117297
  | .simpleInner, .mark => 0x1172b7
  | .simpleInner, .fillCall => 0x1172ca
  | .simpleInner, .branch => 0x1172d0
  | .simpleInner, .firstHead => 0x1172da
  | .simpleInner, .firstWords => 0x1172e7
  | .simpleInner, .firstSetup => 0x11732d
  | .simpleInner, .firstCall => 0x11733a
  | .simpleInner, .zero => 0x11733f
  | .simpleInner, .length => 0x11737e
  | .simpleInner, .lastHead => 0x117394
  | .simpleInner, .lastWords => 0x117399
  | .simpleInner, .lastSetup => 0x1173df
  | .simpleInner, .lastCall => 0x1173ec
  | .simpleInner, .exit => 0x1173f1
  | .simpleOuter, .entry => 0x117535
  | .simpleOuter, .mark => 0x117555
  | .simpleOuter, .fillCall => 0x117568
  | .simpleOuter, .branch => 0x11756e
  | .simpleOuter, .firstHead => 0x117578
  | .simpleOuter, .firstWords => 0x117585
  | .simpleOuter, .firstSetup => 0x1175cb
  | .simpleOuter, .firstCall => 0x1175d8
  | .simpleOuter, .zero => 0x1175dd
  | .simpleOuter, .length => 0x11761c
  | .simpleOuter, .lastHead => 0x117632
  | .simpleOuter, .lastWords => 0x117637
  | .simpleOuter, .lastSetup => 0x11767d
  | .simpleOuter, .lastCall => 0x11768a
  | .simpleOuter, .exit => 0x11768f

def regIndex (r : X86.Syntax.Reg) : BitVec 5 := BitVec.ofNat 5 r.fin.val

theorem read_regIndex (s : RamState) (r : X86.Syntax.Reg) (n : Nat) :
    (.reg (regIndex r) : Operand n).read s = (s.regValue r).setWidth n := by
  cases r <;> rfl

theorem reg_agrees {s t : RamState} {components : List Component}
    (agrees : AgreesExcept components s t) (r : X86.Syntax.Reg)
    (kept : Component.reg (regIndex r) ∉ components) : t.regValue r = s.regValue r := by
  simpa only [read_regIndex, BitVec.setWidth_eq] using
    agrees.read (n := 64) (r := regIndex r) kept

def Variant.hashReg : Variant → X86.Syntax.Reg
  | .simpleInner => .r15
  | _ => .r14

def Variant.hashIndex (v : Variant) : BitVec 5 :=
  regIndex v.hashReg

def Variant.lengthReg : Variant → X86.Syntax.Reg
  | .simpleInner => .r13
  | _ => .r12

def Variant.lengthIndex (v : Variant) : BitVec 5 :=
  regIndex v.lengthReg

def Variant.blocksReg : Variant → X86.Syntax.Reg
  | .simpleInner => .rbp
  | _ => .r13

def Variant.blocksIndex (v : Variant) : BitVec 5 :=
  regIndex v.blocksReg

def Variant.remainingReg : Variant → X86.Syntax.Reg
  | .simpleInner => .r12
  | _ => .r15

def Variant.remainingIndex (v : Variant) : BitVec 5 :=
  regIndex v.remainingReg

def Variant.stableReg : Variant → X86.Syntax.Reg
  | .simpleInner => .r14
  | _ => .rbp

def Variant.stableIndex (v : Variant) : BitVec 5 :=
  regIndex v.stableReg

def base (v : Variant) (initial : RamState) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 v.frame

def regions (v : Variant) (initial : RamState) : Vector MemoryRegion 2 :=
  #v[registerRegion initial .rdi v.outputBytes, Stack.region initial v.reserve]

def writes (v : Variant) (pointer : BitVec 64) : Vector MemoryRegion 4 :=
  #v[⟨(pointer - 344).toNat, 344⟩,
    ⟨(pointer + BitVec.ofNat 64 v.tail).toNat, 64⟩,
    ⟨(pointer + BitVec.ofNat 64 v.hash).toNat, 32⟩,
    ⟨(pointer + BitVec.ofNat 64 v.scratch).toNat, 64⟩]

end Hkdf.Proofs.Common.StreamPadding
