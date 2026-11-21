import X86Proofs.Program.Compose

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs

structure Value where
  width : Nat
  bits : BitVec width
  deriving DecidableEq

namespace Value

def get (n : Nat) (v : Value) : BitVec n := v.bits.setWidth n

def ofBool (b : Bool) : Value := ⟨1, BitVec.ofBool b⟩

def truth (v : Value) : Bool := v.bits != 0

end Value

inductive Reg where
  | gpr (r : BitVec 5)
  | flag (f : StatusFlag)
  | df
  | xmm (r : BitVec 5)
  | mxcsr
  | fpr (r : BitVec 3)
  | fsw
  | fcc
  | ftw
  | fcw
  | fpuPtr
  deriving DecidableEq

namespace Reg

abbrev count : Nat := 53

def width : Reg → Nat
  | .gpr _ => 64
  | .flag _ => 1
  | .df => 1
  | .xmm _ => 128
  | .mxcsr => 32
  | .fpr _ => 80
  | .fsw => 16
  | .fcc => 4
  | .ftw => 16
  | .fcw => 16
  | .fpuPtr => 171

def read (r : Reg) (s : RamState) : Value :=
  match r with
  | .gpr r => ⟨64, (Operand.reg r : Operand 64).read s⟩
  | .flag f => .ofBool ((StatusFlags.ofRFLAGS s.RFLAGS).get f)
  | .df => ⟨1, (Operand.df : Operand 1).read s⟩
  | .xmm r => ⟨128, (Operand.xmm r : Operand 128).read s⟩
  | .mxcsr => ⟨32, (Operand.mxcsr : Operand 32).read s⟩
  | .fpr r => ⟨80, (Operand.fpr r : Operand 80).read s⟩
  | .fsw => ⟨16, (Operand.fsw : Operand 16).read s⟩
  | .fcc => ⟨4, (Operand.fcc 0xF : Operand 4).read s⟩
  | .ftw => ⟨16, (Operand.ftw : Operand 16).read s⟩
  | .fcw => ⟨16, (Operand.fcw : Operand 16).read s⟩
  | .fpuPtr => ⟨171, (Operand.fpuPtr : Operand 171).read s⟩

def write (r : Reg) (v : Value) (s : RamState) : RamState :=
  match r with
  | .gpr r => (Operand.reg r : Operand 64).write s (v.get 64)
  | .flag f =>
      { s with RFLAGS := ((StatusFlags.ofRFLAGS s.RFLAGS).set f v.truth).store s.RFLAGS }
  | .df => (Operand.df : Operand 1).write s (v.get 1)
  | .xmm r => (Operand.xmm r : Operand 128).write s (v.get 128)
  | .mxcsr => (Operand.mxcsr : Operand 32).write s (v.get 32)
  | .fpr r => (Operand.fpr r : Operand 80).write s (v.get 80)
  | .fsw => (Operand.fsw : Operand 16).write s (v.get 16)
  | .fcc => (Operand.fcc 0xF : Operand 4).write s (v.get 4)
  | .ftw => (Operand.ftw : Operand 16).write s (v.get 16)
  | .fcw => (Operand.fcw : Operand 16).write s (v.get 16)
  | .fpuPtr => (Operand.fpuPtr : Operand 171).write s (v.get 171)

def index : Reg → Nat
  | .gpr r => r.toNat
  | .flag f => 16 + f.index
  | .df => 22
  | .xmm r => 23 + r.toNat
  | .mxcsr => 39
  | .fpr r => 40 + r.toNat
  | .fsw => 48
  | .fcc => 49
  | .ftw => 50
  | .fcw => 51
  | .fpuPtr => 52

def ofIndex (i : Nat) : Reg :=
  if i < 16 then .gpr (BitVec.ofNat 5 i)
  else if i < 22 then .flag (StatusFlag.ofIndex (i - 16))
  else if i = 22 then .df
  else if i < 39 then .xmm (BitVec.ofNat 5 (i - 23))
  else if i = 39 then .mxcsr
  else if i < 48 then .fpr (BitVec.ofNat 3 (i - 40))
  else if i = 48 then .fsw
  else if i = 49 then .fcc
  else if i = 50 then .ftw
  else if i = 51 then .fcw
  else .fpuPtr

def isTracked : Reg → Bool
  | .gpr r => r.toNat.blt 16
  | .xmm r => r.toNat.blt 16
  | _ => true

def component : Reg → Component
  | .gpr r => .reg r
  | .flag _ => .flags
  | .df => .df
  | .xmm r => .xmm r
  | .mxcsr => .mxcsr
  | .fpr r => .fpr r
  | .fsw => .fsw
  | .fcc => .fcc
  | .ftw => .ftw
  | .fcw => .fcw
  | .fpuPtr => .fpuPtr

def positions : Component → List Nat
  | .reg r => [r.toNat]
  | .flags => [16, 17, 18, 19, 20, 21]
  | .df => [22]
  | .xmm r => [23 + r.toNat]
  | .mxcsr => [39]
  | .fpr r => [40 + r.toNat]
  | .fsw => [48]
  | .fcc => [49]
  | .ftw => [50]
  | .fcw => [51]
  | .fpuPtr => [52]
  | .rip | .mem _ _ => []

def isFlag : Reg → Bool
  | .flag _ => true
  | _ => false

def flags : List Reg := [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]

def FlagsClosed (rs : List Reg) : Prop := rs.any isFlag = true → ∀ r ∈ flags, r ∈ rs

instance (rs : List Reg) : Decidable (FlagsClosed rs) := inferInstanceAs (Decidable (_ → _))

end Reg

def addrRegs : AddrMode → List Reg
  | .base b _ => [.gpr (b.setWidth 5)]
  | .sib b none _ _ => [.gpr (b.setWidth 5)]
  | .sib b (some i) _ _ => [.gpr (b.setWidth 5), .gpr (i.setWidth 5)]
  | .rip _ => []
  | .abs none _ _ => []
  | .abs (some i) _ _ => [.gpr (i.setWidth 5)]

def addrRegsIn (am : AddrMode) (R : List Reg) : Bool :=
  (addrRegs am).all fun r => R.any fun r' => r'.isTracked && r'.index.beq r.index

def stateOf (p : BitVec 64) (entries : List (Reg × Value)) (mem : Ram) : RamState :=
  entries.foldr (fun e t => e.1.write e.2 t) { (default : RamState) with RIP := p, external := mem }

def Reg.ofWrite? (w : Write) : Option (Reg × Value) :=
  match w with
  | ⟨.reg r, v⟩ => some (.gpr r, ⟨64, v.setWidth 64⟩)
  | ⟨.xmm r, v⟩ => some (.xmm r, ⟨128, v.setWidth 128⟩)
  | ⟨.df, v⟩ => some (.df, ⟨1, v.setWidth 1⟩)
  | ⟨.mxcsr, v⟩ => some (.mxcsr, ⟨32, v.setWidth 32⟩)
  | ⟨.fpr r, v⟩ => some (.fpr r, ⟨80, v.setWidth 80⟩)
  | ⟨.fsw, v⟩ => some (.fsw, ⟨16, fswRest (v.setWidth 16)⟩)
  | ⟨.ftw, v⟩ => some (.ftw, ⟨16, v.setWidth 16⟩)
  | ⟨.fcw, v⟩ => some (.fcw, ⟨16, v.setWidth 16⟩)
  | ⟨.fpuPtr, v⟩ => some (.fpuPtr, ⟨171, v.setWidth 171⟩)
  | _ => none

def writtenValue (r : Reg) (writes : List Write) : Value :=
  (writes.findSome? fun w => match Reg.ofWrite? w with
    | some (r', v) => if r' = r then some v else none
    | none => none).getD ⟨r.width, 0⟩

inductive EffectPart where
  | reg (r : Reg)
  | flag (f : StatusFlag)
  | target
  deriving DecidableEq

def EffectPart.value (o : EffectPart) (e : Effect) (t : RamState) : Value :=
  match o with
  | .reg r => writtenValue r e.writes
  | .flag f => .ofBool ((e.flag t f).getD false)
  | .target => ⟨64, e.rip⟩

def Reg.nonFlags (reads : List Reg) : List Reg := reads.filter fun r => !r.isFlag

def Reg.operands (reads : List Reg) (F : List StatusFlag) : List Reg :=
  Reg.nonFlags reads ++ F.map Reg.flag

def EffectPart.reads (o : EffectPart) (reads : List Reg) (F : List StatusFlag) : List Reg :=
  match o with
  | .flag f =>
    if reads.any Reg.isFlag then Reg.operands reads F ++ [.flag f] else Reg.operands reads F
  | _ => Reg.operands reads F

def EffectPart.isFlag : EffectPart → Bool
  | .flag _ => true
  | _ => false

end P256.Proofs.Lift
