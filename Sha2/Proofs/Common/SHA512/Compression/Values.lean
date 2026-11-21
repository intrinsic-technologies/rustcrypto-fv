import Sha2.Proofs.Common.SHA512.Compression.Execution
import Sha2.Proofs.Common.Instructions.Bswap

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression

open X86 X86.Machine X86.UserProcess X86Proofs

structure Values where
  regs : BitVec 5 → BitVec 64
  stack : Nat → BitVec 64

structure ValueContext where
  stackPointer : BitVec 64
  inputPointer : BitVec 64
  constantPointer : BitVec 64
  inputWords : Nat → BitVec 64
  constants : Nat → BitVec 64

namespace Values

inductive Address where
  | stack (offset : Nat)
  | input (offset : Nat)
  | constant (offset : Nat)
  deriving DecidableEq

inductive Source where
  | reg (index : BitVec 5)
  | imm (value : BitVec 64)
  | mem (address : Address)
  deriving DecidableEq

inductive Binary where
  | add | xor | and
  deriving DecidableEq

inductive Op where
  | mov64 (dst : BitVec 5) (src : Source)
  | store64 (offset : Nat) (src : BitVec 5)
  | addStack64 (offset : Nat) (src : BitVec 5)
  | xorStack64 (offset : Nat) (src : BitVec 5)
  | binary64 (operation : Binary) (dst : BitVec 5) (src : Source)
  | not64 (dst : BitVec 5)
  | rol64 (dst : BitVec 5) (count : Nat)
  | ror64 (dst : BitVec 5) (count : Nat)
  | shr64 (dst : BitVec 5) (count : Nat)
  | lea64 (dst base : BitVec 5) (index : Option (BitVec 5)) (scale : Nat) (disp : BitVec 64)
  | bswap64 (dst : BitVec 5)
  deriving DecidableEq

def Address.value (context : ValueContext) : Address → BitVec 64
  | .stack off => context.stackPointer + BitVec.ofNat 64 off
  | .input off => context.inputPointer + BitVec.ofNat 64 off
  | .constant off => context.constantPointer + BitVec.ofNat 64 off

def read64 (context : ValueContext) (state : Values) : Address → BitVec 64
  | .stack off => state.stack off
  | .input off => context.inputWords off
  | .constant off => context.constants off

def Source.read64 (source : Source) (context : ValueContext) (state : Values) : BitVec 64 :=
  match source with
  | .reg r => state.regs r
  | .imm value => value
  | .mem address => Values.read64 context state address

def writeReg (state : Values) (dst : BitVec 5) (value : BitVec 64) : Values :=
  { state with regs := fun r => if r = dst then value else state.regs r }

def write64 (state : Values) (offset : Nat) (value : BitVec 64) : Values :=
  { state with stack := fun off => if off = offset then value else state.stack off }

def Binary.apply (operation : Binary) (x y : BitVec 64) : BitVec 64 :=
  match operation with
  | .add => x + y
  | .xor => x ^^^ y
  | .and => x &&& y

def Op.eval (operation : Op) (context : ValueContext) (state : Values) : Values :=
  match operation with
  | .mov64 dst src => state.writeReg dst (src.read64 context state)
  | .store64 off src => state.write64 off (state.regs src)
  | .addStack64 off src => state.write64 off (state.stack off + state.regs src)
  | .xorStack64 off src => state.write64 off (state.stack off ^^^ state.regs src)
  | .binary64 operation dst src => state.writeReg dst
      (operation.apply (state.regs dst) (src.read64 context state))
  | .not64 dst => state.writeReg dst (~~~state.regs dst)
  | .rol64 dst count => state.writeReg dst (state.regs dst |>.rotateLeft count)
  | .ror64 dst count => state.writeReg dst (state.regs dst |>.rotateRight count)
  | .shr64 dst count => state.writeReg dst (state.regs dst >>> count)
  | .lea64 dst base index scale disp =>
      let indexed := match index with | none => 0 | some r => state.regs r <<< scale
      state.writeReg dst (state.regs base + indexed + disp)
  | .bswap64 dst => state.writeReg dst (Instructions.bswap64 (state.regs dst))

def run (context : ValueContext) : List Op → Values → Values
  | [], state => state
  | operation :: rest, state => run context rest (operation.eval context state)

def ofRam (s : RamState) : Values :=
  ⟨fun r => (Operand.reg r : Operand 64).read s,
    fun off => memLoad s.external (stackPtr s + BitVec.ofNat 64 off) 64⟩

def contextOfRam (s : RamState) : ValueContext :=
  ⟨stackPtr s, s.regValue .rsi, 0x200000,
    fun off => memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 off) 64,
    fun off => memLoad s.external (0x200000 + BitVec.ofNat 64 off) 64⟩

theorem run_append (context : ValueContext) (left right : List Op) (state : Values) :
    run context (left ++ right) state = run context right (run context left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons operation rest ih => exact ih (operation.eval context state)

end Values
end Sha2.Proofs.Common.SHA512.Compression
