import Hkdf.Proofs.Common.SHA256.Compression.Execution
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs

structure Values where
  regs : BitVec 5 → BitVec 64
  stack : Nat → BitVec 32

structure ValueContext where
  stackPointer : BitVec 64
  inputPointer : BitVec 64
  inputWords : Nat → BitVec 32

namespace Values

inductive Address where
  | stack (offset : Nat)
  | input (offset : Nat)
  deriving DecidableEq

inductive Source where
  | reg (index : BitVec 5)
  | imm (value : BitVec 32)
  | mem (address : Address)
  deriving DecidableEq

inductive Binary where
  | add | xor | and
  deriving DecidableEq

inductive Op where
  | mov32 (dst : BitVec 5) (src : Source)
  | mov64 (dst : BitVec 5) (src : Source)
  | store32 (offset : Nat) (src : BitVec 5)
  | store64 (offset : Nat) (src : BitVec 5)
  | addStack32 (offset : Nat) (src : BitVec 5)
  | binary32 (operation : Binary) (dst : BitVec 5) (src : Source)
  | not32 (dst : BitVec 5)
  | rol32 (dst : BitVec 5) (count : Nat)
  | shr32 (dst : BitVec 5) (count : Nat)
  | lea32 (dst base : BitVec 5) (index : Option (BitVec 5)) (scale : Nat) (disp : BitVec 64)
  | bswap32 (dst : BitVec 5)
  deriving DecidableEq

def Address.value (context : ValueContext) : Address → BitVec 64
  | .stack off => context.stackPointer + BitVec.ofNat 64 off
  | .input off => context.inputPointer + BitVec.ofNat 64 off

def read32 (context : ValueContext) (state : Values) : Address → BitVec 32
  | .stack off => state.stack off
  | .input off => context.inputWords off

def read64 (context : ValueContext) (state : Values) : Address → BitVec 64
  | .stack off => state.stack (off + 4) ++ state.stack off
  | .input off => context.inputWords (off + 4) ++ context.inputWords off

def Source.read32 (source : Source) (context : ValueContext) (state : Values) : BitVec 32 :=
  match source with
  | .reg r => (state.regs r).setWidth 32
  | .imm value => value
  | .mem address => Values.read32 context state address

def Source.read64 (source : Source) (context : ValueContext) (state : Values) : BitVec 64 :=
  match source with
  | .reg r => state.regs r
  | .imm value => value.setWidth 64
  | .mem address => Values.read64 context state address

def writeReg (state : Values) (dst : BitVec 5) (value : BitVec 64) : Values :=
  { state with regs := fun r => if r = dst then value else state.regs r }

def write32 (state : Values) (offset : Nat) (value : BitVec 32) : Values :=
  { state with stack := fun off => if off = offset then value else state.stack off }

def write64 (state : Values) (offset : Nat) (value : BitVec 64) : Values :=
  (state.write32 offset (value.setWidth 32)).write32 (offset + 4) (value.extractLsb' 32 32)

def Binary.apply (operation : Binary) (x y : BitVec 32) : BitVec 32 :=
  match operation with
  | .add => x + y
  | .xor => x ^^^ y
  | .and => x &&& y

def Op.eval (operation : Op) (context : ValueContext) (state : Values) : Values :=
  match operation with
  | .mov32 dst src => state.writeReg dst ((src.read32 context state).setWidth 64)
  | .mov64 dst src => state.writeReg dst (src.read64 context state)
  | .store32 off src => state.write32 off ((state.regs src).setWidth 32)
  | .store64 off src => state.write64 off (state.regs src)
  | .addStack32 off src => state.write32 off (state.stack off + (state.regs src).setWidth 32)
  | .binary32 operation dst src => state.writeReg dst
      ((operation.apply ((state.regs dst).setWidth 32) (src.read32 context state)).setWidth 64)
  | .not32 dst => state.writeReg dst ((~~~((state.regs dst).setWidth 32)).setWidth 64)
  | .rol32 dst count => state.writeReg dst (((state.regs dst).setWidth 32).rotateLeft count |>.setWidth 64)
  | .shr32 dst count => state.writeReg dst ((((state.regs dst).setWidth 32) >>> count).setWidth 64)
  | .lea32 dst base index scale disp =>
      let indexed := match index with | none => 0 | some r => state.regs r <<< scale
      state.writeReg dst (((state.regs base + indexed + disp).setWidth 32).setWidth 64)
  | .bswap32 dst => state.writeReg dst ((Compression.bswap32 ((state.regs dst).setWidth 32)).setWidth 64)

def run (context : ValueContext) : List Op → Values → Values
  | [], state => state
  | operation :: rest, state => run context rest (operation.eval context state)

def ofRam (s : RamState) : Values :=
  ⟨fun r => (Operand.reg r : Operand 64).read s, fun off => memLoad s.external (stackPtr s + BitVec.ofNat 64 off) 32⟩

def contextOfRam (s : RamState) : ValueContext :=
  ⟨stackPtr s, s.regValue .rsi,
    fun off => memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 off) 32⟩

theorem run_append (context : ValueContext) (left right : List Op) (state : Values) :
    run context (left ++ right) state = run context right (run context left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons operation rest ih => exact ih (operation.eval context state)

end Values
end Hkdf.Proofs.Common.SHA256.Compression
