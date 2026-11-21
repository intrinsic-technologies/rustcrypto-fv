import ChaCha20Poly1305.Spec.AEAD
import ChaCha20Poly1305.Spec.Program.Extracted.Symbols
import Prelude

/-!
# The routines of the chacha20poly1305 wrappers

The part of the call contract that needs no program image: the `Routine` record and its constant for
each of the 4 wrappers in `ChaCha20Poly1305/program/src/lib.rs` that have a theorem, which say where
each input, the message's length, the output, the capacity and the heap are passed, how the output's
and the heap's sizes follow the message's length, and whether the crate accepts the inputs; and
`hasRoom`, which decides `encrypt_in_place`'s branch. It imports, of the extraction, only the
wrappers' link-time addresses (`Extracted/Symbols.lean`), so that `ChaCha20Poly1305/Tests.lean` can
test these without the program image. `Spec/Program.lean` has `ValidCall`, the regions and
`readOutput`; `ChaCha20Poly1305/README.md` describes the wrappers.

Each stack budget is a constant computed from the disassembly, because the extraction estimates
none: for `encrypt` it reports a recursive call through `raw_vec::handle_error` (`0x10207c`), and
for the others an unresolved indirect jump at `0x10267e`, in `Formatter::write_str`; both are
reached only on panic paths. Every function on a path that returns reserves its frame once, by
pushes and at most one `sub` of a constant before any loop, and releases it before returning; the
calls on those paths form no cycle, and the loops over the message call the same functions with the
same frames for every block. So the deepest path that returns is the same for every input: the
wrapper, `AeadInOut::encrypt_inout_detached` or `decrypt_inout_detached` (with `Cipher`'s methods
inlined), and `try_apply_keystream_inout`. Each budget is that depth, counted as the extraction
counts (each function's pushes and `sub rsp`, and 8 bytes per call), plus the 128 bytes the
extraction adds below the deepest frame; each `Routine`'s docstring gives its figures.

Source: https://docs.rs/crate/aead/0.6.1/source/src/lib.rs (the `aead` methods the wrappers call)
-/

namespace ChaCha20Poly1305.Spec.Program

open Prelude X86

/--
The bytes of a fixed-size Rust array (a `Key`, `Nonce` or `Tag`), so that a call's inputs, a list
of byte strings, can list it as it is
-/
instance : CoeOut (Vector UInt8 n) ByteArray := ⟨fun array => ⟨array.toArray⟩⟩

/-- `bytes` as a fixed-size Rust array of `n` bytes, if it has `n` bytes -/
def toArray? (bytes : ByteArray) (n : Nat) : Option (Vector UInt8 n) :=
  if h : bytes.data.size = n then some ⟨bytes.data, h⟩ else none

/--
Where a System V integer argument is: in a register, or in stack slot `index`, the 8 bytes at
`RSP + 8 * (index + 1)` on entry, slot 0 being the seventh argument
-/
inductive Argument where
  | register (register : Syntax.Reg)
  | stack (index : Nat)

/-- How a call passes one of its inputs, a byte string it reads -/
inductive InputLayout where
  /-- A fixed-size Rust array of `bytes` bytes, at the address in `pointer` -/
  | fixed (pointer : Syntax.Reg) (bytes : Nat)
  /-- A slice at the address in `pointer`, its length in `length` -/
  | slice (pointer : Syntax.Reg) (length : Argument)
  /--
  The message of an in-place call: a slice at the start of the output buffer, its length in
  `length`, which the call reads and overwrites
  -/
  | inPlace (length : Argument)

/-- The caller's heap of a call that allocates, which the wrapper's bump allocator serves -/
structure Heap where
  /-- The register holding the heap's address -/
  pointer : Syntax.Reg
  /-- The argument holding the heap's length, which must be at least what the call allocates -/
  length : Argument
  /--
  The bytes the call allocates from the heap's start, given the message's length. Each call
  allocates one `Vec` with alignment 1: `Aead::encrypt` reserves the message and 16 bytes
  (`Vec::with_capacity`, aead 0.6.1 `src/lib.rs:201`), and `Aead::decrypt` copies its input
  (`Vec::from`, `src/lib.rs:213`), which allocates nothing for an empty input.
  -/
  bytes : Nat → Nat

/--
One wrapper: its address and stack budget, how it takes its inputs, where its output goes and how
long it is, its heap, and whether the crate accepts a call on given inputs
-/
structure Routine where
  /-- Address of the routine's first instruction. -/
  entryAddress : BitVec 64
  /-- Stack budget in bytes below entry RSP that a valid call provides; it may exceed the use. -/
  minStackBytes : Nat
  /-- How the routine takes its inputs, in the wrapper's argument order. -/
  inputs : List InputLayout
  /-- The argument holding the message's length, which the output's size follows. -/
  messageLength : Argument
  /-- The register holding the output buffer's address. -/
  outputPointer : Syntax.Reg
  /-- Number of bytes an accepted call writes to its output, given the message's length. -/
  outputBytes : Nat → Nat
  /-- The argument holding the output buffer's length, if the wrapper takes one. -/
  outputLength : Option Argument := none
  /--
  The argument holding the capacity of an in-place call's buffer, the bytes its message may grow
  into, if the wrapper takes one; otherwise the buffer is the message or the output, if longer.
  -/
  capacity : Option Argument := none
  /-- The caller's heap, for a call that allocates. -/
  heap : Option Heap := none
  /--
  Whether the crate accepts a call on these inputs, given room for the output (`hasRoom`): it
  returns `Ok` and writes its output.
  -/
  accepts : List ByteArray → Bool := fun _ => true
  /--
  Whether a rejected call needs the output buffer; false where a rejected call neither reads nor
  writes the buffer, nor reads its length: the crate returns its error first.
  -/
  needsOutputIfRejected : Bool := true

/-- Whether a routine overwrites its message in place, at the start of its output buffer -/
def Routine.inPlace (routine : Routine) : Bool :=
  routine.inputs.any fun | .inPlace _ => true | _ => false

/-- The call needs its output buffer: the crate accepts it, or it needs it when rejected too -/
def Routine.needsOutput (routine : Routine) (inputs : List ByteArray) : Bool :=
  routine.accepts inputs || routine.needsOutputIfRejected

/-- The 8-byte slot of stack argument `index` (from 0, the seventh System V argument) -/
def stackArgumentSlot (s : Machine.RamState) (index : Nat) : MemoryRegion :=
  ⟨(s.regValue .rsp).toNat + 8 * (index + 1), 8⟩

/--
The number argument `argument` holds on entry: a register's 64 bits, or the 64-bit word in its
stack slot, 0 if a byte of the slot is missing
-/
def argumentValue (s : Machine.RamState) : Argument → Nat
  | .register register => (s.regValue register).toNat
  | .stack index =>
    match Machine.loadBytes s.external (BitVec.ofNat 64 (stackArgumentSlot s index).start) 8 with
    | .ok value => value.toNat
    | .error _ => 0

/-- The message's length, from the routine's message length argument on entry -/
def messageBytes (routine : Routine) (s : Machine.RamState) : Nat :=
  argumentValue s routine.messageLength

/--
The size of the output buffer: the capacity argument's value where the routine has one; otherwise
the output's size, or for an in-place call the larger of the output and the message it reads there
-/
def bufferBytes (routine : Routine) (s : Machine.RamState) : Nat :=
  match routine.capacity with
  | some capacity => argumentValue s capacity
  | none =>
    if routine.inPlace then
      max (routine.outputBytes (messageBytes routine s)) (messageBytes routine s)
    else routine.outputBytes (messageBytes routine s)

/--
Whether the output fits in the output buffer; false only for an in-place call whose capacity is
below the output's size, which the crate rejects after encrypting the message where it lies
-/
def hasRoom (routine : Routine) (s : Machine.RamState) : Bool :=
  decide (routine.outputBytes (messageBytes routine s) ≤ bufferBytes routine s)

/--
Whether `Aead::decrypt` or `decrypt_in_place` accepts the inputs `[key, nonce, associatedData,
ciphertextWithTag]`: `AEAD.decryptWithTag` gives a plaintext
-/
def tagAccepted : List ByteArray → Bool
  | [key, nonce, associatedData, ciphertextWithTag] =>
    match toArray? key 32, toArray? nonce 12 with
    | some key, some nonce =>
      (AEAD.decryptWithTag associatedData key nonce ciphertextWithTag).isSome
    | _, _ => false
  | _ => false

/--
The wrapper `chacha20poly1305_encrypt` on `[key, nonce, associatedData, plaintext]`, which calls
`KeyInit::new` and `Aead::encrypt` and copies the returned ciphertext and 16-byte tag to the output
at R9; the associated data, plaintext, heap and output lengths are in stack slots 0 to 3, the heap
at R8. `Aead::encrypt` allocates one `Vec` of the plaintext and its tag. The extraction has no
estimate (a cycle through the panic path `raw_vec::handle_error`), so the budget, 1,168 bytes, is
computed from the disassembly (module docstring), along the wrapper (168), with `Aead::encrypt`
inlined, `AeadInOut::encrypt_inout_detached` (440) and `try_apply_keystream_inout` (416)
-/
def encrypt : Routine where
  entryAddress := Extracted.encryptAddress
  minStackBytes := 1168
  inputs := [.fixed .rdi 32, .fixed .rsi 12, .slice .rdx (.stack 0), .slice .rcx (.stack 1)]
  messageLength := .stack 1
  outputPointer := .r9
  outputBytes := (· + 16)
  outputLength := some (.stack 3)
  heap := some ⟨.r8, .stack 2, (· + 16)⟩

/--
The wrapper `chacha20poly1305_decrypt` on `[key, nonce, associatedData, ciphertextWithTag]`, which
calls `KeyInit::new` and `Aead::decrypt` and copies the returned plaintext, 16 bytes shorter than
its input, to the output at R9; the associated data, input, heap and output lengths are in stack
slots 0 to 3, the heap at R8. `Aead::decrypt` allocates one `Vec` holding a copy of its input, even
when it rejects it; the wrapper reads slot 3 and writes the output only after the crate returns
`Ok`. The extraction has no estimate, so the budget, 1,136 bytes, is computed from the
disassembly (module docstring), along the wrapper (136), with `Aead::decrypt` and
`AeadInOut::decrypt_in_place` inlined, `AeadInOut::decrypt_inout_detached` (440) and
`try_apply_keystream_inout` (416)
-/
def decrypt : Routine where
  entryAddress := Extracted.decryptAddress
  minStackBytes := 1136
  inputs := [.fixed .rdi 32, .fixed .rsi 12, .slice .rdx (.stack 0), .slice .rcx (.stack 1)]
  messageLength := .stack 1
  outputPointer := .r9
  outputBytes := (· - 16)
  outputLength := some (.stack 3)
  heap := some ⟨.r8, .stack 2, id⟩
  accepts := tagAccepted
  needsOutputIfRejected := false

/--
The wrapper `chacha20poly1305_encrypt_in_place` on `[key, nonce, associatedData, plaintext]`,
which calls `KeyInit::new` and `AeadInOut::encrypt_in_place` on a `SliceBuffer` holding the
plaintext at the start of the buffer at RCX, whose capacity is in stack slot 0: it overwrites the
plaintext with the ciphertext and then, if the 16-byte tag fits in the capacity, writes it after
the ciphertext; otherwise it returns its error, leaving the ciphertext alone (the branch at
`0x1019d7` returns 1 and skips the tag's stores). The associated data length is in R8, the plaintext
length in R9. The extraction has no estimate, so the budget, 1,104 bytes, is computed from the
disassembly (module docstring), along the wrapper (104), with `AeadInOut::encrypt_in_place` and
`SliceBuffer`'s methods inlined, `AeadInOut::encrypt_inout_detached` (440) and
`try_apply_keystream_inout` (416)
-/
def encryptInPlace : Routine where
  entryAddress := Extracted.encryptInPlaceAddress
  minStackBytes := 1104
  inputs := [.fixed .rdi 32, .fixed .rsi 12, .slice .rdx (.register .r8), .inPlace (.register .r9)]
  messageLength := .register .r9
  outputPointer := .rcx
  outputBytes := (· + 16)
  capacity := some (.stack 0)

/--
The wrapper `chacha20poly1305_decrypt_in_place` on
`[key, nonce, associatedData, ciphertextWithTag]`, which calls `KeyInit::new` and
`AeadInOut::decrypt_in_place` on a `SliceBuffer` of the buffer at RCX, overwriting the ciphertext
with the plaintext, 16 bytes shorter, if the tag after it matches; the associated data length is in
R8, the buffer length in R9. The extraction has no estimate, so the budget, 1,072 bytes, is computed
from the disassembly (module docstring), along the wrapper (72), with `AeadInOut::decrypt_in_place`
and `SliceBuffer`'s methods inlined, `AeadInOut::decrypt_inout_detached` (440) and
`try_apply_keystream_inout` (416)
-/
def decryptInPlace : Routine where
  entryAddress := Extracted.decryptInPlaceAddress
  minStackBytes := 1072
  inputs := [.fixed .rdi 32, .fixed .rsi 12, .slice .rdx (.register .r8), .inPlace (.register .r9)]
  messageLength := .register .r9
  outputPointer := .rcx
  outputBytes := (· - 16)
  accepts := tagAccepted

end ChaCha20Poly1305.Spec.Program
