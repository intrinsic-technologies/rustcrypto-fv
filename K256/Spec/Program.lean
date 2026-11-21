import Prelude
import K256.Spec.Program.Extracted.Image
import K256.Spec.Secp256k1
import K256.Spec.Ecdsa

/-!
# `k256` 0.14.0 call semantics

The call contract of the six entry points of `K256/program/src/lib.rs` that the theorems use, one
per crate function (`[entries]` in `K256/program/extraction.toml`). A `Routine` per entry point
gives what differs between them: its entry address, its stack budget (`minStackBytes`), its inputs
in the Rust function's argument order (`InputLayout`: the register holding each address, a slice's
length register, a fixed input's size, and what its bytes must hold), its byte arguments
(`ByteArgument`), the size of its output at RDI (`outputBytes`; a verifier writes none) and its heap
(`heapBytes`). One `ValidCall` states what a call needs; `readOutput` reads the output back from
final memory at the initial RDI, and `writtenRegions` lists the regions a call may write.

The routines are `signingKeyTrySign`, `verifyingKeyVerify`, `signatureFromSlice`,
`signingKeyGenerateFromRng`, `publicKeyFromSec1Bytes` and `ecdhDiffieHellman`. How to read the
theorem statements, with the calling convention, and how to build the verified binary are in
`K256/README.md`.

Stack budgets (`Routine.minStackBytes`): every budget is a static bound over the disassembly: a walk
of each path of each function on the call graph, counting pushes, stack allocations, stack-probe
loops and return addresses, through jump tables and calls through the read-only data and registers
loaded from it, plus 128 bytes (or the deepest negative RSP offset a function uses) below each
function's deepest point. The target has no red zone (its target specification sets
`disable-redzone`), so each budget is the deepest call chain, returning or panicking, plus 128 bytes
of slack. One kind of indirect call is resolved by hand: the drop of an error's boxed source through
its vtable, which is cut, since every error on these call paths is made by `Error::new()` and has no
source. No budget depends on the inputs: no function on these call graphs recurses or allocates
stack by an input's length, and messages are hashed block by block. A caller may provide more.
-/

namespace K256.Spec.Program

open Prelude X86 Standards.SECG.ECC Standards.SECG.DomainParameters

/-- The direction flag is clear, so string instructions advance their pointers. -/
abbrev DirectionFlagUnset (s : Machine.RamState) : Prop :=
  Prelude.RFLAGS.DirectionFlagClear s.RFLAGS

/-- Physical RAM contains every extracted byte -/
def ProgramLoaded (s : Machine.RamState) : Prop :=
  ∀ address byte, Extracted.programSections.fetchByte address = some byte →
    s.external[address]? = some byte

/-- `address` is contained by an extracted section -/
def InProgram (address : BitVec 64) : Prop :=
  ∃ byte, Extracted.programSections.fetchByte address = some byte

/-- The page-table frames that `IdentityMappedMemory` requires -/
def pageTables : MemoryRegion := ⟨0x1000, 0x2000⟩

/-- The return address in the slot at RSP is below the user address limit, outside the program -/
def ValidReturnAddress (s : Machine.RamState) : Prop :=
  ∃ address, (Stack.returnSlot s).Word64At s.external address ∧
    address.toNat < userAddressLimit ∧
    ¬ InProgram address

/--
The System V callee-saved general-purpose registers other than RSP retain their entry values.
RSP is fixed by the return boundary of `Prelude.UniqueExecution`.
-/
def CalleeSavedRegistersUnchanged (initial final : Machine.RamState) : Prop :=
  ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
    final.regValue register = initial.regValue register

/--
The call never returns to its caller: its return boundary can be read, and every run of finite
fuel from `s` ends out of fuel before reaching it, so it neither returns nor faults. Only
`k256_signing_key_try_sign`'s theorem concludes it, when RFC 6979's nonce search never finds a
signature, as the crate retries nonces without bound.
-/
def NeverReturns [Machine.Bindings] (s : Machine.RamState) : Prop :=
  ∃ boundary, nearReturn64Boundary s = .ok boundary ∧ Diverges boundary s []

/--
The bytes of `region` in `final` memory, in address order. Returns `.ok` on success or
`.error (.unmappedMemory address)` at the first missing byte.
-/
def readRegion (final : Machine.RamState) (region : MemoryRegion) :
    Except Machine.Fault ByteArray :=
  let bytes : Except Machine.Fault (List UInt8) := (List.range region.size).mapM fun i =>
    let address := BitVec.ofNat 64 (region.start + i)
    match final.external[address]? with
    | some byte => .ok byte
    | none => .error (.unmappedMemory address)
  bytes.map fun bytes => ⟨bytes.toArray⟩

/-- Validity conditions on an input in memory: `bytes` at the nonzero start of `region` -/
def ValidInput (s : Machine.RamState) (region : MemoryRegion) (bytes : ByteArray) : Prop :=
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.HasBytes s.external bytes

/-- Validity conditions on a written region in memory: at a nonzero address, below 4 GiB, RAM -/
def ValidOutput (s : Machine.RamState) (region : MemoryRegion) : Prop :=
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.Allocated s.external

/--
Validity conditions on the caller's heap, whose first `region.size` bytes are `region`, at the
address in RDX: they are RAM at a nonzero address, RCX gives a length of at least `region.size`,
and the heap's end does not pass `2^64`
-/
def ValidHeap (s : Machine.RamState) (region : MemoryRegion) : Prop :=
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.Allocated s.external ∧
  region.size ≤ (s.regValue .rcx).toNat ∧
  region.start + (s.regValue .rcx).toNat < 2 ^ 64

/--
The written regions are pairwise disjoint, and each avoids every region the call only reads, the
program and the page tables; the regions the call only reads may overlap one another
-/
def MemorySeparation (written read : List MemoryRegion) : Prop :=
  written.Pairwise MemoryRegion.Disjoint ∧
  ∀ region ∈ written,
    region.Avoids (fun address => InProgram address ∨ pageTables.Contains address.toNat) ∧
    ∀ input ∈ read, region.Disjoint input

/--
The `.bss` section at `0x300000`, the 16 bytes of the wrapper's bump allocator `HEAP`, its next
free address and its end (`K256/program/layout.ld`, which asserts its size); an allocating call
writes both before it reads either
-/
def allocatorStateRegion : MemoryRegion := ⟨0x300000, 16⟩

/--
The status of `signature::Error`, which `Verifier::verify` and `Signature::from_slice` return for
an input they refuse
-/
def signatureErrorStatus : BitVec 32 := 1

/--
The status of `elliptic_curve::Error`, which `SecretKey::from_bytes` and
`PublicKey::from_sec1_bytes` return for bytes they refuse
-/
def ellipticCurveErrorStatus : BitVec 32 := 1

/--
How an entry point receives one input, a byte string it reads, and what the bytes must hold to be
a value of the Rust argument's type, which the wrapper builds with a crate decoder or passes as a
slice (`valid`)
-/
inductive InputLayout where
  /-- A value of a fixed-size Rust type: `bytes` bytes at the address in `register` -/
  | fixed (register : Syntax.Reg) (bytes : Nat) (valid : ByteArray → Bool)
  /--
  A slice of any length: its address in `register`, its length in `lengthRegister`
  -/
  | slice (register lengthRegister : Syntax.Reg) (valid : ByteArray → Bool)

/-- What an input's bytes must hold to be a value of its Rust argument's type -/
def InputLayout.valid : InputLayout → ByteArray → Bool
  | .fixed _ _ valid => valid
  | .slice _ _ valid => valid

/--
A byte an entry point takes by value, in the low byte of `register`, and what it must hold to be a
value of the Rust argument's type (`valid`)
-/
structure ByteArgument where
  /-- The register whose low byte holds the argument -/
  register : Syntax.Reg
  /-- What the byte must hold to be a value of its Rust type -/
  valid : Nat → Bool

/--
One entry point: its address, its stack budget, its inputs and byte arguments in the Rust
function's argument order, its output and its heap
-/
structure Routine where
  /-- Address of the routine's first instruction. -/
  entryAddress : BitVec 64
  /-- Stack budget in bytes below entry RSP that a valid call provides; it may exceed the use. -/
  minStackBytes : Nat
  /--
  Number of bytes the routine writes to its output buffer at RDI; 0 for one that writes none.
  -/
  outputBytes : Nat
  /-- Whether the routine writes an output buffer at RDI: every one but `verifyingKeyVerify`. -/
  writesOutput : Bool := true
  /-- The inputs the routine reads, in the Rust function's argument order. -/
  inputs : List InputLayout
  /-- The bytes the routine takes by value, after its inputs. -/
  byteArguments : List ByteArgument := []
  /--
  Heap bytes the call allocates from the caller's heap, at RDX with its length in RCX; 0 for a
  routine that allocates nothing and takes no heap, as every routine here.
  -/
  heapBytes : Nat := 0

/-- Any bytes: a slice of `u8` -/
def anyBytes (_ : ByteArray) : Bool := true

/--
A secret key: 32 big-endian bytes of a scalar `1 ≤ d < n` (`Keys.decodeSecret`), as
`SigningKey::from_bytes` and `SecretKey::from_bytes` accept them
-/
def isSecretKey (bytes : ByteArray) : Bool :=
  (Keys.decodeSecret Secp256k1.domain bytes).isSome

/-- An ECDSA signature `r ‖ s` that `Signature::from_bytes` accepts (`Ecdsa.signatureScalars`) -/
def isSignature (bytes : ByteArray) : Bool :=
  (Ecdsa.signatureScalars bytes).isSome

/-- A public key that `PublicKey::from_sec1_bytes` decodes (`Secp256k1.decodePublicKey`) -/
def isPublicKey (bytes : ByteArray) : Bool :=
  (Secp256k1.decodePublicKey bytes).isSome

/-- A point's 33-byte `GroupEncoding` that `GroupEncoding::from_bytes` decodes (`groupPoint`) -/
def isGroupPoint (bytes : ByteArray) : Bool :=
  (Secp256k1.groupPoint bytes).isSome

/-- The region of an input's bytes: the layout's size for a fixed-size input, the bytes' own size
for a slice -/
def inputRegion (s : Machine.RamState) (layout : InputLayout) (bytes : ByteArray) : MemoryRegion :=
  match layout with
  | .fixed register size _ => registerRegion s register size
  | .slice register _ _ => registerRegion s register bytes.size

/-- For a slice, its length register holds its length; nothing for a fixed-size input -/
def LengthArgumentMatches (s : Machine.RamState) (layout : InputLayout) (bytes : ByteArray) :
    Prop :=
  match layout with
  | .fixed _ _ _ => True
  | .slice _ lengthRegister _ => (s.regValue lengthRegister).toNat = bytes.size

/-- The low byte of the argument's register holds `value` -/
def ByteArgumentMatches (s : Machine.RamState) (argument : ByteArgument) (value : Nat) : Prop :=
  (s.regValue argument.register).setWidth 8 = BitVec.ofNat 8 value

/--
`property` holds of each layout and the argument in the same position, and there are as many
arguments as layouts
-/
def EachArgument {α β : Type} (property : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | layout :: layouts, argument :: arguments =>
    property layout argument ∧ EachArgument property layouts arguments
  | _, _ => False

/-- The regions of a call's inputs, in order -/
def inputRegions (routine : Routine) (s : Machine.RamState) (inputs : List ByteArray) :
    List MemoryRegion :=
  List.zipWith (inputRegion s) routine.inputs inputs

/-- Output buffer of `routine.outputBytes` bytes supplied through the System V RDI argument -/
def outputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rdi routine.outputBytes

/-- The first `routine.heapBytes` bytes of the caller's heap, supplied through the System V RDX
argument -/
def heapRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rdx routine.heapBytes

/--
The regions a call to `routine` may write, in the order of the theorems' frames: its output buffer,
if it writes one; the caller's heap and the allocator's state, if it allocates; and its stack region
-/
def writtenRegions (routine : Routine) (s : Machine.RamState) : List MemoryRegion :=
  (if routine.writesOutput then [outputRegion routine s] else []) ++
    (if 0 < routine.heapBytes then [heapRegion routine s, allocatorStateRegion] else []) ++
    [Stack.region s routine.minStackBytes]

/--
Validity conditions for a System V call to `routine` with the inputs `inputs` and the byte
arguments `byteArguments`, in the Rust function's argument order. This is everything a call needs:

- the direction flag is clear, the program is loaded at its link-time addresses (`ProgramLoaded`),
  and RIP is at the routine's entry;
- each input's address, and a slice's length, are in the registers its `InputLayout` names, and
  each byte argument is in the low byte of its `ByteArgument`'s register;
- each input and byte argument holds a value of its Rust argument's type (`InputLayout.valid`,
  `ByteArgument.valid`), which the wrapper does not check;
- each input's bytes are in memory at a nonzero address, even when empty, and end strictly below
  `userAddressLimit` (2^32) (`ValidInput`);
- for a routine that writes an output, its `outputBytes` bytes at RDI are RAM at a nonzero address,
  ending strictly below `userAddressLimit` (`ValidOutput`);
- for a routine that allocates, the caller's heap, at RDX with its length in RCX, satisfies
  `ValidHeap`, and the allocator's state (`allocatorStateRegion`) is RAM;
- the stack region, `routine.minStackBytes` bytes below RSP and the 8-byte return slot at RSP, is
  RAM ending strictly below `userAddressLimit`, RSP is at least `minStackBytes`, and RSP is 8 more
  than a multiple of 16 (`Stack.Valid`);
- the written regions (`writtenRegions`) are pairwise disjoint, and each avoids every input, the
  program and the page tables at `[0x1000, 0x3000)` (`MemorySeparation`); the inputs may overlap
  one another;
- the 8 bytes at RSP hold a return address below `userAddressLimit` and outside the program
  (`ValidReturnAddress`).
-/
structure ValidCall (routine : Routine) (s : Machine.RamState) (inputs : List ByteArray)
    (byteArguments : List Nat := []) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  lengthArgumentsMatchInputs : EachArgument (LengthArgumentMatches s) routine.inputs inputs
  byteArgumentsMatchValues :
    EachArgument (ByteArgumentMatches s) routine.byteArguments byteArguments
  inputsHoldValues :
    EachArgument (fun layout bytes => layout.valid bytes = true) routine.inputs inputs
  byteArgumentsHoldValues : EachArgument (fun argument value => argument.valid value = true)
    routine.byteArguments byteArguments
  inputsInMemory :
    EachArgument (fun layout bytes => ValidInput s (inputRegion s layout bytes) bytes)
      routine.inputs inputs
  outputInMemory : routine.writesOutput = true → ValidOutput s (outputRegion routine s)
  heapInMemory : 0 < routine.heapBytes → ValidHeap s (heapRegion routine s)
  allocatorStateInMemory : 0 < routine.heapBytes → allocatorStateRegion.Allocated s.external
  stackAvailable : Stack.Valid s routine.minStackBytes
  separation : MemorySeparation (writtenRegions routine s) (inputRegions routine s inputs)
  returnAddress : ValidReturnAddress s

/-- Reads the output from final memory at the initial output pointer -/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault ByteArray :=
  readRegion final (outputRegion routine initial)

/--
The wrapper `k256_signing_key_try_sign`: `SigningKey::from_bytes`, then `Signer::try_sign` for
`SigningKey` at `Signature`, writing the 64-byte signature `r ‖ s`; its inputs are the secret key
(RSI) and the message (RDX, its length in RCX). It returns nothing, as `try_sign` cannot fail for
this key type.
-/
def signingKeyTrySign : Routine where
  entryAddress := Extracted.signingKeyTrySignAddress
  minStackBytes := 11192
  outputBytes := 64
  inputs := [.fixed .rsi 32 isSecretKey, .slice .rdx .rcx anyBytes]

/--
The wrapper `k256_verifying_key_verify`: `VerifyingKey::from_sec1_bytes` on the key's 65-byte
uncompressed encoding (RDI), `Signature::from_bytes` on the signature (RCX), then `Verifier::verify`
for `VerifyingKey` on the message (RSI, its length in RDX); it writes no output.
-/
def verifyingKeyVerify : Routine where
  entryAddress := Extracted.verifyingKeyVerifyAddress
  minStackBytes := 13000
  outputBytes := 0
  writesOutput := false
  inputs := [.fixed .rdi 65 isPublicKey, .slice .rsi .rdx anyBytes, .fixed .rcx 64 isSignature]

/--
The wrapper `k256_signature_from_slice`: `Signature::from_slice` on the bytes (RSI, their length in
RDX), writing the signature `r ‖ s`, 64 bytes. Its deepest chain ends in a panic, which never
returns: the index check in crypto-bigint's `fill_limbs_from_be_slice_truncated`. The deepest
returning chain is 656 bytes, slack included.
-/
def signatureFromSlice : Routine where
  entryAddress := Extracted.signatureFromSliceAddress
  minStackBytes := 784
  outputBytes := 64
  inputs := [.slice .rsi .rdx anyBytes]

/--
The wrapper `k256_signing_key_generate_from_rng`: `Generate::generate_from_rng` for `SigningKey`
with the wrapper's `CallerBytes` generator over the random bytes (RSI, their length in RDX), which
must hold a 32-byte block that is a valid secret scalar (`Secp256k1.randomSecret`), writing the
drawn key, 97 bytes: its secret scalar's 32 bytes (`to_bytes`), then its verifying key's 65-byte
uncompressed SEC 1 encoding (`verifying_key().to_sec1_point(false)`).
-/
def signingKeyGenerateFromRng : Routine where
  entryAddress := Extracted.signingKeyGenerateFromRngAddress
  minStackBytes := 10584
  outputBytes := 97
  inputs := [.slice .rsi .rdx fun random => (Secp256k1.randomSecret random).isSome]

/--
The wrapper `k256_public_key_from_sec1_bytes`: `PublicKey::from_sec1_bytes` on the bytes (RSI, their
length in RDX), writing the key's 65-byte uncompressed SEC 1 encoding. The extraction gives no
stack estimate for this image (`Extracted.Symbols`: an unresolved call).
-/
def publicKeyFromSec1Bytes : Routine where
  entryAddress := Extracted.publicKeyFromSec1BytesAddress
  minStackBytes := 1928
  outputBytes := 65
  inputs := [.slice .rsi .rdx anyBytes]

/--
The wrapper `k256_ecdh_diffie_hellman`: `NonZeroScalar::from_repr` on the secret key (RSI),
`GroupEncoding::from_bytes` for `AffinePoint` on the point's 33-byte `GroupEncoding` (RDX), then
`ecdh::diffie_hellman`, writing the shared secret's 32 bytes.
-/
def ecdhDiffieHellman : Routine where
  entryAddress := Extracted.ecdhDiffieHellmanAddress
  minStackBytes := 10088
  outputBytes := 32
  inputs := [.fixed .rsi 32 isSecretKey, .fixed .rdx 33 isGroupPoint]

end K256.Spec.Program
