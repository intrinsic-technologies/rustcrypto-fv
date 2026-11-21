import Base16ct.Spec

/-!
# Satisfiability of the `base16ct` call predicates

A theorem whose hypotheses no state meets is proved by anything, so the theorems here show that
each statement's hypotheses can be met on non-empty data. Checked by Lean when `Base16ct.Tests` is
built, they exhibit for every theorem of `Base16ct.Statements` bindings and an
initial state that meet all of its hypotheses together, on the 6-byte input `foobar`:

* `validCall_satisfiable`: for each of the seven routines called through `Program.ValidCall`,
  `Prelude.MachineRamUnitStrideDecodable`, `Prelude.SupportedIntegerMachineState` and
  `Program.ValidCall routine initial foobar 12 writtenLength lengthWritten`, for every
  `writtenLength` up to 12 and every `lengthWritten`, so also for the written length and the
  condition each theorem supplies, 12 for `encode` and `encode_str` and 3 for `decode`;
* `validLengthCall_satisfiable`: the same for the two routines called through
  `Program.ValidLengthCall`, with `byteLength` 6, for every `lengthWritten`.

The witnesses meet every conditional requirement, the length word, the output buffer and their
separation included, so they meet the strongest form of each predicate. They are not runs:
nothing here executes the extracted code, and nothing about the theorems of `Base16ct.Statements`,
which `Base16ct/Proofs/` proves, follows from them beyond their hypotheses being consistent.

## The states

The bindings are `modelBindings witnessProcessor`. `witnessProcessor` is the processor that
lean-x86's `Processor.initialize` builds from `cpuidQuery true`, the CPUID answers of lean-x86's
validation fixture. The bindings use the default memory-type configuration, whose MTRR
capabilities have no SMRR interface.

Each initial state, `callState`, is lean-x86's user profile `UserProcess.Profile.initialState`
with CR3 at the page tables, and CR4.OSFXSR and CR4.OSXMMEXCPT set as `Prelude.SupportedSSE`
requires. The profile chooses write-back memory: IA32_MTRR_DEF_TYPE `0x806`, IA32_PAT
`0x0606060606060606`, no variable or fixed MTRR range, and zero SMRR registers. Its RAM, built by
`callMemory` from layers of consecutive bytes, holds:

* the extracted `.text` at `0x100000`, the program's only section;
* the 4-KiB PML4 and PDPT frames of `Program.pageTables`, holding the entries that
  `Prelude.IdentityMappedMemory` requires;
* the input at `0x500000` (RDI, with its length in RSI);
* 4 KiB from `0x600000` on (RCX), of which the output buffer is the first bytes (R8 holds its
  capacity);
* the 8-byte length word at `0x700000` (RDX);
* 4 KiB of stack below `0x800000`, with the entry RSP at `0x7FFFF8`, which is 8 modulo 16, and
  the return address `0x900000` at RSP.

## How the theorems are proved

`getElem?_callMemory` reads the RAM back as the function `callByte`, so the memory conjuncts are
facts about byte layers. `witnessCheck_routines` decides, by kernel reduction and for every
routine, that its stack budget fits the 4-KiB stack and the facts that need the processor: the
CPUID reads of SSE, LAM, LASS and LZCNT, and the memory-type inputs that lean-x86 reads from the
processor and the state. `emulateGetMemoryType_memoryTypeInputs` shows that those inputs select
write-back at selector 0 for every address below `userAddressLimit`, and `lookup_eq_of_inputs`
carries this to `Bindings.MemoryType.lookup`. No `native_decide` is used.
-/

namespace Base16ct.Tests.CallWitness

open Base16ct.Spec
open Prelude X86 X86.Machine X86.UserProcess

/-! ## Processors and bindings -/

/--
CPUID answers for an x86-64 processor with SSE2, 1-GiB pages, and 52 physical and 48 linear
address bits, which `Prelude.SupportedIntegerMachineState` and lean-x86's identity map require;
`lzcnt` sets the LZCNT feature bit of leaf `0x80000001`. These are the answers of lean-x86's
validation fixture (`TestSupport.SourceExecution.sourceCpuid`), which reports LZCNT.
-/
def cpuidQuery (lzcnt : Bool) : Cpuid.Query := Cpuid.Config.toQuery {
  maxBasic := 0x14
  maxExtended := 0x80000008
  vendor := (0x756e6547, 0x6c65746e, 0x49656e69)
  entries := #[
    ⟨1, 0, (0, 0x800, 1 <<< 13, 0x07899171)⟩,
    ⟨2, 0, (1, 0, 0, 0)⟩,
    ⟨7, 0, (2, 0, 0, 0)⟩, ⟨7, 1, (0, 0, 0, 0)⟩, ⟨7, 2, (0, 0, 0, 0)⟩,
    ⟨0x14, 0, (1, 0, 0, 0)⟩, ⟨0x14, 1, (0, 0, 0, 0)⟩,
    ⟨0x80000001, 0, (0, 0, if lzcnt then 1 <<< 5 else 0, 0x24100800)⟩,
    ⟨0x80000008, 0, (0x3034, 0, 0, 0)⟩] }

/-- The first page-table frame, where `Prelude.IdentityMappedMemory` puts the PML4. -/
def tableBase : Nat := 0x1000

/-- The user-profile state that a processor's address widths are read in. -/
def processorSeed : RamState :=
  Profile.initialState .user (fun _ => false) Ram.empty (Vector.replicate 16 0) 0
    default (BitVec.ofNat 64 tableBase) 0

/-- The processor that lean-x86 initializes from `cpuidQuery lzcnt`. -/
def modelProcessor (lzcnt : Bool) : Except String Processor :=
  (Processor.initialize (cpuidQuery lzcnt) processorSeed .Core).mapError reprStr

/-- `modelProcessor true` initializes. -/
theorem modelProcessor_isSome : (modelProcessor true).toOption.isSome = true := by
  decide +kernel

/-- The processor of the theorems, which reports LZCNT. -/
@[instance_reducible]
def witnessProcessor : Processor :=
  (modelProcessor true).toOption.get modelProcessor_isSome

/-- `witnessProcessor` has the 52 physical address bits that `SupportedIntegerCPU` requires. -/
theorem witnessProcessor_maxPhysical : witnessProcessor.config.Max_Physical_Address = 52 := by
  decide +kernel

/-- `witnessProcessor` does not update accessed bits early. -/
theorem witnessProcessor_early :
    witnessProcessor.config.Feature_Early_Page_Access_Bit_Update = false := by
  decide +kernel

/-- Rejects a numerical binding, which no extracted routine uses. -/
def unused (operation : String) : Runtime.Error Empty :=
  .externalFailure s!"{operation} is not used by the base16ct routines"

/-- Numerical bindings that reject every call: the routines use no x87 or SSE arithmetic. -/
@[instance_reducible]
def rejectingNumerical {σ : Type} : Bindings.Numerical σ where
  reciprocal := ⟨fun _ => throw (unused "RCPSS")⟩
  reciprocalSqrt := ⟨fun _ => throw (unused "RSQRTSS")⟩
  exp2m1 := ⟨fun _ => throw (unused "F2XM1")⟩
  sin := ⟨fun _ => throw (unused "FSIN")⟩
  cos := ⟨fun _ => throw (unused "FCOS")⟩
  sincos := ⟨fun _ => throw (unused "FSINCOS")⟩
  tan := ⟨fun _ => throw (unused "FPTAN")⟩
  atan2 := ⟨fun _ _ => throw (unused "FPATAN")⟩
  mulLog2 := ⟨fun _ _ => throw (unused "FYL2X")⟩
  mulLog2p1 := ⟨fun _ _ => throw (unused "FYL2XP1")⟩

/--
Machine bindings built from lean-x86's own constructors: the remainder-reduction, FXSAVE,
compare-memory and stack-return choices of lean-x86's validation fixture, the default memory-type
configuration, and rejecting bindings for the numerical helpers, cache-disabled memory types,
MSRs, ports, cache and translation maintenance, and the time-stamp counter, which the routines
do not use. The string-stride binding returns one element per iteration, as
the statements require through `MachineRamUnitStrideDecodable`.
-/
@[instance_reducible]
def modelBindings (processor : Processor) : Bindings where
  numerical := rejectingNumerical
  remainderReduction := Bindings.RemainderReduction.fixed 0
  fxsave := Bindings.Fxsave.ofFunctions (fun _ _ => 0) (fun _ _ => false) (fun _ _ => true)
    (fun _ _ => ⟨none, 0, none, none⟩) (fun _ _ => ⟨none⟩) (fun _ _ => false)
    (fun _ _ => false)
  compareMemory := Bindings.CompareMemory.fixed false false false
  stackReturn := Bindings.StackReturn.fixed false false
  memoryType := MemoryType.Config.default
  cacheControl := Bindings.CacheControl.unavailable
  msrReadAllowedFallback := inferInstance
  msrWriteAllowedFallback := inferInstance
  msrReadFallback := inferInstance
  msrWriteBehaviorFallback := inferInstance
  msrCommitFallback := inferInstance
  portRead := inferInstance
  portWrite := inferInstance
  invalidateAllTranslations := inferInstance
  invalidateTranslations := inferInstance
  cacheInvalidate := inferInstance
  cacheFlush := inferInstance
  cacheWriteback := inferInstance
  prefetch := Bindings.Cache.ignorePrefetch
  stringStride := ⟨fun _ _ => pure 1⟩
  timestamp := inferInstance
  processor
  daz16 := ⟨fun _ => throw (unused "DAZ16")⟩
  ftz16 := ⟨fun _ => throw (unused "FTZ16")⟩

section
open scoped X86.Runtime.Syntax

/-- The default MTRR capabilities `0x508` leave bit 11, the SMRR interface, clear. -/
theorem smrrMatches_eq (base mask address : BitVec 64) :
    Helpers.Emulate_Memory.SMRR_Matches 0x508 base mask address = .ok false := by
  unfold Helpers.Emulate_Memory.SMRR_Matches
  simp [Runtime.CheckedSlice.read, Runtime.slice, Runtime.assert]
  rfl

end

/-- `Prelude.SMRRUnblocked` holds for `modelBindings` in every state. -/
theorem smrrUnblocked (processor : Processor) (s : RamState) :
    SMRRUnblocked (modelBindings processor) s :=
  fun address => smrrMatches_eq _ _ address

/-! ## RAM as byte layers -/

/-- The byte of `bytes` placed from `start` on at `address`, if any. -/
def byteAt (start : Nat) (bytes : List UInt8) (address : Nat) : Option UInt8 :=
  if start ≤ address ∧ address < start + bytes.length then bytes[address - start]? else none

theorem findSomeRev?_codeRange (start : Nat) (bytes : List UInt8) (address : BitVec 64)
    (hfit : start + bytes.length ≤ 2 ^ 64) :
    (codeRange (BitVec.ofNat 64 start) bytes).findSomeRev?
        (fun entry => match entry with
          | (stored, byte) => if (stored == address) = true then some byte else none) =
      byteAt start bytes address.toNat := by
  induction bytes generalizing start with
  | nil => simp [codeRange, byteAt]
  | cons byte bytes ih =>
    have haddress := address.isLt
    rw [codeRange, show BitVec.ofNat 64 start + 1 = BitVec.ofNat 64 (start + 1) from
      BitVec.ofNat_add_ofNat _ _]
    simp only [List.findSomeRev?, ih (start + 1) (by simp at hfit; omega)]
    simp only [byteAt, List.length_cons, beq_iff_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat]
    simp at hfit
    have hstart : start % 2 ^ 64 = start := Nat.mod_eq_of_lt (by omega)
    rw [hstart]
    by_cases hin : start + 1 ≤ address.toNat ∧ address.toNat < start + 1 + bytes.length
    · rw [List.getElem?_eq_getElem (show address.toNat - (start + 1) < bytes.length by omega),
        show address.toNat - start = (address.toNat - (start + 1)) + 1 by omega,
        List.getElem?_cons_succ, List.getElem?_eq_getElem (by omega)]
      simp only [hin.1, hin.2, show start ≤ address.toNat by omega,
        show address.toNat < start + (bytes.length + 1) by omega, and_self, ↓reduceIte]
    · simp only [hin, ↓reduceIte]
      by_cases heq : start = address.toNat
      · subst heq
        simp
      · simp only [heq, ↓reduceIte]
        simp only [show ¬ (start ≤ address.toNat ∧
          address.toNat < start + (bytes.length + 1)) by omega, ↓reduceIte]

theorem getElem?_insertMany_codeRange (memory : Ram) (start : Nat) (bytes : List UInt8)
    (address : BitVec 64) (hfit : start + bytes.length ≤ 2 ^ 64) :
    (memory.insertMany (codeRange (BitVec.ofNat 64 start) bytes))[address]? =
      (byteAt start bytes address.toNat).or memory[address]? := by
  rw [Std.ExtHashMap.getElem?_insertMany_list, findSomeRev?_codeRange start bytes address hfit]

theorem byteAt_of_mem_codeRange {start : Nat} {bytes : List UInt8} {address : BitVec 64}
    {byte : UInt8} (hfit : start + bytes.length ≤ 2 ^ 64)
    (h : (address, byte) ∈ codeRange (BitVec.ofNat 64 start) bytes) :
    byteAt start bytes address.toNat = some byte := by
  induction bytes generalizing start with
  | nil => simp [codeRange] at h
  | cons first bytes ih =>
    simp only [List.length_cons] at hfit
    rw [codeRange, show BitVec.ofNat 64 start + 1 = BitVec.ofNat 64 (start + 1) from
      BitVec.ofNat_add_ofNat _ _, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp [byteAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show start < 2 ^ 64 by omega)]
    · have hrest := ih (start := start + 1) (by omega) h
      simp only [byteAt] at hrest ⊢
      split at hrest
      · rw [show address.toNat - start = (address.toNat - (start + 1)) + 1 by omega,
          List.getElem?_cons_succ]
        simp only [List.length_cons, show start ≤ address.toNat by omega,
          show address.toNat < start + (bytes.length + 1) by omega, and_self, ↓reduceIte, hrest]
      · simp at hrest

theorem lt_of_byteAt_eq_some {start : Nat} {bytes : List UInt8} {address : Nat} {byte : UInt8}
    (h : byteAt start bytes address = some byte) :
    start ≤ address ∧ address < start + bytes.length := by
  simp only [byteAt] at h
  split at h
  · assumption
  · simp at h

theorem byteAt_eq_none {start : Nat} {bytes : List UInt8} {address : Nat}
    (h : address < start ∨ start + bytes.length ≤ address) :
    byteAt start bytes address = none := by
  simp only [byteAt]
  exact ite_eq_right_iff.mpr fun h' => absurd h' (by omega)

theorem byteAt_replicate {start count address : Nat} (value : UInt8) (hlow : start ≤ address)
    (hhigh : address < start + count) :
    byteAt start (List.replicate count value) address = some value := by
  simp only [byteAt, List.length_replicate, hlow, hhigh, and_self, ↓reduceIte,
    List.getElem?_replicate, show address - start < count by omega]

theorem length_toList (data : Bytes.Chunked) : data.toList.length = data.size := by
  simp [Bytes.Chunked.toList, Bytes.Chunked.toListFrom]

/-! ## Initial states -/

/-- Address of the input bytes. -/
def inputAddress : Nat := 0x500000

/-- Address of the output buffer. -/
def outputAddress : Nat := 0x600000

/-- Allocated bytes from `outputAddress` on, at least every output buffer. -/
def outputAllocation : Nat := 0x1000

/-- Address of the length word. -/
def lengthAddress : Nat := 0x700000

/-- End of the allocated stack; the entry RSP is 8 bytes below it. -/
def stackTop : Nat := 0x800000

/-- Allocated stack bytes below `stackTop`, more than any routine's `minStackBytes`. -/
def stackAllocation : Nat := 0x1000

/-- The entry RSP, which is 8 modulo 16. -/
def stackPointer : Nat := stackTop - 8

/-- The return address on the stack, outside the program. -/
def returnAddress : Nat := 0x900000

/-- The little-endian bytes of a 64-bit word. -/
def wordBytes (value : Nat) : List UInt8 :=
  (List.range 8).map fun i => UInt8.ofNat (value >>> (8 * i) % 256)

/-- The PML4 frame at `0x1000`: the entry `0x2027` that `Prelude.IdentityMappedMemory` requires. -/
def pml4Bytes : List UInt8 :=
  (List.range 8).map (fun i => UInt8.ofNat ((0x2027 : Nat) >>> (8 * i) % 256)) ++
    List.replicate 4088 0

/--
The PDPT frame at `0x2000`: the four 1-GiB entries that `Prelude.IdentityMappedMemory` requires.
-/
def pdptBytes : List UInt8 :=
  (List.range 32).map (fun index =>
    UInt8.ofNat ((((index / 8) <<< 30 ||| 0xe7) : Nat) >>> (8 * (index % 8)) % 256)) ++
    List.replicate 4064 0

/-- The bytes of the extracted `.text` section. -/
def textBytes : List UInt8 :=
  Program.Extracted.textBytes.toList

/--
The RAM of a call on `input`, in layers from the bottom: the input, the output allocation, the length word, the stack, the return address, the page tables, and the
program image.
-/
def callMemory (input : List UInt8) : Ram :=
  (((((((Ram.empty.insertMany
    (codeRange (BitVec.ofNat 64 inputAddress) input)).insertMany
    (codeRange (BitVec.ofNat 64 outputAddress) (List.replicate outputAllocation 0xAA))).insertMany
    (codeRange (BitVec.ofNat 64 lengthAddress) (List.replicate 8 0xBB))).insertMany
    (codeRange (BitVec.ofNat 64 (stackTop - stackAllocation))
      (List.replicate stackAllocation 0xCC))).insertMany
    (codeRange (BitVec.ofNat 64 stackPointer) (wordBytes returnAddress))).insertMany
    (codeRange (BitVec.ofNat 64 0x1000) pml4Bytes)).insertMany
    (codeRange (BitVec.ofNat 64 0x2000) pdptBytes)).insertMany
    (codeRange (BitVec.ofNat 64 0x100000) textBytes)

/-- The bytes of `callMemory` above the input, from the top layer down. -/
def fixedByte (address : Nat) : Option UInt8 :=
  (byteAt 0x100000 textBytes address).or <|
  (byteAt 0x2000 pdptBytes address).or <|
  (byteAt 0x1000 pml4Bytes address).or <|
  (byteAt stackPointer (wordBytes returnAddress) address).or <|
  (byteAt (stackTop - stackAllocation) (List.replicate stackAllocation 0xCC) address).or <|
  (byteAt lengthAddress (List.replicate 8 0xBB) address).or <|
  byteAt outputAddress (List.replicate outputAllocation 0xAA) address

/-- The byte of `callMemory input` at an address. -/
def callByte (input : List UInt8) (address : Nat) : Option UInt8 :=
  (fixedByte address).or (byteAt inputAddress input address)

theorem textBytes_length : textBytes.length = 1753 := by
  rw [textBytes, length_toList]
  decide

theorem pml4Bytes_length : pml4Bytes.length = 4096 := by
  simp only [pml4Bytes, List.length_append, List.length_map, List.length_range,
    List.length_replicate]

theorem pdptBytes_length : pdptBytes.length = 4096 := by
  simp only [pdptBytes, List.length_append, List.length_map, List.length_range,
    List.length_replicate]

theorem wordBytes_length (value : Nat) : (wordBytes value).length = 8 := by
  simp [wordBytes]

/-- `callMemory input` holds the bytes of `callByte input`. -/
theorem getElem?_callMemory (input : List UInt8) (hinput : input.length ≤ 0x1000)
    (address : BitVec 64) : (callMemory input)[address]? = callByte input address.toNat := by
  simp only [callMemory, callByte, fixedByte]
  rw [getElem?_insertMany_codeRange _ _ _ _ (by rw [textBytes_length]; decide),
    getElem?_insertMany_codeRange _ _ _ _ (by rw [pdptBytes_length]; decide),
    getElem?_insertMany_codeRange _ _ _ _ (by rw [pml4Bytes_length]; decide),
    getElem?_insertMany_codeRange _ _ _ _ (by rw [wordBytes_length]; decide),
    getElem?_insertMany_codeRange _ _ _ _ (by rw [List.length_replicate]; decide),
    getElem?_insertMany_codeRange _ _ _ _ (by rw [List.length_replicate]; decide),
    getElem?_insertMany_codeRange _ _ _ _ (by rw [List.length_replicate]; decide),
    getElem?_insertMany_codeRange _ _ _ _ (by simp [inputAddress]; omega),
    Ram.empty, Std.ExtHashMap.getElem?_empty, Option.or_none]
  simp only [Option.or_assoc]

theorem programImage_eq : Program.Extracted.programImage =
    codeRange (BitVec.ofNat 64 0x100000) textBytes := by
  simp [Program.Extracted.programImage, Program.Extracted.programSections,
    ImageSections.toCodeMap, ImageSection.toCodeMap, textBytes, Program.Extracted.textAddress]

/--
The general-purpose registers of a call, in `Syntax.Reg.fin` order: the arguments in RDI, RSI,
RDX, RCX and R8, `stackPointer` in RSP, and distinct nonzero entry values in the others.
-/
def callRegisters (input : List UInt8) (outputCapacity : Nat) : Vector (BitVec 64) 16 :=
  #v[0x0F0E0D0C0B0A0908, BitVec.ofNat 64 outputAddress, BitVec.ofNat 64 lengthAddress,
    0x3F3E3D3C3B3A3938, BitVec.ofNat 64 stackPointer, 0x5F5E5D5C5B5A5958,
    BitVec.ofNat 64 input.length, BitVec.ofNat 64 inputAddress,
    BitVec.ofNat 64 outputCapacity, 0x9F9E9D9C9B9A9998, 0xAFAEADACABAAA9A8, 0xBFBEBDBCBBBAB9B8,
    0xCFCECDCCCBCAC9C8, 0xDFDEDDDCDBDAD9D8, 0xEFEEEDECEBEAE9E8, 0xFFFEFDFCFBFAF9F8]

/-- The user profile with the page tables at `0x1000` and CR4.OSFXSR and CR4.OSXMMEXCPT set. -/
def baseState : RamState :=
  { Profile.initialState .user (fun _ => false) Ram.empty (Vector.replicate 16 0) 0
      ⟨false, false, false, false, false, false, false⟩ (BitVec.ofNat 64 tableBase) 0 with
    CR4 := 0x620 }

/--
The initial state of a call of `routine` on `input` with `outputCapacity` in R8, with the RAM
that the module documentation describes.
-/
def callState (routine : Program.Routine) (input : List UInt8) (outputCapacity : Nat) :
    RamState :=
  { baseState with
    GPR := embedGPR (callRegisters input outputCapacity)
    RIP := routine.entryAddress
    Next_IP := routine.entryAddress
    external := callMemory input }


/-! ## Memory type -/

section
open X86.Runtime X86.Helpers
open scoped X86.Runtime.Syntax

/-- The memory-type inputs that lean-x86 reads from `witnessProcessor` and `baseState`. -/
def memoryTypeInputs : Memory_Type_Inputs where
  IA32_MTRRCAP := 0x508
  IA32_MTRR_DEF_TYPE := 0x806
  IA32_PAT := 0x0606060606060606
  MTRR_Fixed := Vector.replicate 11 0
  MTRR_Base := Vector.replicate 256 0
  MTRR_Mask := Vector.replicate 256 0
  Memory_Physical_Address_Bits := 52
  CR0 := 0x80010011
  Processor_Is_Atom := false
  CPUID_MTRR := true
  CPUID_PAT := true
  IA32_SMRR_PHYSBASE := 0
  IA32_SMRR_PHYSMASK := 0
  In_SMM := false

theorem pow52 : ((2 : Int) ** (52 : Int) : Except (Error Empty) Int) = pure (2 ^ 52) := rfl

theorem intSlice_addressMask :
    (intSlice (4503599627370495 : Int) 0 64 : Except (Error Empty) (Bits 64)) =
      pure 4503599627370495#64 := rfl

@[simp] theorem true_andOp (b : Bool) : (true &&& b) = b := rfl
@[simp] theorem false_andOp (b : Bool) : (false &&& b) = false := rfl
@[simp] theorem andOp_false (b : Bool) : (b &&& false) = false := by cases b <;> rfl
@[simp] theorem andOp_true (b : Bool) : (b &&& true) = b := by cases b <;> rfl
@[simp] theorem true_orOp (b : Bool) : (true ||| b) = true := rfl
@[simp] theorem false_orOp (b : Bool) : (false ||| b) = b := rfl

/-- An address below 4 GiB has no bit at or above bit 52. -/
theorem and_highMask_eq_zero (address : BitVec 64) (h : address.toNat < userAddressLimit) :
    (address &&& 18442240474082181120#64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (18442240474082181120#64).toNat = 4095 <<< 52 by rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_testBit]
  by_cases hi : 52 ≤ i
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide)
      (by omega)))]
    simp
  · simp [hi]

set_option maxRecDepth 20000 in
/-- With `memoryTypeInputs`, every address below 4 GiB is write-back at PAT selector 0. -/
theorem emulateGetMemoryType_memoryTypeInputs (address : BitVec 64)
    (h : address.toNat < userAddressLimit) :
    Emulate_Get_Memory_Type memoryTypeInputs address 0 =
      .ok ⟨false, .Memory_Type_Write_Back⟩ := by
  unfold Emulate_Get_Memory_Type Emulate_Memory.Normal_Type Emulate_Memory.MTRR_Type
    Emulate_Memory.SMRR_Matches
  have h1 : memoryTypeInputs.Memory_Physical_Address_Bits = 52 := rfl
  have h2 : memoryTypeInputs.IA32_MTRR_DEF_TYPE = 0x806 := rfl
  have h3 : memoryTypeInputs.IA32_MTRRCAP = 0x508 := rfl
  have h4 : memoryTypeInputs.IA32_PAT = 0x0606060606060606 := rfl
  have h5 : memoryTypeInputs.CR0 = 0x80010011 := rfl
  have h6 : memoryTypeInputs.IA32_SMRR_PHYSMASK = 0 := rfl
  simp only [h1, h2, h3, h4, h5, h6]
  simp [pow52, intSlice_addressMask, and_highMask_eq_zero address h, CheckedSlice.read, slice,
    assert, intRange, List.range_succ, Array.get, memoryTypeInputs]
  rfl

/--
A memory-type lookup returns the type that `Emulate_Get_Memory_Type` selects from the inputs that
lean-x86 reads, when that selection needs no cache-disabled binding.
-/
theorem lookup_eq_of_inputs {σ : Type} (processor : Processor) {_ : MemoryType.Config}
    {_ : Bindings.CacheControl} (s : X86.State σ) (address : BitVec 64) (pat : BitVec 3)
    (inputs : Memory_Type_Inputs) (kind : Memory_Type)
    (hinputs : Bindings.MemoryType.inputsOfState processor s = .ok inputs)
    (hmtrr : inputs.CPUID_MTRR = true) (hpat : inputs.CPUID_PAT = true)
    (hselect : Emulate_Get_Memory_Type inputs address pat = .ok ⟨false, kind⟩) :
    Bindings.MemoryType.lookup processor s address pat = .ok kind := by
  unfold Bindings.MemoryType.inputsOfState at hinputs
  unfold Bindings.MemoryType.lookup Get_Memory_Type Resolve_Memory_Type
  simp only [] at hinputs ⊢
  letI : X86.Config := processor.config
  letI := processor.cpuidBinding (σ := σ)
  letI := processor.processorTypeBinding
  rcases run : ExceptT.run Emulate_Memory.Read_Type_Inputs s with ⟨result, after⟩
  rw [run] at hinputs
  simp only at hinputs
  subst hinputs
  change Emulate_Memory.Read_Type_Inputs s = _ at run
  simp [bind, ExceptT.bind, StateT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, run, pure,
    ExceptT.pure, hmtrr, hpat, liftM, monadLift, MonadLift.monadLift, hselect]
  rfl

end

/-! ## Processor checks -/

/-- The answer that `Prelude.ReportsCPUFeature processor s feature` asks about, if any. -/
def cpuFeature (processor : Processor) (s : RamState) (feature : CPUID_Feature) : Option Bool :=
  letI := processor.cpuidBinding (σ := Ram)
  ((Read_CPUID_Feature feature).run s).1.toOption

/--
The facts about `s` that need `witnessProcessor`: its CPUID reads of SSE, LAM, LASS and LZCNT,
and the memory-type inputs it gives with the default memory-type configuration.
-/
def processorChecks (s : RamState) : Bool :=
  cpuFeature witnessProcessor s CPUID_SSE_Encoding == some true &&
  cpuFeature witnessProcessor s CPUID_LAM_Encoding == some false &&
  cpuFeature witnessProcessor s CPUID_LASS_Encoding == some false &&
  (cpuFeature witnessProcessor s CPUID_LZCNT_Encoding).isSome &&
  (@Bindings.MemoryType.inputsOfState Ram witnessProcessor MemoryType.Config.default s).toOption ==
    some memoryTypeInputs

theorem eq_ok_of_toOption {ε α : Type} {result : Except ε α} {value : α}
    (h : result.toOption = some value) : result = .ok value := by
  cases result <;> simp_all [Except.toOption]

theorem processorChecks_spec {s : RamState} (h : processorChecks s = true) :
    ReportsCPUFeature witnessProcessor s CPUID_SSE_Encoding true ∧
    ReportsCPUFeature witnessProcessor s CPUID_LAM_Encoding false ∧
    ReportsCPUFeature witnessProcessor s CPUID_LASS_Encoding false ∧
    LeadingZeroCountReported (modelBindings witnessProcessor) s ∧
    @Bindings.MemoryType.inputsOfState Ram witnessProcessor MemoryType.Config.default s =
      .ok memoryTypeInputs := by
  simp only [processorChecks, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hsse, hlam⟩, hlass⟩, hlzcnt⟩, hinputs⟩ := h
  exact ⟨hsse, hlam, hlass, Option.isSome_iff_exists.mp hlzcnt, eq_ok_of_toOption hinputs⟩

theorem writeBackMemoryType {s : RamState} (h : processorChecks s = true) :
    WriteBackMemoryType (modelBindings witnessProcessor) s 0 := fun address haddress =>
  lookup_eq_of_inputs witnessProcessor s address 0 memoryTypeInputs _
    (processorChecks_spec h).2.2.2.2 rfl rfl
    (emulateGetMemoryType_memoryTypeInputs address haddress)


/-! ## Facts about the base state -/

theorem baseState_cpl : 0 ≤ baseState.CPL ∧ baseState.CPL ≤ 3 := by
  decide +kernel

theorem baseState_flags : baseState.RFLAGS.TF = 0 ∧ baseState.RFLAGS.RF = 0 ∧
    baseState.RFLAGS.DF = 0 := by
  decide +kernel

theorem baseState_cr0 : SupportedIntegerCR0 baseState.CR0 ∧ CR0.SSEEnabled baseState.CR0 := by
  have h : baseState.CR0.PE = 1 ∧ baseState.CR0.PG = 1 ∧ baseState.CR0.NW = 0 ∧
      baseState.CR0.CD = 0 ∧ baseState.CR0.AM = 0 ∧ baseState.CR0.EM = 0 ∧
      baseState.CR0.TS = 0 := by
    decide +kernel
  obtain ⟨pe, pg, nw, cd, am, em, ts⟩ := h
  exact ⟨⟨⟨pe, pg⟩, ⟨nw, cd⟩, ⟨am⟩⟩, ⟨em, ts⟩⟩

theorem baseState_cr4 : SupportedIntegerCR4 baseState.CR4 ∧ CR4.SSEEnabled baseState.CR4 := by
  have h : baseState.CR4.PAE = 1 ∧ baseState.CR4.LA57 = 0 ∧ baseState.CR4.VME = 0 ∧
      baseState.CR4.PVI = 0 ∧ baseState.CR4.SMEP = 0 ∧ baseState.CR4.SMAP = 0 ∧
      baseState.CR4.PKE = 0 ∧ baseState.CR4.CET = 0 ∧ baseState.CR4.OSFXSR = 1 ∧
      baseState.CR4.OSXMMEXCPT = 1 := by
    decide +kernel
  obtain ⟨pae, la57, vme, pvi, smep, smap, pke, cet, osfxsr, osxmmexcpt⟩ := h
  exact ⟨⟨⟨pae, la57⟩, ⟨vme, pvi⟩, ⟨smep⟩, ⟨smap⟩, ⟨pke⟩, ⟨cet⟩⟩, ⟨osfxsr, osxmmexcpt⟩⟩

theorem baseState_efer : SupportedIntegerEFER baseState.IA32_EFER := by
  have h : baseState.IA32_EFER.LME = 1 ∧ baseState.IA32_EFER.LMA = 1 ∧
      baseState.IA32_EFER.NXE = 0 := by
    decide +kernel
  exact ⟨⟨h.1, h.2.1⟩, ⟨h.2.2⟩⟩

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]


/-- `Machine.loadBytes` over a byte function instead of RAM. -/
def loadFrom (lookup : Nat → Option UInt8) (address : BitVec 64) (count : Nat) :
    Except Machine.Fault (BitVec 64) :=
  loop count 0 0 0
where
  /-- `Machine.loadBytes.loop` over `lookup`. -/
  loop : Nat → Nat → Nat → Nat → Except Machine.Fault (BitVec 64)
    | 0, _, _, accumulator => .ok (Machine.fromNat accumulator)
    | remaining + 1, current, shift, accumulator =>
      match lookup (Machine.addAddress address current).toNat with
      | none => .error (.unmappedMemory (Machine.addAddress address current))
      | some byte =>
        loop remaining (current + 1) (shift + 8) (accumulator + byte.toNat * 2 ^ shift)

theorem loadBytes_eq_loadFrom (memory : Ram) (lookup : Nat → Option UInt8)
    (address : BitVec 64) (count : Nat)
    (hlookup : ∀ current < count, memory[Machine.addAddress address current]? =
      lookup (Machine.addAddress address current).toNat) :
    Machine.loadBytes memory address count = loadFrom lookup address count := by
  unfold Machine.loadBytes loadFrom
  suffices ∀ remaining current shift accumulator, current + remaining ≤ count →
      Machine.loadBytes.loop memory address remaining current shift accumulator =
        loadFrom.loop lookup address remaining current shift accumulator from
    this _ _ _ _ (by omega)
  intro remaining
  induction remaining with
  | zero => intros; rfl
  | succ remaining ih =>
    intro current shift accumulator hle
    simp only [Machine.loadBytes.loop, loadFrom.loop, hlookup current (by omega)]
    rcases lookup (Machine.addAddress address current).toNat with _ | byte
    · rfl
    · exact ih (current + 1) _ _ (by omega)


/-! ## Facts about the initial states -/

section
variable (routine : Program.Routine) (input : List UInt8) (outputCapacity : Nat)

theorem callState_rdi : (callState routine input outputCapacity).regValue .rdi =
    BitVec.ofNat 64 inputAddress := by
  simp only [callState, X86.State.regValue, embedGPR, Vector.getElem_ofFn]; rfl

theorem callState_rsi : (callState routine input outputCapacity).regValue .rsi =
    BitVec.ofNat 64 input.length := by
  simp only [callState, X86.State.regValue, embedGPR, Vector.getElem_ofFn]; rfl

theorem callState_rdx : (callState routine input outputCapacity).regValue .rdx =
    BitVec.ofNat 64 lengthAddress := by
  simp only [callState, X86.State.regValue, embedGPR, Vector.getElem_ofFn]; rfl

theorem callState_rcx : (callState routine input outputCapacity).regValue .rcx =
    BitVec.ofNat 64 outputAddress := by
  simp only [callState, X86.State.regValue, embedGPR, Vector.getElem_ofFn]; rfl

theorem callState_r8 : (callState routine input outputCapacity).regValue .r8 =
    BitVec.ofNat 64 outputCapacity := by
  simp only [callState, X86.State.regValue, embedGPR, Vector.getElem_ofFn]; rfl

theorem callState_rsp : (callState routine input outputCapacity).regValue .rsp =
    BitVec.ofNat 64 stackPointer := by
  simp only [callState, X86.State.regValue, embedGPR, Vector.getElem_ofFn]; rfl

end

theorem fixedByte_pml4 : ∀ i : Fin 8, fixedByte (0x1000 + i.val) =
    some (UInt8.ofNat ((0x2027 : Nat) >>> (8 * i.val) % 256)) := by
  decide +kernel

theorem fixedByte_pdpt : ∀ page : Fin 4, ∀ i : Fin 8,
    fixedByte (0x2000 + 8 * page.val + i.val) =
      some (UInt8.ofNat (((page.val <<< 30 ||| 0xe7) : Nat) >>> (8 * i.val) % 256)) := by
  decide +kernel

theorem callByte_of_fixedByte (input : List UInt8) {address : Nat} {byte : UInt8}
    (h : fixedByte address = some byte) : callByte input address = some byte := by
  simp only [callByte, h, Option.some_or]

/-- `fixedByte` has no byte where the input is. -/
theorem fixedByte_input {address : Nat} (hlow : inputAddress ≤ address)
    (hhigh : address < inputAddress + 0x1000) : fixedByte address = none := by
  unfold inputAddress at hlow hhigh
  have htext : byteAt 0x100000 textBytes address = none :=
    byteAt_eq_none (by rw [textBytes_length]; omega)
  have hpdpt : byteAt 0x2000 pdptBytes address = none :=
    byteAt_eq_none (by rw [pdptBytes_length]; omega)
  have hpml4 : byteAt 0x1000 pml4Bytes address = none :=
    byteAt_eq_none (by rw [pml4Bytes_length]; omega)
  have hword : byteAt stackPointer (wordBytes returnAddress) address = none :=
    byteAt_eq_none (by rw [wordBytes_length]; unfold stackPointer stackTop; omega)
  have hstack : byteAt (stackTop - stackAllocation) (List.replicate stackAllocation 0xCC)
      address = none :=
    byteAt_eq_none (by rw [List.length_replicate]; unfold stackTop stackAllocation; omega)
  have hlength : byteAt lengthAddress (List.replicate 8 0xBB) address = none :=
    byteAt_eq_none (by rw [List.length_replicate]; unfold lengthAddress; omega)
  have houtput : byteAt outputAddress (List.replicate outputAllocation 0xAA) address = none :=
    byteAt_eq_none (by rw [List.length_replicate]; unfold outputAddress; omega)
  simp only [fixedByte, htext, hpdpt, hpml4, hword, hstack, hlength, houtput, Option.none_or]

/-- Every address of a replicated layer of `fixedByte` has a byte. -/
theorem fixedByte_isSome_of_layer {address : Nat}
    (h : (outputAddress ≤ address ∧ address < outputAddress + outputAllocation) ∨
      (lengthAddress ≤ address ∧ address < lengthAddress + 8) ∨
      (stackTop - stackAllocation ≤ address ∧ address < stackTop)) :
    (fixedByte address).isSome := by
  simp only [fixedByte, Option.isSome_or]
  rcases h with ⟨hlow, hhigh⟩ | ⟨hlow, hhigh⟩ | ⟨hlow, hhigh⟩
  · rw [byteAt_replicate 0xAA hlow hhigh]
    simp
  · rw [byteAt_replicate 0xBB hlow hhigh]
    simp
  · rw [byteAt_replicate 0xCC hlow (by unfold stackTop stackAllocation at *; omega)]
    simp

theorem allocated_of_fixedByte {input : List UInt8} (hinput : input.length ≤ 0x1000)
    {region : MemoryRegion} (h : ∀ address, region.start ≤ address →
      address < region.start + region.size → (fixedByte address).isSome) :
    region.Allocated (callMemory input) := by
  intro address hcontains
  simp only [MemoryRegion.Contains] at hcontains
  rw [getElem?_callMemory _ hinput]
  obtain ⟨byte, hbyte⟩ := Option.isSome_iff_exists.mp (h _ hcontains.1 hcontains.2)
  exact ⟨byte, callByte_of_fixedByte input hbyte⟩

/-- The return-address word at `stackPointer`. -/
def wordByte (address : Nat) : Option UInt8 :=
  byteAt stackPointer (wordBytes returnAddress) address

theorem callByte_word (input : List UInt8) {address : Nat} (hlow : stackPointer ≤ address)
    (hhigh : address < stackPointer + 8) : callByte input address = wordByte address := by
  unfold stackPointer stackTop at hlow hhigh
  have hword : (wordByte address).isSome := by
    have hall : ∀ k : Fin 8, (wordByte (0x800000 - 8 + k.val)).isSome := by decide +kernel
    simpa [show 0x800000 - 8 + (address - (0x800000 - 8)) = address by omega] using
      hall ⟨address - (0x800000 - 8), by omega⟩
  obtain ⟨byte, hbyte⟩ := Option.isSome_iff_exists.mp hword
  have htext : byteAt 0x100000 textBytes address = none :=
    byteAt_eq_none (by rw [textBytes_length]; omega)
  have hpdpt : byteAt 0x2000 pdptBytes address = none :=
    byteAt_eq_none (by rw [pdptBytes_length]; omega)
  have hpml4 : byteAt 0x1000 pml4Bytes address = none :=
    byteAt_eq_none (by rw [pml4Bytes_length]; omega)
  simp only [callByte, fixedByte, htext, hpdpt, hpml4, Option.none_or]
  rw [show byteAt stackPointer (wordBytes returnAddress) address = wordByte address from rfl, hbyte]
  rfl

theorem loadFrom_wordByte :
    (loadFrom wordByte (BitVec.ofNat 64 stackPointer) 8).toOption =
      some (BitVec.ofNat 64 returnAddress) := by
  decide +kernel

theorem inProgram_range {address : BitVec 64} (h : Program.InProgram address) :
    address.toNat < 0x100000 + 1753 := by
  obtain ⟨byte, hmem⟩ := h
  rw [programImage_eq] at hmem
  have := lt_of_byteAt_eq_some (byteAt_of_mem_codeRange (by rw [textBytes_length]; decide) hmem)
  rw [textBytes_length] at this
  omega

theorem avoids_reserved {region : MemoryRegion} (hstart : 0x100000 + 1753 ≤ region.start) :
    region.Avoids (fun address => Program.InProgram address ∨
      Program.pageTables.Contains address.toNat) := by
  intro address hcontains hforbidden
  simp only [MemoryRegion.Contains] at hcontains
  rcases hforbidden with hprogram | htables
  · have := inProgram_range hprogram
    omega
  · simp only [Program.pageTables, MemoryRegion.Contains] at htables
    omega

theorem disjoint_of_le {region region' : MemoryRegion}
    (h : region.start + region.size ≤ region'.start ∨
      region'.start + region'.size ≤ region.start) :
    region.Disjoint region' := by
  intro address hcontains hcontains'
  simp only [MemoryRegion.Contains] at hcontains hcontains'
  omega

theorem pairwiseDisjoint_three {region region' region'' : MemoryRegion}
    (h : region.Disjoint region') (h' : region.Disjoint region'')
    (h'' : region'.Disjoint region'') :
    MemoryRegion.PairwiseDisjoint #v[region, region', region''] := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only [Fin.mk_lt_mk] at hij
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
  · exact h
  · exact h'
  · exact h''

/-- The page tables of every `callState` are those of `Prelude.IdentityMappedMemory`. -/
theorem callState_identityMappedMemory (routine : Program.Routine) (input : List UInt8)
    (outputCapacity : Nat) (hinput : input.length ≤ 0x1000) :
    IdentityMappedMemory (callState routine input outputCapacity) where
  cr3 := rfl
  tables := by
    refine ⟨fun i => ?_, fun page i => ?_⟩
    · rw [show (callState routine input outputCapacity).external = callMemory input from rfl,
        getElem?_callMemory _ hinput, toNat_ofNat_of_lt (by omega)]
      exact callByte_of_fixedByte input (fixedByte_pml4 i)
    · rw [show (callState routine input outputCapacity).external = callMemory input from rfl,
        getElem?_callMemory _ hinput, toNat_ofNat_of_lt (by omega)]
      exact callByte_of_fixedByte input (fixedByte_pdpt page i)

/-- A `callState` whose processor checks pass is a supported machine state. -/
theorem callState_supportedIntegerMachineState (routine : Program.Routine) (input : List UInt8)
    (outputCapacity : Nat) (hinput : input.length ≤ 0x1000)
    (hchecks : processorChecks (callState routine input outputCapacity) = true) :
    SupportedIntegerMachineState witnessProcessor (callState routine input outputCapacity) := by
  obtain ⟨hsse, hlam, hlass, -, -⟩ := processorChecks_spec hchecks
  exact {
    integer := {
      cs := rfl, ss := rfl, ds := rfl, es := rfl
      cpl := baseState_cpl
      cr0 := baseState_cr0.1
      cr4 := baseState_cr4.1
      efer := baseState_efer
      maxPhysical := witnessProcessor_maxPhysical
      early := witnessProcessor_early
      lam := hlam
      lass := hlass
      debug := ⟨rfl⟩
      aet := rfl }
    sse := ⟨hsse, baseState_cr0.2, baseState_cr4.2⟩
    memory := callState_identityMappedMemory routine input outputCapacity hinput
    ready := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨baseState_flags.1⟩,
      ⟨baseState_flags.2.1⟩, rfl, rfl⟩ }

/-- `Prelude.MachineRamUnitStrideDecodable` for a `callState` whose processor checks pass. -/
theorem callState_decodable (routine : Program.Routine) (input : List UInt8)
    (outputCapacity : Nat)
    (hchecks : processorChecks (callState routine input outputCapacity) = true) :
    MachineRamUnitStrideDecodable (modelBindings witnessProcessor)
      (callState routine input outputCapacity) :=
  ⟨smrrUnblocked _ _, writeBackMemoryType hchecks, fun {_} _ _ _ _ => rfl,
    (processorChecks_spec hchecks).2.2.2.1⟩

/-! ## The regions of a call -/

section
variable (routine : Program.Routine) (input : List UInt8) (outputCapacity : Nat)

theorem callState_external : (callState routine input outputCapacity).external =
    callMemory input := rfl

theorem callState_inputRegion :
    Program.inputRegion (callState routine input outputCapacity) input.toByteArray =
      ⟨inputAddress, input.length⟩ := by
  simp only [Program.inputRegion, registerRegion, callState_rdi, List.size_toByteArray,
    toNat_ofNat_of_lt (show inputAddress < 2 ^ 64 by decide)]

theorem callState_lengthInputRegion :
    Program.lengthInputRegion (callState routine input outputCapacity) input.length =
      ⟨inputAddress, input.length⟩ := by
  simp only [Program.lengthInputRegion, registerRegion, callState_rdi,
    toNat_ofNat_of_lt (show inputAddress < 2 ^ 64 by decide)]

theorem callState_outputRegion (length : Nat) :
    Program.outputRegion (callState routine input outputCapacity) length =
      ⟨outputAddress, length⟩ := by
  simp only [Program.outputRegion, registerRegion, callState_rcx,
    toNat_ofNat_of_lt (show outputAddress < 2 ^ 64 by decide)]

theorem callState_lengthOutputRegion :
    Program.lengthOutputRegion (callState routine input outputCapacity) =
      ⟨lengthAddress, 8⟩ := by
  simp only [Program.lengthOutputRegion, registerRegion, callState_rdx,
    toNat_ofNat_of_lt (show lengthAddress < 2 ^ 64 by decide)]

theorem callState_rspNat :
    ((callState routine input outputCapacity).regValue .rsp).toNat = stackPointer := by
  rw [callState_rsp, toNat_ofNat_of_lt (by decide)]

theorem callState_stackRegion (stackBytes : Nat) (hstack : stackBytes ≤ stackAllocation - 8) :
    Stack.region (callState routine input outputCapacity) stackBytes =
      ⟨stackPointer - stackBytes, 8 + stackBytes⟩ := by
  simp only [Stack.region, callState_rspNat, Stack.returnAddressBytes, MemoryRegion.mk.injEq,
    true_and]
  unfold stackPointer stackTop
  unfold stackAllocation at hstack
  omega

theorem callState_programLoaded (hinput : input.length ≤ 0x1000) :
    Program.ProgramLoaded (callState routine input outputCapacity) := by
  intro address byte hmem
  rw [programImage_eq] at hmem
  rw [callState_external, getElem?_callMemory _ hinput]
  apply callByte_of_fixedByte input
  have htext := byteAt_of_mem_codeRange (by rw [textBytes_length]; decide) hmem
  simp only [fixedByte, htext, Option.some_or]

theorem callState_validInput (hinput : input.length ≤ 0x1000) :
    Program.ValidInput (callState routine input outputCapacity) input.toByteArray := by
  simp only [Program.ValidInput, callState_inputRegion]
  refine ⟨by decide, by simp only [MemoryRegion.Bounded, inputAddress, userAddressLimit]; omega,
    List.size_toByteArray, fun i => ?_⟩
  have hi : i.val < input.length := by simpa using i.isLt
  simp only
  rw [callState_external, getElem?_callMemory _ hinput, toNat_ofNat_of_lt
    (by unfold inputAddress; omega), callByte,
    fixedByte_input (by unfold inputAddress; omega) (by unfold inputAddress; omega),
    Option.none_or, List.getElem_toByteArray]
  simp only [byteAt, show inputAddress ≤ inputAddress + i.val by omega,
    show inputAddress + i.val < inputAddress + input.length by omega, and_self, ↓reduceIte,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi]

theorem callState_validLengthInput (hinput : input.length ≤ 0x1000) :
    Program.ValidLengthInput (callState routine input outputCapacity) input.length := by
  have hvalid := callState_validInput routine input outputCapacity hinput
  simp only [Program.ValidLengthInput, callState_lengthInputRegion]
  simp only [Program.ValidInput, callState_inputRegion] at hvalid
  obtain ⟨hnonnull, hbounded, -, hbytes⟩ := hvalid
  refine ⟨hnonnull, hbounded, fun address hcontains => ?_⟩
  simp only [MemoryRegion.Contains] at hcontains
  have hfin : address.toNat - inputAddress < input.toByteArray.size := by
    rw [List.size_toByteArray]; omega
  have hbyte := hbytes ⟨_, hfin⟩
  simp only [show inputAddress + (address.toNat - inputAddress) = address.toNat by omega,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] at hbyte
  exact ⟨_, hbyte⟩

theorem callState_validOutput (hinput : input.length ≤ 0x1000) (length : Nat)
    (hlength : length ≤ outputAllocation) :
    Program.ValidOutput (callState routine input outputCapacity) length := by
  simp only [Program.ValidOutput, callState_external, callState_outputRegion]
  refine ⟨by decide, by simp only [MemoryRegion.Bounded, outputAddress, userAddressLimit,
      outputAllocation] at *; omega,
    allocated_of_fixedByte hinput fun address hlow hhigh => fixedByte_isSome_of_layer ?_⟩
  simp only at hlow hhigh
  unfold outputAllocation at hlength
  unfold outputAllocation
  omega

theorem callState_validLengthOutput (hinput : input.length ≤ 0x1000) :
    Program.ValidLengthOutput (callState routine input outputCapacity) := by
  simp only [Program.ValidLengthOutput, callState_external, callState_lengthOutputRegion]
  refine ⟨by simp only [MemoryRegion.Bounded, lengthAddress, userAddressLimit]; omega,
    allocated_of_fixedByte hinput fun address hlow hhigh => fixedByte_isSome_of_layer ?_⟩
  simp only at hlow hhigh
  omega

theorem callState_validStack (hinput : input.length ≤ 0x1000) (stackBytes : Nat)
    (hstack : stackBytes ≤ stackAllocation - 8) :
    Stack.Valid (callState routine input outputCapacity) stackBytes := by
  simp only [Stack.Valid, callState_stackRegion routine input outputCapacity stackBytes hstack]
  simp only [callState_external, Stack.NoUnderflow, callState_rspNat, Stack.returnSlot,
    MemoryRegion.Aligned, Stack.callAlignment, Stack.returnAddressBytes]
  unfold stackAllocation at hstack
  unfold stackPointer stackTop
  refine ⟨by simp only [MemoryRegion.Bounded, userAddressLimit]; omega,
    allocated_of_fixedByte hinput fun address hlow hhigh => fixedByte_isSome_of_layer ?_,
    by omega, by decide⟩
  simp only [stackTop, stackAllocation] at hlow hhigh ⊢
  omega

theorem callState_validReturnAddress (hinput : input.length ≤ 0x1000) :
    Program.ValidReturnAddress (callState routine input outputCapacity) := by
  refine ⟨BitVec.ofNat 64 returnAddress, ⟨rfl, ?_⟩, by decide, fun hprogram => ?_⟩
  · simp only [Stack.returnSlot, callState_rspNat, callState_external]
    rw [loadBytes_eq_loadFrom _ wordByte _ _ fun current hcurrent => ?_]
    · exact eq_ok_of_toOption loadFrom_wordByte
    · have haddress : (Machine.addAddress (BitVec.ofNat 64 stackPointer) current).toNat =
          stackPointer + current := by
        simp only [Machine.addAddress, Machine.fromNat, BitVec.ofNat_add_ofNat]
        exact toNat_ofNat_of_lt (by unfold stackPointer stackTop; omega)
      rw [getElem?_callMemory _ hinput, haddress]
      exact callByte_word input (by omega) (by omega)
  · have := inProgram_range hprogram
    simp [returnAddress] at this

end

/-! ## The call predicates -/

/--
A `callState` is a valid call of `routine` for every `lengthWritten`, when the input fits its
4-KiB space, the capacity and the written length fit the output allocation and the routine's
stack budget fits below the return slot.
-/
theorem callState_validCall (routine : Program.Routine) (input : List UInt8)
    (outputCapacity writtenLength : Nat) (lengthWritten : Prop) (hinput : input.length ≤ 0x1000)
    (hcapacity : outputCapacity ≤ outputAllocation)
    (hwritten : writtenLength ≤ outputAllocation)
    (hstack : routine.minStackBytes ≤ stackAllocation - 8) :
    Program.ValidCall routine (callState routine input outputCapacity) input.toByteArray
      outputCapacity writtenLength lengthWritten := by
  have hstackRegion := callState_stackRegion routine input outputCapacity _ hstack
  unfold stackAllocation at hstack
  unfold outputAllocation at hcapacity hwritten
  exact {
    directionFlagUnset := ⟨baseState_flags.2.2⟩
    programLoaded := callState_programLoaded routine input outputCapacity hinput
    entry := rfl
    lengthArgumentMatchesInput := by
      rw [callState_rsi, toNat_ofNat_of_lt (by omega), List.size_toByteArray]
    capacityArgumentMatchesOutput := by
      rw [callState_r8, toNat_ofNat_of_lt (by omega)]
    inputInMemory := callState_validInput routine input outputCapacity hinput
    outputInMemory := callState_validOutput routine input outputCapacity hinput _ hcapacity
    lengthOutputInMemoryIfLengthWritten := fun _ =>
      callState_validLengthOutput routine input outputCapacity hinput
    stack := callState_validStack routine input outputCapacity hinput _ hstack
    separation := by
      simp only [Program.MemorySeparation, callState_inputRegion, callState_outputRegion,
        callState_lengthOutputRegion, hstackRegion]
      unfold inputAddress outputAddress lengthAddress stackPointer stackTop
      refine ⟨pairwiseDisjoint_three (disjoint_of_le (by simp only; omega))
        (disjoint_of_le (by simp only; omega)) (disjoint_of_le (by simp only; omega)),
        fun region hregion => ?_, fun _ => ⟨pairwiseDisjoint_three
          (disjoint_of_le (by simp only; omega)) (disjoint_of_le (by simp only; omega))
          (disjoint_of_le (by simp only; omega)), avoids_reserved (by simp only; omega)⟩⟩
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
        or_false] at hregion
      rcases hregion with rfl | rfl <;> exact avoids_reserved (by simp only; omega)
    returnAddress := callState_validReturnAddress routine input outputCapacity hinput }

/--
A `callState` is a valid length call of `routine` with `byteLength` the input's length, for
every `lengthWritten`, when the input fits its 4-KiB space and the routine's stack budget fits
below the return slot.
-/
theorem callState_validLengthCall (routine : Program.Routine) (input : List UInt8)
    (lengthWritten : Prop) (hinput : input.length ≤ 0x1000)
    (hstack : routine.minStackBytes ≤ stackAllocation - 8) :
    Program.ValidLengthCall routine (callState routine input 0) input.length lengthWritten := by
  have hstackRegion := callState_stackRegion routine input 0 _ hstack
  unfold stackAllocation at hstack
  exact {
    directionFlagUnset := ⟨baseState_flags.2.2⟩
    programLoaded := callState_programLoaded routine input 0 hinput
    entry := rfl
    lengthArgumentMatchesInput := by
      rw [callState_rsi, toNat_ofNat_of_lt (by omega)]
    inputInMemory := callState_validLengthInput routine input 0 hinput
    lengthOutputInMemoryIfLengthWritten := fun _ =>
      callState_validLengthOutput routine input 0 hinput
    stack := callState_validStack routine input 0 hinput _ hstack
    separation := by
      simp only [Program.LengthMemorySeparation, callState_lengthOutputRegion, hstackRegion]
      unfold lengthAddress stackPointer stackTop
      exact ⟨avoids_reserved (by simp only; omega),
        fun _ => ⟨disjoint_of_le (by simp only; omega), avoids_reserved (by simp only; omega)⟩⟩
    returnAddress := callState_validReturnAddress routine input 0 hinput }

/-! ## The witnesses -/

/-- `foobar`, the longest input of RFC 4648 section 10, as US-ASCII codes. -/
def foobar : List UInt8 :=
  "foobar".toList.map fun c => c.toNat.toUInt8

/-- The routines whose statements assume `Program.ValidCall`. -/
def validCallRoutines : List Program.Routine :=
  [Program.base16ctLowerEncode, Program.base16ctUpperEncode, Program.base16ctLowerEncodeStr,
    Program.base16ctUpperEncodeStr, Program.base16ctLowerDecode, Program.base16ctUpperDecode,
    Program.base16ctMixedDecode]

/-- The routines whose statements assume `Program.ValidLengthCall`. -/
def validLengthCallRoutines : List Program.Routine :=
  [Program.base16ctDecodedLen, Program.base16ctEncodedLen]

/-- The decidable facts that the witness theorems need about a routine's `callState`. -/
def witnessCheck (routine : Program.Routine) (outputCapacity : Nat) : Bool :=
  decide (routine.minStackBytes ≤ stackAllocation - 8) &&
    processorChecks (callState routine foobar outputCapacity)

/-- `witnessCheck` holds for every routine, at the capacity its witness uses. -/
theorem witnessCheck_routines :
    (∀ routine ∈ validCallRoutines, witnessCheck routine 12 = true) ∧
    ∀ routine ∈ validLengthCallRoutines, witnessCheck routine 0 = true := by
  decide +kernel

theorem foobar_length : foobar.length = 6 := by
  decide

/--
For each routine called through `Program.ValidCall`, every `writtenLength` up to 12 and every
`lengthWritten`, some bindings and initial state meet every hypothesis of its statement together
on the non-empty input `foobar` with a 12-byte output buffer.
-/
theorem validCall_satisfiable : ∀ routine ∈ validCallRoutines, ∀ writtenLength ≤ 12,
    ∀ lengthWritten : Prop,
    ∃ (bindings : Machine.Bindings) (initial : Machine.RamState),
      MachineRamUnitStrideDecodable bindings initial ∧
      SupportedIntegerMachineState bindings.processor initial ∧
      Program.ValidCall routine initial foobar.toByteArray 12 writtenLength lengthWritten := by
  intro routine hroutine writtenLength hwritten lengthWritten
  have h := witnessCheck_routines.1 routine hroutine
  simp only [witnessCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hinput : foobar.length ≤ 0x1000 := by rw [foobar_length]; decide
  exact ⟨modelBindings witnessProcessor, callState routine foobar 12,
    callState_decodable routine foobar 12 h.2,
    callState_supportedIntegerMachineState routine foobar 12 hinput h.2,
    callState_validCall routine foobar 12 writtenLength lengthWritten hinput (by decide)
      (by unfold outputAllocation; omega) h.1⟩

/--
For each routine called through `Program.ValidLengthCall` and every `lengthWritten`, some
bindings and initial state meet every hypothesis of its statement together with `byteLength` 6,
the length of `foobar`, whose bytes are in memory at `src`.
-/
theorem validLengthCall_satisfiable : ∀ routine ∈ validLengthCallRoutines,
    ∀ lengthWritten : Prop,
    ∃ (bindings : Machine.Bindings) (initial : Machine.RamState),
      MachineRamUnitStrideDecodable bindings initial ∧
      SupportedIntegerMachineState bindings.processor initial ∧
      Program.ValidLengthCall routine initial 6 lengthWritten := by
  intro routine hroutine lengthWritten
  have h := witnessCheck_routines.2 routine hroutine
  simp only [witnessCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hinput : foobar.length ≤ 0x1000 := by rw [foobar_length]; decide
  have hcall := callState_validLengthCall routine foobar lengthWritten hinput h.1
  rw [foobar_length] at hcall
  exact ⟨modelBindings witnessProcessor, callState routine foobar 0,
    callState_decodable routine foobar 0 h.2,
    callState_supportedIntegerMachineState routine foobar 0 hinput h.2, hcall⟩

end Base16ct.Tests.CallWitness
