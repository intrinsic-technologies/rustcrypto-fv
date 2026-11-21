import ChaCha20Poly1305.Proofs.CoreContract

namespace ChaCha20Poly1305.Proofs.Core

open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract

def frameBytes : Nat := 0x1b8

def framePointer (s : RamState) : BitVec 64 := stackPtr s - BitVec.ofNat 64 frameBytes

def frameBase (s : RamState) : Nat := (stackPtr s).toNat - frameBytes

def slot (s : RamState) (offset : Nat) : MemoryRegion := ⟨frameBase s + offset, 8⟩

def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.rbx, 0x188), (.r12, 0x190), (.r13, 0x198), (.r14, 0x1a0), (.r15, 0x1a8), (.rbp, 0x1b0)]

structure Inv [bindings : Machine.Bindings] (s t : RamState) (outPtr : BitVec 64) (length : Nat) :
    Prop where
  environment : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  code : CodeIn Extracted.programImage t
  directionFlagUnset : DirectionFlagUnset t
  rsp : stackPtr t = framePointer s
  frame : MemoryWriteFrame s t
    #v[resultRegion s, messageRegion outPtr length, Stack.region s coreStackBytes]
  allocated : ∀ region ∈ coreWritten s outPtr length, region.Allocated t.external
  saved : ∀ entry ∈ savedRegisters, (slot s entry.2).Word64At t.external (s.regValue entry.1)
  returnAddress : (Stack.returnSlot s).Word64At t.external (returnBoundary s).rip

theorem read_unchanged [Machine.Bindings] {s t : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hFrame : MemoryWriteFrame s t
      #v[resultRegion s, messageRegion outPtr plaintext.size, Stack.region s coreStackBytes])
    {region : MemoryRegion} (hRegion : region ∈ coreRead s inPtr outPtr plaintext.size)
    (address : BitVec 64) (hAddress : region.Contains address.toNat) :
    t.external[address]? = s.external[address]? := by
  apply hFrame address
  intro written hWritten hContains
  have hList : written ∈ coreWritten s outPtr plaintext.size := by
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]
      at hWritten
    simp only [coreWritten, List.mem_cons, List.not_mem_nil, or_false]
    exact hWritten
  exact hPre.separation.2.1 written hList region hRegion address.toNat hContains hAddress

end ChaCha20Poly1305.Proofs.Core
