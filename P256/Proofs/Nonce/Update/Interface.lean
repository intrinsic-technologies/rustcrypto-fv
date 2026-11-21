import P256.Proofs.Nonce.UpdateValue.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure UpdateEmptyPre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (state : State) : Prop extends DrbgCalleePre s boundary 0x109f30 1856 state where
  inputCount : s.regValue .rdx = 0

structure UpdateSeedAt (s : RamState) (address : BitVec 64) (bytes : ByteArray) : Prop where
  bounded : ({ start := address.toNat, size := bytes.size } : MemoryRegion).Bounded
  allocated : ({ start := address.toNat, size := bytes.size } : MemoryRegion).Allocated s.external
  contents : ({ start := address.toNat, size := bytes.size } : MemoryRegion).HasBytes s.external bytes
  stateApart : MemoryRegion.Disjoint
    ({ start := address.toNat, size := bytes.size } : MemoryRegion) (registerRegion s .rdi 64)
  stackApart : MemoryRegion.Disjoint
    ({ start := address.toNat, size := bytes.size } : MemoryRegion) (Stack.region s 1856)

structure UpdateSeededPre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (state : State) (secret reduced : ByteArray) : Prop extends
    DrbgCalleePre s boundary 0x109f30 1856 state where
  secretSize : secret.size = 32
  reducedSize : reduced.size = 32
  inputCount : s.regValue .rdx = 3
  descriptorsBounded : (registerRegion s .rsi 48).Bounded
  descriptorsAllocated : (registerRegion s .rsi 48).Allocated s.external
  descriptorsStateApart : MemoryRegion.Disjoint (registerRegion s .rsi 48) (registerRegion s .rdi 64)
  descriptorsStackApart : MemoryRegion.Disjoint (registerRegion s .rsi 48) (Stack.region s 1856)
  seeds : ∃ secretPointer reducedPointer : BitVec 64,
    loadBytes s.external (s.regValue .rsi) 8 = .ok secretPointer ∧
    loadBytes s.external (s.regValue .rsi + 8) 8 = .ok (32 : BitVec 64) ∧
    loadBytes s.external (s.regValue .rsi + 16) 8 = .ok reducedPointer ∧
    loadBytes s.external (s.regValue .rsi + 24) 8 = .ok (32 : BitVec 64) ∧
    loadBytes s.external (s.regValue .rsi + 40) 8 = .ok (0 : BitVec 64) ∧
    UpdateSeedAt s secretPointer secret ∧ UpdateSeedAt s reducedPointer reduced

inductive UpdateInput where
  | empty
  | seeded (secret reduced : ByteArray)

def UpdateInput.seed : UpdateInput → ByteArray
  | .empty => ByteArray.empty
  | .seeded secret reduced => secret ++ reduced

def UpdateInput.nonempty : UpdateInput → Bool
  | .empty => false
  | .seeded _ _ => true

def UpdatePre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (state : State) : UpdateInput → Prop
  | .empty => UpdateEmptyPre s boundary state
  | .seeded secret reduced => UpdateSeededPre s boundary state secret reduced

theorem UpdatePre.drbg [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {state : State} {input : UpdateInput} (pre : UpdatePre s boundary state input) :
    DrbgCalleePre s boundary 0x109f30 1856 state := by
  cases input with
  | empty => exact pre.toDrbgCalleePre
  | seeded _ _ => exact pre.toDrbgCalleePre

end P256.Proofs.Nonce
