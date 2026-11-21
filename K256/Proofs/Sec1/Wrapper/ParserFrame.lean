import K256.Proofs.Sec1.Parser.Memory

set_option autoImplicit false

namespace K256.Proofs.Sec1.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.Lift K256.Proofs.Refine
  Sec1.LIR

theorem parserArgs_get (s : RamState) (i : Fin 53) :
    (parserArgs s)[i.val] =
      if i.val = 14 then ⟨64, s.regValue .rdi⟩
      else if i.val = 7 then ⟨64, s.regValue .rsp - 112⟩
      else if i.val = 4 then ⟨64, s.regValue .rsp - 256⟩
      else (Reg.ofIndex i).read s := by
  simp only [parserArgs, Vector.getElem_set, Lifted.locationOf, Vector.getElem_ofFn, eq_comm]

theorem parserMemory_load (s : RamState) :
    let sp := s.regValue .rsp
    let mem := parserMemory s
    memLoad mem (sp - 256) 64 = 0x101dea ∧
    memLoad mem (sp - 16) 64 = s.regValue .rbx ∧
    memLoad mem (sp - 8) 64 = s.regValue .r14 ∧
    memLoad mem sp 64 = (returnBoundary s).rip := by
  intro sp mem
  have apart (a b : BitVec 64) (h : 8 ≤ (a - b).toNat ∧ 8 ≤ (b - a).toNat) :
      RangeApart (sp - a) 8 (sp - b) 8 := by
    apply RangeApart.of_offsets (addr_sub sp a) (addr_sub sp b)
    rwa [show 0 - b - (0 - a) = a - b by bv_omega,
      show 0 - a - (0 - b) = b - a by bv_omega]
  have returnApart (a : BitVec 64) (h : 8 ≤ (a - 0).toNat ∧ 8 ≤ (0 - a).toNat) :
      RangeApart (sp - a) 8 sp 8 := by
    apply RangeApart.of_offsets (addr_sub sp a) (addr_self sp)
    rwa [show 0 - (0 - a) = a - 0 by bv_omega,
      show 0 - a - 0 = 0 - a by bv_omega]
  dsimp only [mem, parserMemory]
  refine ⟨memLoad_memStore_same _ _ _ (by decide) (by decide), ?_, ?_, ?_⟩
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apart 256 16 (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (apart 256 8 (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (apart 16 8 (by decide))]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (returnApart 256 (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (returnApart 16 (by decide)),
      memLoad_memStore_of_rangeApart _ _ _ _ _ (returnApart 8 (by decide))]
    rfl

theorem parserEntryWritable {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) :
    let sp := s.regValue .rsp - 256
    let dst := s.regValue .rsp - 112
    let mem := parserMemory s
    Writable Extracted.programImage mem (sp - 1672) 1672 ∧
    Writable Extracted.programImage mem dst 96 ∧ Readable mem sp 8 := by
  have frame := Parser.parserMemory_frame call
  intro sp dst mem
  refine ⟨?_, (stackWritable call (offset := 112) (by decide) (by decide) (by decide)).of_frame frame,
    ((stackWritable call (offset := 256) (by decide) (by decide) (by decide)).of_frame frame).readable⟩
  change Writable Extracted.programImage (parserMemory s) (s.regValue .rsp - 256 - 1672) 1672
  rw [BitVec.sub_sub]
  exact (stackWritable call (offset := 1928) (by decide) (by decide) (by decide)).of_frame frame

theorem parserOutputApart (sp : BitVec 64) :
    RangeApart (sp - 112) 96 (sp - 1928) 1680 :=
  RangeApart.of_offsets (addr_sub sp 112) (addr_sub sp 1928) (by decide)

theorem parserInput {s : RamState} {bytes : ByteArray} {mem : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (frame : RamWriteFrame s.external mem [Stack.region s publicKeyFromSec1Bytes.minStackBytes]) :
    ((parserArgs s)[2].get 64).toNat = bytes.size ∧
    (parserArgs s)[6].get 64 = s.regValue .rsi ∧
    Readable mem (s.regValue .rsi) bytes.size ∧
    (registerRegion s .rsi bytes.size).HasBytes mem bytes ∧
    (∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2) := by
  have ⟨content, loaded⟩ := Parser.inputs_of_stackFrame call frame
  refine ⟨?_, ?_, ?_, content, loaded⟩
  · have h : (parserArgs s)[2] = (Reg.ofIndex 2).read s := parserArgs_get s 2
    rw [h]
    exact call.lengthArgumentsMatchInputs.1
  · have h : (parserArgs s)[6] = (Reg.ofIndex 6).read s := parserArgs_get s 6
    rw [h]
    rfl
  · have valid : ValidInput s (registerRegion s .rsi bytes.size) bytes := call.inputsInMemory.1
    simpa only [registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      Readable.of_hasBytes content valid.2.1

theorem parserInputOutside {s : RamState} {bytes : ByteArray} {regions : List MemoryRegion}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (nonempty : 0 < bytes.size)
    (inside : RegionsWithin regions [Stack.region s publicKeyFromSec1Bytes.minStackBytes]) :
    Outside regions (s.regValue .rsi) bytes.size := by
  let stk := Stack.region s publicKeyFromSec1Bytes.minStackBytes
  let input := registerRegion s .rsi bytes.size
  have valid : ValidInput s input bytes := call.inputsInMemory.1
  have sep : MemorySeparation [outputRegion publicKeyFromSec1Bytes s, stk] [input] :=
    call.separation
  have apart := (sep.2 stk (by simp)).2 input List.mem_cons_self
  have hInput : input.start + input.size < 2^32 := valid.2.1
  have stackPositive : 0 < stk.size := by
    change 0 < (s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 1928)
    omega
  refine ⟨by change input.start + input.size ≤ 2^64; omega, fun r hr => ?_⟩
  obtain ⟨r', h', lo, hi⟩ := inside r hr
  obtain rfl := List.mem_singleton.mp h'
  change input.start + input.size ≤ r.start ∨ r.start + r.size ≤ input.start
  rcases apart_of_disjoint apart stackPositive nonempty with h | h
  · exact Or.inr (Nat.le_trans hi h)
  · exact Or.inl (Nat.le_trans h lo)

end K256.Proofs.Sec1.Wrapper
