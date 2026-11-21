import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Outer.Serialize
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Outer.Pad
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Outer.Compress

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Outer

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad (padded)

def digest (innerHash outerHash : Array UInt32) : ByteArray :=
  serializeHash (Hkdf.Proofs.NIST.SHA256.compress outerHash
    (Hkdf.Proofs.NIST.Encoding.octetsToBits (padded (serializeHash innerHash))))

private theorem serializeABI {s t : RamState} {phase : Bool}
    (h : AgreesExcept (serializeComponents phase s) s t)
    (dir : RFLAGS.DirectionFlagClear s.RFLAGS) : PreservesABI s t := by
  apply abi_of_agreement h dir
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [serializeComponents]
  all_goals simp [serializeComponents]

theorem finalizeOuter [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat} {innerHash outerHash : Array UInt32}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (bound : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f3bd)
    (r13 : s.regValue .r13 = stackPtr s + 16) (r15 : s.regValue .r15 = stackPtr s + 144)
    (inner : HashStateAt s (stackPtr s + 144) innerHash)
    (outer : HashStateAt s (stackPtr s + 184) outerHash)
    (count : loadBytes s.external (stackPtr s + 216) 8 = .ok 1) :
    ∃ fuel t, Advances boundary fuel s t ∧ SavedFrame entry t boundary length ∧
      t.RIP = 0x10f53c ∧ stackPtr t = stackPtr s ∧ PreservesABI s t ∧
      MemoryWriteFrame s t (writeRegions (stackPtr s)) ∧
      (⟨(stackPtr t + 16).toNat, 32⟩ : MemoryRegion).HasBytes t.external
        (digest innerHash outerHash) := by
  obtain ⟨_, u, runU, savedU, pcU, spU, agreeU, innerBytes⟩ :=
    serializeAt pre pos bound saved false pc inner
  have writesU := serializeWrites false s
  have keepU (offset len : Nat) (bounded : offset + len ≤ 2^64) (after : 112 ≤ offset) :
      (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Agrees s u := by
    refine writesU.agrees agreeU bounded ?_ ?_
    · intro r member
      obtain rfl := List.mem_singleton.mp member
      decide
    · intro r member
      obtain rfl := List.mem_singleton.mp member
      exact .inr after
  have countU : slot u 216 = 1 := by
    change memLoad u.external (stackPtr u + 216) 64 = 1
    rw [spU]
    exact (agrees_memLoad (keepU 216 8 (by decide) (by decide))).trans
      (Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64 count)
  have outerU : HashStateAt u (stackPtr u + 184) outerHash := by
    rw [spU]
    exact Hkdf.Proofs.Common.hashState_of_bytes outer (keepU 184 32 (by decide) (by decide))
  have bytesU : (⟨(stackPtr u + 80).toNat, 32⟩ : MemoryRegion).HasBytes u.external
      (serializeHash innerHash) := by
    rw [spU]
    exact innerBytes
  have abiU := serializeABI agreeU saved.directionFlag
  have frameU := local_frame pre.call.stack saved.sp agreeU writesU (by
    intro r member
    obtain rfl := List.mem_singleton.mp member
    decide)
  obtain ⟨_, v, runV, savedV, pcV, spV, abiV, frameV, block, eighth, words⟩ :=
    padOuter pre pos bound savedU pcU (by rw [spU]; exact (abiU.1 .r15 (by simp)).trans r15)
      countU bytesU outerU
  have r13V : v.regValue .r13 = stackPtr v + 16 := by
    rw [spV, spU]
    exact (abiV.1 .r13 (by simp)).trans ((abiU.1 .r13 (by simp)).trans r13)
  obtain ⟨_, w, runW, savedW, pcW, spW, abiW, frameW, compressed⟩ :=
    compressOuter pre pos bound savedV pcV r13V block eighth words
  obtain ⟨_, t, runT, savedT, pcT, spT, agreeT, bytesT⟩ :=
    serializeAt pre pos bound savedW true pcW compressed
  have frameT := local_frame pre.call.stack savedW.sp agreeT (serializeWrites true w) (by
    intro r member
    obtain rfl := List.mem_singleton.mp member
    decide)
  have fullFrame : MemoryWriteFrame s t (writeRegions (stackPtr s)) := by
    rw [spU] at frameV
    rw [spV, spU] at frameW
    rw [spW, spV, spU] at frameT
    exact memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans frameU frameV) frameW)
      frameT
  refine ⟨_, t, ((runU.trans runV).trans runW).trans runT, savedT, pcT,
    spT.trans (spW.trans (spV.trans spU)), ?_, fullFrame, ?_⟩
  · exact preservesABI_trans (preservesABI_trans (preservesABI_trans abiU abiV) abiW)
      (serializeABI agreeT savedW.directionFlag)
  · rw [spT]
    exact bytesT

end Hkdf.Proofs.NewExpand.Expand.Finalize.Outer
