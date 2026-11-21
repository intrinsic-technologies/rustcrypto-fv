import Sha2.Proofs.Common.Machine.MemoryFrame
import Sha2.Proofs.Wrapper.Absorb.Partial.Call
import Sha2.Proofs.Wrapper.Absorb.Partial.Increment
import Sha2.Proofs.Wrapper.Absorb.Partial.Finish
import Sha2.Proofs.Wrapper.Absorb.CompressSetup

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb.Partial

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

structure Result [Bindings] (initial s t : RamState) (hash : Array UInt32) (chunk : ByteArray) (v : Variant := .sha256) : Prop where
  preserved : Preserved (v := v) initial t
  rip : t.RIP = (v.pc 0x14c)
  hashWords : HashStateAt t (stackPtr initial - 88)
    (NIST.SHA256.compress hash (NIST.Encoding.octetsToBits chunk))
  blocks : memLoad t.external (stackPtr initial - 56) 64 =
    memLoad s.external (stackPtr initial - 56) 64 + 1
  source : t.regValue .r13 = s.regValue .rbx
  savedRbp : t.regValue .rbp = s.regValue .rbp
  indexRegister : t.regValue .r14 = s.regValue .r14
  countRegister : t.regValue .r15 = s.regValue .r15
  tailLength : t.external[stackPtr initial - 89]? = some 0

theorem compress [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {hash : Array UInt32} {chunk : ByteArray}
    (ctx : Context (v := v) initial inputs) (input : Preserved (v := v) initial s) (rip : s.RIP = (v.pc 0x11f))
    (words : HashStateAt s (stackPtr initial - 88) hash)
    (bytes : (⟨(stackPtr initial - 152).toNat, 64⟩ : MemoryRegion).HasBytes s.external chunk) :
    ∃ t, Result (v := v) initial s t hash chunk := by
  obtain ⟨u, preservedU, ripU, blocksU, frameU⟩ := increment ctx input rip
  have wordsU : HashStateAt u (stackPtr initial - 88) hash :=
    hashState_of_bytes words (bytes_of_mem_frame frameU (by simp [Component.Covers]) (by unfold OffsetsApart; decide +kernel) (by cases v <;> decide))
  have bytesU : (⟨(stackPtr initial - 152).toNat, 64⟩ : MemoryRegion).HasBytes u.external chunk := by
    refine ⟨bytes.1, fun i => ?_⟩
    have hi : i.val < 64 := by have hsize : chunk.size = 64 := bytes.1; omega
    have byte := bytes.2 i
    change u.external[BitVec.ofNat 64 ((stackPtr initial - 152).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [bytes_of_mem_frame frameU (offset := 152) (len := 64)
      (by simp [Component.Covers]) (by unfold OffsetsApart; decide +kernel) (by cases v <;> decide) i.val hi]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte
  obtain ⟨mid, preservedV, effectV⟩ := register_block ctx preservedU
    (pc := (v.textOffset + 0x127)) (CompressSetup.run (returnBoundary initial)
      (validCall_returnBoundary ctx.machine ctx.call).2.2)
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel) ripU
    (by simp [CompressSetup.effect, Effect.components, Component.Covers])
    (by simp [CompressSetup.effect, Effect.components])
    (by simp [CompressSetup.effect, Effect.components])
  have frameV : AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] u mid := effectV.agrees
  have memoryV : mid.external = u.external := frameV.external (by simp [Component.Covers])
  have wordsV : HashStateAt mid (stackPtr initial - 88) hash :=
    hashState_of_bytes wordsU (fun i _ => by rw [memoryV])
  have bytesV : (⟨(stackPtr initial - 152).toNat, 64⟩ : MemoryRegion).HasBytes mid.external chunk := by
    rw [memoryV]
    exact bytesU
  have destinationV : mid.regValue .rdi = stackPtr initial - 88 :=
    effectV.writes.2.1.trans (stack_add preservedU.rsp (by cases v <;> decide))
  have sourceV : mid.regValue .rsi = stackPtr initial - 152 :=
    effectV.writes.2.2.trans (stack_add preservedU.rsp (by cases v <;> decide))
  obtain ⟨w, preservedW, ripW, wordsW, blocksW, abiW⟩ :=
    compression_call ctx preservedV wordsV effectV.rip destinationV sourceV effectV.writes.1 bytesV
  obtain ⟨t, preservedT, ripT, sourceT, tailT, frameT⟩ := finish ctx preservedW ripW
  have wordsT := hashState_of_bytes wordsW
    (bytes_of_mem_frame frameT (by simp [Component.Covers]) (by unfold OffsetsApart; decide +kernel) (by cases v <;> decide))
  have blocksT : memLoad t.external (stackPtr initial - 56) 64 =
      memLoad w.external (stackPtr initial - 56) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun value : Option UInt8 => value.getD 0)
      (bytes_of_mem_frame frameT (by simp [Component.Covers]) (offset := 56) (len := 8)
        (by unfold OffsetsApart; decide +kernel) (by cases v <;> decide) i hi)
  have beforeCall := frameU.trans frameV
  refine ⟨t, preservedT, ripT, wordsT, ?_, ?_, ?_, ?_, ?_, tailT⟩
  · rw [blocksT, blocksW, memoryV]
    exact blocksU
  · exact sourceT.trans ((abiW.1 .rbx (by simp)).trans
      (beforeCall.read (n := 64) (r := 3) (by simp)))
  · exact (frameT.read (n := 64) (r := 5) (by simp)).trans
      ((abiW.1 .rbp (by simp)).trans (beforeCall.read (n := 64) (r := 5) (by simp)))
  · exact (frameT.read (n := 64) (r := 14) (by simp)).trans
      ((abiW.1 .r14 (by simp)).trans (beforeCall.read (n := 64) (r := 14) (by simp)))
  · exact (frameT.read (n := 64) (r := 15) (by simp)).trans
      ((abiW.1 .r15 (by simp)).trans (beforeCall.read (n := 64) (r := 15) (by simp)))

end Sha2.Proofs.Wrapper.Absorb.Partial
