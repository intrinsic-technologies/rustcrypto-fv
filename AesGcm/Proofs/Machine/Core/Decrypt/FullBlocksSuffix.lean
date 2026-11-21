import AesGcm.Proofs.Machine.Core.Interface
import AesGcm.Proofs.Machine.Runtime.MemorySlices
import AesGcm.Proofs.Machine.Runtime.StackGeometry

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem fullBlocks_suffix {u : Bool} {code : CodeMap} {key : Vector UInt8 (AES16.variant u).keyBytes}
    {fr : Activation} {before after : Ram} {src dst : BitVec 64} {input : ByteArray} {n : Nat}
    (sized : n ≤ input.size) (room : fr.low.toNat + (if u then 2912 else 2384) ≤ fr.rsp.toNat)
    (buf : BufferIn before fr.r8 src dst input)
    (destWrite : Writable code before dst input.size)
    (schedule : AES16.ScheduleIn (AES16.variant u) key (fr.rdi + 32) before)
    (scheduleRead : Readable before (fr.rdi + 32) (16 * ((AES16.variant u).Nr + 1)))
    (stackSep : ∀ r ∈ [span (fr.rdi + 32) (16 * ((AES16.variant u).Nr + 1)), span src input.size],
      (callStack fr).Disjoint r)
    (descSep : ∀ r ∈ [span (fr.rdi + 32) (16 * ((AES16.variant u).Nr + 1)), span src input.size],
      (span fr.r8 24).Disjoint r)
    (destSep : (span dst input.size).Disjoint (span (fr.rdi + 32) (16 * ((AES16.variant u).Nr + 1))))
    (frame : RamWriteFrame before after
      [span (fr.rsp - BitVec.ofNat 64 (if u then 2912 else 2384)) ((if u then 2912 else 2384) - 100),
        span (fr.r8 + 8) 8, span dst n]) :
    AES16.ScheduleIn (AES16.variant u) key (fr.rdi + 32) after ∧
    Readable after (src + BitVec.ofNat 64 n) (input.size - n) ∧
    (span (src + BitVec.ofNat 64 n) (input.size - n)).HasBytes after (input.extract n input.size) ∧
    Writable code after (dst + BitVec.ofNat 64 n) (input.size - n) := by
  let window := if u then 2912 else 2384
  let scheduleBase := fr.rdi + 32
  let scheduleSize := 16 * ((AES16.variant u).Nr + 1)
  let stack := span (fr.rsp - BitVec.ofNat 64 window) (window - 100)
  let descriptor := span (fr.r8 + 8) 8
  let written := span dst n
  let tailSrc := src + BitVec.ofNat 64 n
  let tailDst := dst + BitVec.ofNat 64 n
  let tailSize := input.size - n
  obtain ⟨descRead, _, _, _, sourceRead, sourceBytes, buffers⟩ := buf
  have srcLow := sourceRead.low
  have dstLow := destWrite.readable.low
  have descLow := descRead.low
  have scheduleLow := scheduleRead.low
  have addr {base : BitVec 64} {off : Nat} (h : base.toNat + off < 2 ^ 64) :
      (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt h]
  have tailSrcNat : tailSrc.toNat = src.toNat + n := addr (by omega)
  have tailDstNat : tailDst.toNat = dst.toNat + n := addr (by omega)
  have descNat : (fr.r8 + 8).toNat = fr.r8.toNat + 8 := addr (off := 8) (by omega)
  have apart {whole part : MemoryRegion}
      (hwhole : whole ∈ [span scheduleBase scheduleSize, span src input.size])
      (inside : ∀ a, part.Contains a → whole.Contains a) (hprefix : part.Disjoint written) :
      ∀ r ∈ [stack, descriptor, written], part.Disjoint r := by
    intro r hr a ha hb
    rcases List.mem_cons.mp hr with rfl | hr
    · exact local_span_disjoint_external room (Nat.le_refl window) (Nat.sub_le _ _)
        (stackSep whole hwhole) a hb (inside a ha)
    rcases List.mem_cons.mp hr with rfl | hr
    · apply descSep whole hwhole a _ (inside a ha)
      change (fr.r8 + 8).toNat ≤ a ∧ a < (fr.r8 + 8).toNat + 8 at hb
      change fr.r8.toNat ≤ a ∧ a < fr.r8.toNat + 24
      omega
    · exact hprefix a ha (List.mem_singleton.mp hr ▸ hb)
  have prefixInside (a : Nat) (h : written.Contains a) : (span dst input.size).Contains a := by
    change dst.toNat ≤ a ∧ a < dst.toNat + n at h
    change dst.toNat ≤ a ∧ a < dst.toNat + input.size
    omega
  have tailInside (a : Nat) (h : (span tailSrc tailSize).Contains a) :
      (span src input.size).Contains a := by
    change tailSrc.toNat ≤ a ∧ a < tailSrc.toNat + (input.size - n) at h
    change src.toNat ≤ a ∧ a < src.toNat + input.size
    omega
  have tailApart : (span tailSrc tailSize).Disjoint written := by
    intro a ht hp
    rcases buffers with same | separate
    · change tailSrc.toNat ≤ a ∧ _ at ht
      change _ ∧ a < dst.toNat + n at hp
      rw [tailSrcNat, same] at ht
      omega
    · exact separate a (tailInside a ht) (prefixInside a hp)
  change AES16.ScheduleIn (AES16.variant u) key scheduleBase after ∧
    Readable after tailSrc tailSize ∧ (span tailSrc tailSize).HasBytes after (input.extract n input.size) ∧
    Writable code after tailDst tailSize
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro round plane
    have roundLt := round.isLt
    have planeLt := plane.isLt
    let offset := 16 * round.val + 2 * plane.val
    let word := scheduleBase + BitVec.ofNat 64 offset
    have offsetBound : offset + 2 ≤ scheduleSize := by
      dsimp only [offset, scheduleSize]
      omega
    change scheduleBase.toNat + scheduleSize ≤ 2 ^ 32 at scheduleLow
    have wordNat : word.toNat = scheduleBase.toNat + offset := addr (by omega)
    have wordInside (a : Nat) (h : (span word 2).Contains a) :
        (span scheduleBase scheduleSize).Contains a := by
      simp only [MemoryRegion.Contains, span, wordNat] at h ⊢
      omega
    change memLoad after word 16 = _
    exact (memLoad_eq_of_disjoint frame (by change word.toNat + 2 ≤ 2 ^ 64; omega)
      (apart List.mem_cons_self wordInside
        (fun a ha hb => destSep a (prefixInside a hb) (wordInside a ha)))).trans
      (schedule round plane)
  · exact (sourceRead.of_frame frame).sub (by rw [tailSrcNat]; omega)
      (by rw [tailSrcNat]; dsimp only [tailSize]; omega)
  · have tail := hasBytes_extract sourceBytes n input.size sized (Nat.le_refl _) (by omega)
    exact hasBytes_of_frame frame tail
      (by change tailSrc.toNat + (input.size - n) ≤ 2 ^ 64; omega)
      (apart (List.mem_cons.mpr (Or.inr List.mem_cons_self)) tailInside tailApart)
  · exact (destWrite.of_frame frame).sub (by rw [tailDstNat]; omega)
      (by rw [tailDstNat]; dsimp only [tailSize]; omega)

end AesGcm.Proofs.Machine.Core.Decrypt
