import AesGcm.Proofs.Machine.KeySchedule.Projection
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Fixslice.Memory

namespace AesGcm.Proofs.Machine.AES16

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine

def variant (use256 : Bool) : Variant := if use256 then .aes256 else .aes128

def expectedKey (v : Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) : Fixslice16.Planes16 :=
  let planes := Fixslice16.encodeStandard
    (KeySchedule.invRowsPow (KeySchedule.roundPhase v round.val)
      (KeySchedule.roundKeyBlock v key round))
  if round.val = 0 then planes else Fixslice16.subBytesNots planes

def ScheduleIn (v : Variant) (key : Vector UInt8 v.keyBytes)
    (dst : BitVec 64) (mem : Ram) : Prop :=
  ∀ (r : Fin (v.Nr + 1)) (p : Fin 8),
    memLoad mem (dst + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 = expectedKey v key r p

theorem expectedKey_zero (v : Variant) (key : Vector UInt8 v.keyBytes) :
    expectedKey v key ⟨0, by cases v <;> decide⟩ =
      Fixslice16.encodeStandard (KeySchedule.roundKeyBlock v key ⟨0, by cases v <;> decide⟩) := by
  rw [expectedKey, ← KeySchedule.projectPlanes_expectedKey v key _ 0, KeySchedule.expectedKey_zero,
    Fixslice16.projectPlanes_encodeStandard]

theorem ScheduleIn.words {v : Variant} {key : Vector UInt8 v.keyBytes}
    {dst : BitVec 64} {mem : Ram} (h : ScheduleIn v key dst mem)
    (r : Fin (v.Nr + 1)) :
    WordsAt mem (dst + BitVec.ofNat 64 (16 * r.val)) 16
      (Vector.ofFn (expectedKey v key r)) := by
  intro p hp
  simpa only [wordAddr, Nat.reduceDiv, Vector.getElem_ofFn, BitVec.add_assoc,
    ← BitVec.ofNat_add] using h r ⟨p, hp⟩

theorem scheduleIn_of_copy {v : Standards.NIST.AES.Variant}
    {key : Vector UInt8 v.keyBytes} {src dst : BitVec 64} {before after : Ram}
    (hs : ScheduleIn v key src before)
    (hc : ∀ i < 16 * (v.Nr + 1),
      after[dst + BitVec.ofNat 64 i]? = before[src + BitVec.ofNat 64 i]?) :
    ScheduleIn v key dst after := by
  intro r p
  rw [← hs r p]
  apply memLoad_congr
  intro i hi
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, memByte, PhysicalMemory.read]
  rw [hc _ (by have := r.isLt; have := p.isLt; change i < 2 at hi; omega)]

theorem scheduleIn_of_frame {v : Variant} {key : Vector UInt8 v.keyBytes}
    {base : BitVec 64} {before after : Ram} {regions : List MemoryRegion}
    (hs : ScheduleIn v key base before) (hf : RamWriteFrame before after regions)
    (hout : Outside regions base (16 * (v.Nr + 1))) : ScheduleIn v key base after := by
  intro r p
  have hp := p.isLt
  have hr := r.isLt
  have hbound : 16 * r.val + 2 * p.val + 2 ≤ 16 * (v.Nr + 1) := by omega
  have haddr : (base + BitVec.ofNat 64 (16 * r.val + 2 * p.val)).toNat =
      base.toNat + 16 * r.val + 2 * p.val := by
    have hlow := hout.1
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hf.memLoad_eq ⟨?_, ?_⟩]
  · exact hs r p
  · have := hout.1
    rw [haddr]
    change base.toNat + 16 * r.val + 2 * p.val + 2 ≤ 2 ^ 64
    omega
  · intro reg hreg
    have h := hout.2 reg hreg
    rw [haddr]
    change base.toNat + 16 * r.val + 2 * p.val + 2 ≤ reg.start ∨
      reg.start + reg.size ≤ base.toNat + 16 * r.val + 2 * p.val
    omega

end AesGcm.Proofs.Machine.AES16
