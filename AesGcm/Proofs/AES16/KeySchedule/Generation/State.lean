import AesGcm.Proofs.AES16.KeySchedule.Algebra
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn104370.Frame
import AesGcm.Proofs.Machine.LIR.Fn1057c0.Frame

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def RawSchedulePrefix (v : Variant) (key : Vector UInt8 v.keyBytes)
    (rounds : Nat) (base : BitVec 64) (mem : Ram) : Prop :=
  ∀ (r : Fin (v.Nr + 1)), r.val < rounds → ∀ p : Fin 8,
    memLoad mem (base + BitVec.ofNat 64 (16 * r.val + 2 * p.val)) 16 =
      Fixslice16.encodeStandard (Machine.KeySchedule.roundKeyBlock v key r) p

namespace Generation

def base (use256 : Bool) (sp : BitVec 64) : BitVec 64 :=
  sp + (if use256 then 12 else 8)

def regions (use256 : Bool) (sp : BitVec 64) : List MemoryRegion :=
  [span (sp - 248) 248, span (base use256 sp) (if use256 then 240 else 176)]

def roundRegions (use256 : Bool) (sp : BitVec 64) (round : Nat) : List MemoryRegion :=
  [span (sp - 248) 248, span (base use256 sp + BitVec.ofNat 64 (16 * round)) 16]

def label (use256 : Bool) (round : Nat) : LIR.Label :=
  if round = (variant use256).Nr + 1 then
    (if use256 then .l10593a else .l10446f)
  else if use256 then
    (if round % 2 = 0 then .l105870 else .l1058d4)
  else .l104424

structure Ready (use256 : Bool) (round : Nat) (sp : BitVec 64)
    (args : Values Value Reg.count) : Prop where
  hsp : args[4].get 64 = sp
  hTypes : GPRsTyped args
  hDF : args[22] = ⟨1, 0⟩
  h39 : args[39] = ⟨32, args[39].get 32⟩
  h50 : args[50] = ⟨16, args[50].get 16⟩
  h51 : args[51] = ⟨16, args[51].get 16⟩
  hbuffer : args[14].get 64 = base use256 sp
  hindex : args[15].get 64 = BitVec.ofNat 64 (8 * (round - 1))
  hcontrol : if use256 then
    args[3].get 64 = BitVec.ofNat 64 (32 * (round / 2)) ∧
    args[12].get 64 = BitVec.ofNat 64 (16 + 32 * (round / 2)) ∧
    args[13].get 64 = BitVec.ofNat 64 (32 + 34 * ((round - 2) / 2))
  else
    args[5].get 64 = BitVec.ofNat 64 (round - 1) ∧
    args[12].get 64 = BitVec.ofNat 64 (16 * round) ∧
    args[13].get 64 = base use256 sp + BitVec.ofNat 64 (18 * (round - 1))

structure MemoryReady (use256 : Bool) (code : CodeMap) (mem : Ram) (sp : BitVec 64) : Prop where
  hstack : Writable code mem (sp - 248) (if use256 then 608 else 512)
  hroom : 248 ≤ sp.toNat
  hAlign : sp.toNat % 16 = 0
  hreadPanic : Readable mem 0x201210 8
  hpanic : memLoad mem 0x201210 64 = 0x103880
  hreadBounds : Readable mem 0x201230 8
  hbounds : memLoad mem 0x201230 64 = 0x101230
  hslotsApart : 0x201330 ≤ sp.toNat ∨
    sp.toNat + (if use256 then 360 else 264) ≤ 0x201210

def SameFP (before after : Values Value Reg.count) : Prop :=
  after[39] = before[39] ∧ after[50] = before[50] ∧ after[51] = before[51]

end Generation
end AesGcm.Proofs.Machine.AES16.KeySchedule
