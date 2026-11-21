import K256.Proofs.Sec1.Affine.Routes.Input
import K256.Proofs.Sec1.Affine.CoordinateFrame
import K256.Proofs.Sec1.Decode

namespace K256.Proofs.Sec1.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open Standards.SECG.ECC

def childActivation (s : RamState) (mem : Ram) (tag : BitVec 8) : Activation :=
  let fr := activation s
  let sp := fr.rsp - 136
  { fr with
    original := mem, rsp := sp - 8, low := sp - 8 - 1048,
    ret := if tag != 4 then 0x1214ce else 0x121502,
    rsi := fr.rsi + 1, r14 := fr.rsi + 1, rdi := sp,
    rdx := if tag != 4 then (if tag = 3 then 1 else 0) else fr.rsi + 33 }

theorem childGeometry {s : RamState} {bytes : ByteArray} {m : Ram}
    (mem : CoordinateMemory s bytes m) (t : BitVec 8) :
    let fr := childActivation s m t
    fr.low.toNat + 1048 = fr.rsp.toNat ∧ fr.rsp.toNat + 8 = fr.rdi.toNat := by
  let fr := childActivation s m t
  have room : 1048 ≤ fr.rsp.toNat := mem.room
  have a : fr.low.toNat = fr.rsp.toNat - 1048 := BitVec.toNat_sub_of_le (by change 1048 ≤ fr.rsp.toNat; exact room)
  have b : fr.low.toNat + 1056 = fr.rdi.toNat := mem.stackEnd
  change fr.low.toNat + 1048 = fr.rsp.toNat ∧ fr.rsp.toNat + 8 = fr.rdi.toNat
  omega

structure CoordinateRegisters (fr : Activation) (args : Values Value Reg.count) : Prop where
  rsp : args[4] = ⟨64,fr.rsp⟩
  rdi : args[7] = ⟨64,fr.rdi⟩
  rsi : args[6] = ⟨64,fr.rsi⟩
  rdx : args[2] = ⟨64,fr.rdx⟩
  df : args[22] = ⟨1,0⟩
  saved : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,39,50,51] → args[i] = fr.entryValue i.val

def ResultAt (m : Ram) (dst : BitVec 64) (point : Option Curve.Point) : Prop :=
  match point with
  | none => memLoad m (dst + 88) 8 = 0
  | some p => memLoad m (dst + 88) 8 = 1 ∧ Parser.PublicKeyAt m dst p

def CoordinateRoutine (s : RamState) (bytes : ByteArray) (tag : BitVec 8) : Prop :=
  ∀ (child : Values Value Reg.count) (mem : Ram),
    let fr := childActivation s mem tag
    CoordinateMemory s bytes mem → CoordinateRegisters fr child → memLoad mem fr.rsp 64 = fr.ret →
    ∃ out, program.Exec (dialect Extracted.programImage)
      ⟨⟨if tag != 4 then .l1205b0 else .l11f780,child,mem⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ out.values[4] = ⟨64,(activation s).rsp - 136⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,13,22,39,50,51] → out.values[i] = child[i]) ∧
      RamWriteFrame mem out.store (coordinateWrites (activation s)) ∧
      ResultAt out.store fr.rdi (K256.Spec.Secp256k1.decodePublicKey bytes)

theorem finishResult {m next : Ram} {src dst : BitVec 64} {p : Option Curve.Point}
    (valid : memLoad next (dst + 88) 8 = memLoad m (src + 88) 8)
    (point : memLoad m (src + 88) 8 = 1 → ∀ p, Parser.PublicKeyAt m src p → Parser.PublicKeyAt next dst p)
    (h : ResultAt m src p) : ResultAt next dst p := by
  cases p with
  | none => exact valid.trans h
  | some p => exact ⟨valid.trans h.1,point h.1 p h.2⟩

end K256.Proofs.Sec1.Affine
