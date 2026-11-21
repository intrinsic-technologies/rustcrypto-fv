import ChaCha20Poly1305.Proofs.Decrypt.HashControl
import ChaCha20Poly1305.Proofs.Decrypt.PadFinish
import ChaCha20Poly1305.Proofs.Decrypt.BlockMath

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 600000
set_option maxRecDepth 6000
set_option pp.maxSteps 140

theorem noWrites {m m' : Ram} (f : RamWriteFrame m m' []) : m'=m :=
  Std.ExtHashMap.ext_getElem? (fun k => f.outside k (by simp [Outside]; have := k.isLt; omega))

theorem maskLowEq {n : BitVec 64} {s : ByteArray} (h : n.toNat=s.size) (h32 : n.toNat<2^32) : maskLow n=amount s := by
  apply BitVec.eq_of_toNat_eq
  rw [maskLow,BitVec.toNat_setWidth_of_le (by decide),BitVec.toNat_and,BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt h32,amountNat,←h]
  exact Nat.and_two_pow_sub_one_eq_mod _ 4

private theorem truncateMask (n : BitVec 64) (k : Nat) (low : n.toNat<2^k) :
    (n &&& BitVec.ofNat 64 (2^k-1))=n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,←Nat.and_two_pow_sub_one_eq_mod _ 64,←Nat.and_assoc,
    Nat.and_two_pow_sub_one_eq_mod _ 64,Nat.and_two_pow_sub_one_eq_mod _ k,Nat.mod_eq_of_lt low,Nat.mod_eq_of_lt n.isLt]

theorem masks {n : BitVec 64} {s : ByteArray} (h : n.toNat=s.size) (h32 : n.toNat<2^32) :
    maskA n=offset s ∧ maskC n=offset s := by
  have common : n &&& (BitVec.allOnes 64 <<< 4) = offset s := by
    apply BitVec.eq_of_toNat_eq
    rw [Stream.Control.maskFloor,h,offset,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have tr (k : Nat) (hk : n.toNat<2^k) :
      (BitVec.ofNat 64 (2^k-1) &&& (BitVec.allOnes 64 <<< 4)) &&& n = offset s := by
    rw [BitVec.and_comm _ n,←BitVec.and_assoc,truncateMask n k hk,common]
  exact ⟨tr 63 (by omega),tr 38 (by omega)⟩

def basePtr (ct : Bool) (fr : Activation) := match ct with | false => fr.r13 | true => fr.r15

def afterBlocks (fr : Activation) (s : ByteArray) := {fr with rbx := if s.size<16 then fr.rbx else 0#64}

theorem fromJump {a b P} (run : JumpRun lifted fnCode a b) (h : Forward b P) : Forward a P := by
  intro post cont
  obtain ⟨o,r,q⟩ := h post cont
  exact ⟨o,execJump run r,q⟩

structure AtTest (ct : Bool) (fr : Activation) (s : ByteArray) (key : Vector UInt8 32)
    (v : Nat) (m : Ram) (b : lifted.Location) : Prop where
  label : b.label = finish ct
  regs : Atom.All fnCode b.arguments b.store (Hash.regs (afterBlocks fr s))
  frame : RamWriteFrame m b.store (regions fr)
  acc : ∃ ws, represents ws (foldFrom s (rKey key) v (s.size/16)) ∧ Atom.All fnCode b.arguments b.store (accData fr.rdi ws)

theorem beforeTest (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (key : Vector UInt8 32) (v : Nat)
    (ws : Vector (BitVec 32) 5) (rep : represents ws v) (a : lifted.Location)
    (geo : 0<s.size → PadScope fr src s.size a.store) (len : basePtr ct fr=offset s)
    (entry : a.label=enter ct (decide (16≤s.size)))
    (ready : Atom.All fnCode a.arguments a.store (regs fr))
    (setup : 16≤s.size → Atom.All fnCode a.arguments a.store (beginStep ct fr src).pre)
    (hr : Atom.All fnCode a.arguments a.store (rData fr.rdi (rWords key)))
    (ha : Atom.All fnCode a.arguments a.store (accData fr.rdi ws))
    (raw : memLoad a.store src (8*s.size)=Bytes.packed s) :
    Forward a (AtTest ct fr s key v a.store) := by
  by_cases many : 16≤s.size
  · obtain ⟨b,ab,bl,rs,frame⟩ := Micro.run (beginValid ct fr src) (by simpa [enter,many,beginStep] using entry) (setup many)
    apply fromJump ab
    have me := noWrites frame
    have start : Atom.All fnCode b.arguments b.store (loopRegs fr src s 0) := by
      have z : remain s 0 = offset s := by simp [remain,offset]
      cases ct <;> dsimp [basePtr] at len
      all_goals unpack_atoms rs [] <;> join_atoms [loopRegs,addr,z]
      all_goals first | assumption | (rw [←len]; assumption) | (simpa using ‹_›)
    have keepR : Atom.All fnCode b.arguments b.store (rData fr.rdi (rWords key)) := by rw [me]; exact hr
    have keepA : Atom.All fnCode b.arguments b.store (accData fr.rdi ws) := by rw [me]; exact ha
    apply (full ct fr src s key v ws rep b (me ▸ (geo (by omega)).toScope) (by omega) bl start
      keepR keepA (me ▸ raw) _ (Nat.le_refl _)).bind
    intro c h
    apply Forward.here
    refine ⟨by simpa [doneLabel] using h.label,?_,me ▸ h.frame,h.acc⟩
    have u := ((Atom.all_append _ _).1 h.regs).1
    simpa only [afterBlocks,ite_eq_right (Nat.not_lt.mpr many),remain,Nat.sub_self,Nat.mul_zero] using u
  · have n : s.size/16=0 := by omega
    apply Forward.here
    exact ⟨by simpa [enter,many] using entry,by simpa [afterBlocks,Nat.lt_of_not_ge many] using ready,
      .refl _ _,ws,by simpa [n,foldFrom] using rep,ha⟩

end ChaCha20Poly1305.Proofs.Decrypt.Hash
