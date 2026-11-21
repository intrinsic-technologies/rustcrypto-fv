import ChaCha20Poly1305.Proofs.Decrypt.HashBytes
import ChaCha20Poly1305.Proofs.Decrypt.PartialCalls

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305
set_option maxHeartbeats 620000
set_option maxRecDepth 6000
set_option pp.maxSteps 160

def padRegions (fr : Activation) := ⟨fr.rsp.toNat+32,16⟩ :: regions fr

structure PadScope (fr : Activation) (src : BitVec 64) (n : Nat) (m : Ram) extends Scope fr src n m where
  area : Writable fnCode m fr.rsp 392
  ctxAt : fr.rdi = fr.rsp+336
  apart : src.toNat+n ≤ fr.rsp.toNat-96 ∨ fr.rsp.toNat+392 ≤ src.toNat
  code : fr.rsp.toNat+392 ≤ 0x1001f0 ∨ 0x102e00+96 ≤ fr.rsp.toNat
  got : fr.rsp.toNat+392 ≤ 0x2013a8 ∨ 0x2013e8+96 ≤ fr.rsp.toNat
  copyRead : Readable m 0x2013a8 8
  copyAddr : memLoad m 0x2013a8 64 = 0x102dc0
  fillRead : Readable m 0x2013e0 8
  fillAddr : memLoad m 0x2013e0 64 = 0x102d70

theorem widen {m m' : Ram} {small big : List MemoryRegion} (f : RamWriteFrame m m' small)
    (incl : RegionsWithin small big) : RamWriteFrame m m' big := (RamWriteFrame.refl m big).trans f incl

theorem PadScope.after {fr src n m m'} (g : PadScope fr src n m) (f : RamWriteFrame m m' (padRegions fr)) :
    PadScope fr src n m' := by
  have lo := g.area.readable.low
  have h := g.got
  have sp := g.floor
  refine ⟨g.toScope.after f,g.area.of_frame f,g.ctxAt,g.apart,g.code,g.got,g.copyRead.of_frame f,
    Eq.trans (f.memLoad_eq ?_) g.copyAddr,g.fillRead.of_frame f,Eq.trans (f.memLoad_eq ?_) g.fillAddr⟩
  all_goals simp [Outside,padRegions,regions,g.ctxAt] <;> bv_omega

theorem PadScope.data {fr src n m m'} (g : PadScope fr src n m) (f : RamWriteFrame m m' (padRegions fr)) :
    memLoad m' src (8*n) = memLoad m src (8*n) := by
  have lo := g.area.readable.low
  have buf := g.buf.low
  have sep := g.apart
  have sp := g.floor
  apply f.memLoad_eq
  simp [Outside,padRegions,regions,g.ctxAt]; bv_omega

def tempAreas (fr : Activation) : List MemoryRegion := [⟨fr.rsp.toNat-8,8⟩,⟨fr.rsp.toNat+32,16⟩]

theorem PadScope.keepAcc {fr src n m m' r ws rs rs'} (g : PadScope fr src n m) (f : RamWriteFrame m m' (tempAreas fr))
    (h : Atom.All fnCode rs m (rData fr.rdi r ++ accData fr.rdi ws)) :
    Atom.All fnCode rs' m' (rData fr.rdi r ++ accData fr.rdi ws) := by
  have lo := g.area.readable.low
  have sp := g.floor
  apply ChaChaRound.keepFrame _ f h
  intro t ht
  simp only [rData,accData,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ChaChaRound.pass,Outside,tempAreas,g.ctxAt]; all_goals bv_omega

def amount (s : ByteArray) := BitVec.ofNat 64 (s.size%16)
def offset (s : ByteArray) := BitVec.ofNat 64 (16*(s.size/16))

theorem amountNat (s : ByteArray) : (amount s).toNat = s.size%16 := by
  simp only [amount,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show s.size%16<2^64 by omega)]

theorem restNat (s : ByteArray) : ((16:BitVec 64)-amount s).toNat = 16-s.size%16 := by
  have h := amountNat s
  bv_omega

@[refine_layout] def snapAt (fr : Activation) (depth : Nat) (m : Ram) :=
  {fr with original := m,low := fr.rsp-BitVec.ofNat 64 depth}

theorem tempToPad {fr src n m} (g : PadScope fr src n m) : RegionsWithin (tempAreas fr) (padRegions fr) := by
  have sp := g.floor
  simp [RegionsWithin,tempAreas,padRegions,regions]; omega

theorem tempToFrame {fr src n m dest len} (g : PadScope fr src n m)
    (lo : fr.rsp.toNat+32 ≤ (dest : BitVec 64).toNat) (hi : dest.toNat+len ≤ fr.rsp.toNat+48) :
    RegionsWithin ((snapAt fr 8 m).region :: [⟨dest.toNat,len⟩]) (tempAreas fr) := by
  have floor := g.floor
  simp [RegionsWithin,tempAreas,snapAt,Activation.region]
  bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Hash
