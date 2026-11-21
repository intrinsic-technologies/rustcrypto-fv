import ChaCha20Poly1305.Proofs.Decrypt.KeyContract
import ChaCha20Poly1305.Proofs.Decrypt.HashControl
import ChaCha20Poly1305.Proofs.Decrypt.TagCalls

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash

theorem copiedAt {m : Ram} {s d : BitVec 64} {len off k : Nat} (len64 : len≤2^64) (h : off+k/8≤len) :
    memLoad (memCopy m d s len) (d+BitVec.ofNat 64 off) k = memLoad m (s+BitVec.ofNat 64 off) k := by
  apply memLoad_congr
  intro i hi
  simp only [BitVec.add_assoc,←BitVec.ofNat_add]
  have e := memStore_getElem?_self_of_le m d (memLoad m s (8*len)) (by omega) (off+i) (by omega)
  rw [storedByte_memLoad _ _ _ (by omega)] at e
  change ((memCopy m d s len)[d+BitVec.ofNat 64 (off+i)]?.getD 0)=_
  rw [show (memCopy m d s len)[d+BitVec.ofNat 64 (off+i)]? = _ from e]; rfl

@[refine_layout] def updated (sp : BitVec 64) (m : Ram) :=
  memStore (memStore m (sp+80) (1#32)) (sp+96) (64#8)
@[refine_layout] def movedMem (sp : BitVec 64) (m : Ram) :=
  memCopy (updated sp m) (sp+208) (sp+32) 128
@[refine_layout] def updates (sp : BitVec 64) : List MemoryRegion :=
  [slot sp 80 4,slot sp 96 1]
@[refine_layout] def installWrites (sp : BitVec 64) := slot sp 24 8 :: slot sp 208 128 :: updates sp

theorem updatedFrame (sp : BitVec 64) (m : Ram) (lo : sp.toNat+392≤2^32) : RamWriteFrame m (updated sp m) (updates sp) := by
  apply ((RamWriteFrame.refl m (updates sp)).memStore (v := (1#32)) (a := sp+80) _).memStore
  all_goals simp [InRegions,updates,slot,InRegion] <;> bv_omega

theorem copiedFrame (sp : BitVec 64) (m : Ram) (lo : sp.toNat+392≤2^32) : RamWriteFrame (updated sp m) (movedMem sp m) [slot sp 208 128] := by
  apply (RamWriteFrame.refl _ _).memStore
  exact ⟨_,.head _,by simp [InRegion,slot]; bv_omega⟩

set_option maxRecDepth 8000
set_option maxHeartbeats 700000

theorem copyHeader (x : Raw) (sp : BitVec 64) (m : Ram) (rs rs') (lo : sp.toNat+392≤2^32)
    (st : Atom.All fnCode rs m (fixed x (sp+32))) :
    Atom.All fnCode rs' (movedMem sp m) (header x 1 (sp+208) ++ [.mem (sp+272) 8 64]) := by
  have f := updatedFrame sp m lo
  have kept : Atom.All fnCode rs (updated sp m) (fixed x (sp+32)) := by
    apply ChaChaRound.keepFrame _ f st
    intro t ht
    simp only [fixed,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [ChaChaRound.pass,Outside,updates,slot]; all_goals bv_omega
  have cnt : memLoad (updated sp m) (sp+80) 32=1 := by
    rw [updated,memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_toNat (by bv_omega) (by bv_omega) (by bv_omega)),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
    rfl
  have used : memLoad (updated sp m) (sp+96) 8=64 := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have cp (i w : Nat) (h : i+w/8≤128) :
      memLoad (movedMem sp m) (sp+BitVec.ofNat 64 (208+i)) w = memLoad (updated sp m) (sp+BitVec.ofNat 64 (32+i)) w := by
    simp only [BitVec.ofNat_add,←BitVec.add_assoc]
    exact copiedAt (m := updated sp m) (s := sp+32) (d := sp+208) (by decide : 128≤2^64) h
  simp only [fixed,Atom.All,Atom.Holds,BitVec.add_assoc] at kept
  simp only [header,List.cons_append,List.nil_append,Atom.All,Atom.Holds,BitVec.add_assoc]
  exact ⟨(cp 0 64 (by decide)).trans kept.1,
    (cp 8 64 (by decide)).trans kept.2.1,
    (cp 16 64 (by decide)).trans kept.2.2.1,
    (cp 24 64 (by decide)).trans kept.2.2.2.1,
    (cp 32 64 (by decide)).trans kept.2.2.2.2.1,
    (cp 40 64 (by decide)).trans kept.2.2.2.2.2.1,
    (cp 48 32 (by decide)).trans cnt,
    (cp 52 64 (by decide)).trans kept.2.2.2.2.2.2.1,
    (cp 60 32 (by decide)).trans kept.2.2.2.2.2.2.2.1,
    (cp 64 8 (by decide)).trans used,trivial⟩

@[refine_layout] def install (x : Raw) (fr : Activation) (n : BitVec 64) : Micro.Step where
  entry := .l1003ae
  exit := .l1003e3
  pre := regs fr ++ [.gpr 5 fr.rbp,.fact (fr.r15=274877906879),.readable fr.rbx 24,.mem (fr.rbx+16) 64 n,
    .fact (fr.rbx.toNat+24 ≤ fr.rsp.toNat ∨ fr.rsp.toNat+392 ≤ fr.rbx.toNat)] ++
    localArea fr ++ fixed x (fr.rsp+32)
  post := regs fr ++ [.gpr 5 fr.rbp,.mem (fr.rsp+24) 64 n] ++ header x 1 (fr.rsp+208) ++ [.mem (fr.rsp+272) 8 64]
  writes := installWrites fr.rsp

end ChaCha20Poly1305.Proofs.Decrypt.Detached
