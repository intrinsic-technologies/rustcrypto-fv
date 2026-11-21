import ChaCha20Poly1305.Proofs.Decrypt.Install

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash

theorem installFacts {sp vec : BitVec 64} {m : Ram} (n : BitVec 64) (area : Writable fnCode m sp 392)
    (rd : Readable m vec 24) (val : memLoad m (vec+16) 64=n)
    (sep : vec.toNat+24≤sp.toNat ∨ sp.toNat+392≤vec.toNat)
    (code : sp.toNat+392≤0x1001f0 ∨ 0x102def≤sp.toNat) :
    RepMovsOk fnCode (updated sp m) 0 (sp+32) (sp+208) 32 4 0x1003cd 2 ∧
    Readable (movedMem sp m) (vec+16) 8 ∧ memLoad (movedMem sp m) (vec+16) 64=n ∧
    RamWriteFrame m (movedMem sp m) (installWrites sp) := by
  have lo := area.readable.low
  have vl := rd.low
  have f1 := updatedFrame sp m lo
  have f2 := copiedFrame sp m lo
  have all : RamWriteFrame m (movedMem sp m) (installWrites sp) := by
    apply (widen f1 _).trans f2
    all_goals simp [RegionsWithin,updates,slot,installWrites] <;> bv_omega
  have area' := area.of_frame f1
  have inp : Copy.Input fnCode (updated sp m) (sp+32) (sp+208) 128 :=
    ⟨area'.readable.sub (by bv_omega) (by bv_omega),area'.sub (by bv_omega) (by bv_omega),by bv_omega⟩
  have safe := Copy.guard inp (Copy.start ..) (i:=0) (size:=4) (count:=32)
    (p:=0x1003cd) (k:=2) (by decide) (by decide) (by bv_omega)
  refine ⟨by simpa [Copy.ptr] using safe,(rd.of_frame all).sub (by bv_omega) (by bv_omega),?_,all⟩
  rw [all.memLoad_eq,val]
  simp [Outside,installWrites,updates,slot]; bv_omega

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
set_option pp.maxSteps 180

attribute [local irreducible] memLoad memStore memCopy

theorem installValid (x : Raw) (fr : Activation) (n : BitVec 64) (hn : n.toNat<2^32) :
    Micro.Valid (install x fr n) := by
  unfold Micro.Valid
  refine_intro
  obtain ⟨guard,read,value,wf⟩ := installFacts (sp:=fr.rsp) (vec:=fr.rbx) (m:=mem) n
    (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  have fs : Atom.All fnCode (Vector.replicate Reg.count (⟨64,0⟩ : Value)) mem (fixed x (fr.rsp+32)) := by
    join_atoms [] <;> assumption
  have header := copyHeader x fr.rsp mem _ (Vector.replicate Reg.count (⟨64,0⟩ : Value))
    (by assumption) fs
  unpack_atoms header [BitVec.add_assoc]
  simp only [movedMem,updated,installWrites,slot,updates] at guard read value wf
  have test : ¬ 274877906879 < n.toNat := by omega
  have val : memLoad (memCopy (memStore (memStore mem (fr.rsp + 80) (1 : BitVec 32)) (fr.rsp + 96) (64 : BitVec 8)) (fr.rsp + 208) (fr.rsp + 32) 128) (fr.rbx+16) 64=n := value
  have area := atom16.of_frame wf
  have preframe := hframe.trans wf (fun z hz => ⟨z,hz,Nat.le_refl _,Nat.le_refl _⟩)
  refine_uir [Micro.program,install]
  refine_lifted [guard,value,read,cmpSpec_CF,cmpSpec_ZF]
  all_goals try refine_close [value,read,BitVec.add_assoc]
  all_goals try (exfalso; rw [val] at hc; bv_omega)
  all_goals try exact Or.inr guard
  all_goals try exact LoadOk.of_region read (Nat.le_refl _) (Nat.le_refl _)
  all_goals try (apply StoreOk.of_region area <;> first | bv_omega | (apply RangeApart.of_toNat <;> bv_omega))
  all_goals try (apply preframe.memStore; simp [InRegions,InRegion]; bv_omega)
  all_goals try assumption
  all_goals trace_state

end ChaCha20Poly1305.Proofs.Decrypt.Detached
