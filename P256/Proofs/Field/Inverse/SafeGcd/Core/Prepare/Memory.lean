import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Signed
import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Frame

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude
open Shared (batchCount batchInput batchResult)

def batchFrame (fr : Activation) (original : Ram) : Activation :=
  { fr with original := original, rsp := fr.rsp - 0x188, r13 := fr.rsp - 0x180 }

@[refine_layout] def memoryAtoms (fr : Activation) (p : Inputs) (s : LoopState) : List Atom :=
  [.mem (fr.rsp - 8) 64 fr.rbp, .mem (fr.rsp - 16) 64 fr.r15,
   .mem (fr.rsp - 24) 64 fr.r14, .mem (fr.rsp - 32) 64 fr.r13,
   .mem (fr.rsp - 40) 64 fr.r12, .mem (fr.rsp - 48) 64 fr.rbx,
   .mem fr.rsp 64 fr.ret, .readable fr.rsp 8, .fact (fr.ret.toNat < 2^32),
   .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
   .fact (fr.rsp.toNat % 16 = 8),
   .mem (fr.rsp - 0x108) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
   .mem (fr.rsp - 0x60) 64 fr.rcx] ++ commonAtoms fr p ++ savedInputAtoms fr p ++ stateAtoms fr s ++
  [.mem (fr.rsp - 0x38) 64 (BitVec.ofNat 64 s.remaining),
   .mem (fr.rsp - 0x184) 32 (BitVec.ofNat 32 (batchCount s))]

theorem resident_split {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} :
    Atom.All code args mem (Signed.residentAtoms fr controls p s) ↔
      args[4] = ⟨64, fr.rsp - 0x188⟩ ∧ args[22] = ⟨1,0⟩ ∧
      args[39] = ⟨32, controls.MXCSR⟩ ∧ args[51] = ⟨16, controls.FP87_Control⟩ ∧
      Atom.All code args mem (memoryAtoms fr p s) := by
  simp only [Signed.residentAtoms, Core.residentAtoms, memoryAtoms, frameAtoms,
    Atom.all_append, Atom.All, Atom.Holds, and_assoc]
  constructor
  · intro h
    rcases h with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,q,r,mx,fc,t⟩
    exact ⟨a,b,mx,fc,c,d,e,f,g,h,i,j,k,l,m,n,o,q,r,t⟩
  · intro h
    rcases h with ⟨a,b,mx,fc,c,d,e,f,g,h,i,j,k,l,m,n,o,q,r,t⟩
    exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,q,r,mx,fc,t⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem memory_stable {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState}
    (h : Atom.All code args mem (Signed.residentAtoms fr controls p s)) :
    ∀ a ∈ memoryAtoms fr p s,
      Support.MemoryStable [Batch.scratchRegion (batchFrame fr mem)] a := by
  simp only [Signed.residentAtoms, Core.residentAtoms, Atom.all_append] at h
  have hf := h.1.1.1.1
  simp only [frameAtoms, Atom.All, Atom.Holds] at hf
  obtain ⟨_,_,_,_,_,_,_,_,_,hret,_,hw,hroom,_,_,_,_,_⟩ := hf
  have hc := h.1.1.1.2
  change Atom.All code args mem (outputAtoms fr ++ inputAtoms fr p) at hc
  rw [Atom.all_append] at hc
  have hc2 := hc.2
  simp only [inputAtoms, Atom.All, Atom.Holds] at hc2
  obtain ⟨_,_,_,hr1,hr2,hr3,hs1,hs2,hs3,_,_⟩ := hc2
  have hl := hret.low
  have hl1 := hr1.low
  have hl2 := hr2.low
  have hl3 := hr3.low
  simp only [memoryAtoms, commonAtoms, outputAtoms, inputAtoms, savedInputAtoms,
    stateAtoms, signedAtoms,
    List.forall_mem_append, List.not_mem_nil, Support.MemoryStable, and_true,
    Vector.size, Nat.reduceDiv, Nat.reduceMul, Nat.reduceLT, true_and,
    Outside, Batch.scratchRegion, batchFrame, List.mem_cons, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals first | omega | bv_omega

end P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare
