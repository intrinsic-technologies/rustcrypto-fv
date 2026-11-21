import K256.Proofs.Ecdh.Multiply.Loop.Setup
import K256.Proofs.Ecdh.Multiply.Loop.Body
import K256.Proofs.Generate.Generator.Multiply.Writeback

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

set_option linter.unusedVariables false in
theorem peerWindowLoop (doubles : type_of% @fourDoubles) (select : type_of% @lookup)
    (add : type_of% @addCall) {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (pos : 0 < d) (bound : d < domain.n)
    (ready : PeerPrepared fr a m d peer) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l11d748, a, m⟩, []⟩ out ∧ PeerCoreResult fr d peer out := by
  obtain ⟨b,n,start,first⟩ := peerWindowSetup entry ready
  have finish (k : Nat) (hk : k ≤ 32) {a : Registers} {m : Ram} (s : PeerWindowHead fr a m d peer k) :
      ∃ c u, Reaches (windowLabel (BitVec.ofNat 64 k)) a m .l11f6c4 c u ∧ PeerWindowHead fr c u d peer 0 := by
    induction k generalizing a m with
    | zero => exact ⟨a,m,.refl _,s⟩
    | succ k ih =>
      have nz : BitVec.ofNat 64 (k+1) ≠ 0 := by
        intro eq
        have h := congrArg BitVec.toNat eq
        change (k+1) % 2^64 = 0 at h
        rw [Nat.mod_eq_of_lt (by omega)] at h
        omega
      obtain ⟨c,u,body,atoms,widths,saved,mem,acc,count,digit,temp⟩ :=
        peerWindowRound doubles select add entry (by omega) s
      obtain ⟨e,branch,atoms',widths',saved',cx,dx,r12⟩ :=
        windowCountdown atoms count digit widths saved
      obtain ⟨v,t,tail,last⟩ := ih (by omega) ⟨atoms',widths',saved',mem,acc,cx,dx,r12 ▸ temp⟩
      rw [windowLabel, ite_eq_right nz]
      exact ⟨v,t,(body.trans branch).trans tail,last⟩
  obtain ⟨v,t,loopPath,last⟩ := finish 32 (by decide) first
  obtain ⟨p,_,stored,pval⟩ := last.acc
  have value : p.value = peerWindow d peer := by
    simpa only [peerWindowValue, Curve.radixRemaining_zero, Nat.sub_zero, peerWindow, peerFirstBase, peerSecondBase, firstComponent, secondComponent] using pval
  have ptr := last.memory.locals (0x248,fr.rdi) (by simp)
  have output := entry.outputWrite.of_frame last.memory.frame
  have high := entry.high
  have apart : fr.rsp.toNat + 8 ≤ fr.rdi.toNat := by
    rw [entry.outputPtr, BitVec.toNat_add_of_lt (by change fr.rsp.toNat + 352 < 2^64; omega)]
    change _ ≤ fr.rsp.toNat + 352
    omega
  obtain ⟨out,run,tag,done_,_,point,frame,keep,cx⟩ := writeback fr v t last.atoms
    (fun x hx => Common.fnCode_subset_programImage x (code_l11f6c4 x hx))
    (by simpa only [Lift.reduceAddOffset, BitVec.reduceSub, Lift.reduceAddNeg] using ptr)
    (value ▸ stored.projectiveAt) output (Or.inr apart)
  have ret : program.Exec (dialect Extracted.programImage) ⟨⟨.l11f6c4,v,t⟩,[]⟩ out :=
    .done (by simp only [Program.step,run,Transfer.next])
  refine ⟨out,Program.Exec.of_sem ((start.trans loopPath).exec ret.sem),tag,done_,?_,?_,point⟩
  · intro ⟨i,hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact congrArg Value.width cx
    all_goals rw [keep _ (by simp)]; exact last.widths _ (by simp [Activation.argumentNumbers])
  · apply last.memory.frame.trans frame
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨_, by simp [coreWrites], Nat.le_refl _, Nat.le_refl _⟩

end K256.Proofs.Generate.Generator.Multiply
