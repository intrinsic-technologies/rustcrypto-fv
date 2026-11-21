import ChaCha20Poly1305.Proofs.MemoryRoutines.Contracts
import X86Proofs.Instructions.Call.Triple

namespace ChaCha20Poly1305.Proofs.MemoryRoutines

open X86 X86.Machine X86.UserProcess X86Proofs

structure CallBodyResult [Bindings] (s t : RamState) : Prop where
  ready : ReadyToStep t
  rsp : stackPtr t = stackPtr s
  result : rax.read t = rdi.read s
  agrees : AgreesExcept (callChanges s) s t

theorem call_ret [Bindings] {s t : RamState} {entry pc : BitVec 64} {codeLength : Nat}
    (hpre : CallPre entry codeLength s) (hbody : CallBodyResult s t)
    (hcode : CodeIn (codeRange pc [0xc3]) t) (hip : t.RIP = pc) :
    ∃ u, Machine.step t = some (.next u) ∧ CallResult s u ∧ u.external = t.external := by
  have hbytes (i : Nat) (hi : i < 8) :
      t.external[stackPtr s + BitVec.ofNat 64 i]? =
        s.external[stackPtr s + BitVec.ofNat 64 i]? := by
    apply hbody.agrees.byte
    intro c hc hcover
    simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover
    obtain ⟨j, hj, he⟩ := hcover
    exact hpre.dstReturn j hj i hi he.symm
  have htop : stackTop t = (returnBoundary s).rip := by
    change memLoad t.external (stackPtr t) 64 = memLoad s.external (stackPtr s) 64
    rw [hbody.rsp]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun byte : Option UInt8 ↦ byte.getD 0) (hbytes i hi)
  have hread : MemReadable t (stackPtr t) 8 := by
    rw [hbody.rsp]
    exact ⟨hpre.returnSlot.low,
      fun i hi ↦ hbody.agrees.grow _ (hpre.returnSlot.mem i hi)⟩
  obtain ⟨u, hstep, hready, he⟩ := ret_effect_step pc t hbody.ready hcode
    ⟨⟨hip, hread⟩, by rw [htop]; exact hpre.returnLow⟩
  refine ⟨u, hstep, ⟨hready, he.rip.trans htop, ?_, ?_, ?_⟩, ?_⟩
  · exact he.writes.trans (congrArg (· + 8) hbody.rsp)
  · exact (he.agrees.read (by simp)).trans hbody.result
  · apply (hbody.agrees.trans he.agrees).mono
    simp [callChanges]
  · exact he.agrees.external (by simp [Component.Covers])

theorem call_body_returns [Bindings] {s t : RamState} {entry pc : BitVec 64}
    {codeLength fuel : Nat} (hpre : CallPre entry codeLength s)
    (hbody : CallBodyResult s t) (hcode : CodeIn (codeRange pc [0xc3]) t)
    (hip : t.RIP = pc) (hrun : Advances (returnBoundary s) fuel s t) :
    ∃ u, Returns (returnBoundary s) (fuel + 1) s u ∧
      CallResult s u ∧ u.external = t.external := by
  obtain ⟨u, hstep, hresult, hext⟩ := call_ret hpre hbody hcode hip
  refine ⟨u, hrun.returns ?_, hresult, hext⟩
  exact Returns.of_step hstep hresult.rip hresult.rsp

theorem call_body_advances [Bindings] {s t : RamState} {entry pc : BitVec 64}
    {codeLength fuel : Nat} {boundary : ReturnBoundary} (hpre : CallPre entry codeLength s)
    (hbody : CallBodyResult s t) (hcode : CodeIn (codeRange pc [0xc3]) t)
    (hip : t.RIP = pc) (hrun : Advances boundary fuel s t)
    (hne : (returnBoundary s).rip ≠ boundary.rip) :
    ∃ u, Advances boundary (fuel + 1) s u ∧ CallResult s u ∧ u.external = t.external := by
  obtain ⟨u, hstep, hresult, hext⟩ := call_ret hpre hbody hcode hip
  refine ⟨u, hrun.trans ?_, hresult, hext⟩
  exact Advances.of_step hstep (.inl (hresult.rip ▸ hne))

end ChaCha20Poly1305.Proofs.MemoryRoutines
