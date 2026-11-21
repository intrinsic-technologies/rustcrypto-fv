import Sha3.Proofs.Permutation.LoadStore.Load.Progress
import Sha3.Proofs.Permutation.LoadStore.Load.Model
import Sha3.Proofs.Permutation.LoadStore.Load.Instructions

namespace Sha3.Proofs.Permutation.Load

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {copy : Copy} [Bindings] {boundary : ReturnBoundary} {initial : RamState} {v : Values}
  {p next : BitVec 64} {bytes : List UInt8}

theorem advance_load (hp : Pre copy initial) (hboundary : ¬ InProgram boundary.rip)
    {am : AddrMode} {dst : BitVec 5} {lane : Fin 25}
    (hstep : StepEffect (LoadPre p (fun s ↦ am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p bytes) (movR64M64Effect p dst am))
    (hin : (p, bytes) ∈ loadInstructionBytes copy) (hlen : bytes.length = movLoadLen am)
    (hnext : p + BitVec.ofNat 64 (movLoadLen am) = next)
    (haddr : ∀ s, am.addr s next =
      (Operand.reg 7 : Operand 64).read s + BitVec.ofNat 64 (8 * lane.val))
    (hpointer : v.registers 7 = initial.regValue .rdi) (hdst : dst ≠ 4) :
    AdvanceTriple boundary 1 (Progress initial v p) Extracted.programImage
      (fun _ t ↦ Progress initial (execute initial v (.load dst lane)) next t) := by
  intro s hready hcode hs
  have ha : am.addr s (p + BitVec.ofNat 64 (movLoadLen am)) =
      initial.regValue .rdi + BitVec.ofNat 64 (8 * lane.val) := by
    rw [hnext, haddr, hs.registers 7 (by decide), hpointer]
  have hpre : LoadPre p (fun s ↦ am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8 s := by
    refine ⟨hs.rip, ?_⟩
    rw [ha]
    exact hs.input_lane_readable hp lane
  have hn : (movR64M64Effect p dst am s).rip ≠ boundary.rip := by
    change p + BitVec.ofNat 64 (movLoadLen am) ≠ boundary.rip
    rw [← hlen]
    exact fun he ↦ hboundary (he ▸ loadInstruction_next_inProgram copy hin)
  obtain ⟨t, hrun, ht, he⟩ := hstep.advances hready
    (hcode.mono fun x hx ↦ loadCode_subset_programImage copy x
      (loadInstruction_code_subset copy _ hin x hx)) hpre hn
  have hav := Effect.avoids_of_components_reg_rip
    (movR64M64Effect_components p dst am s) Extracted.programImage
  refine ⟨t, hrun, ht, he.codeIn hav hcode, ?_⟩
  have hv : (Operand.reg dst : Operand 64).read t =
      memoryLanes (initial.regValue .rdi) initial lane := by
    have hw := he.writes
    change (Operand.reg dst : Operand 64).read t =
      (Operand.mem (am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) : Operand 64).read s at hw
    rw [ha] at hw
    exact hw.trans (hs.input_lane hp lane)
  have hprogress := hs.reg he hdst (by simp) hv
  change Progress initial (execute initial v (.load dst lane))
    (p + BitVec.ofNat 64 (movLoadLen am)) t at hprogress
  rwa [hnext] at hprogress

theorem advance_store (hp : Pre copy initial) (hboundary : ¬ InProgram boundary.rip)
    {am : AddrMode} {src : BitVec 5} {slot : Fin 27}
    (hstep : StepEffect (StorePreReadable p (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p bytes) (movM64R64Effect p src am))
    (hin : (p, bytes) ∈ loadInstructionBytes copy) (hlen : bytes.length = 3 + am.tail.length)
    (hnext : p + BitVec.ofNat 64 (3 + am.tail.length) = next)
    (haddr : ∀ s, am.addr s next = stackPtr s + BitVec.ofNat 64 (8 * slot.val))
    (hsrc : src ≠ 4) :
    AdvanceTriple boundary 1 (Progress initial v p) Extracted.programImage
      (fun _ t ↦ Progress initial (execute initial v (.store src slot)) next t) := by
  intro s hready hcode hs
  have ha : storeAddrAt p am (3 + am.tail.length) s = slotAddress initial slot.val := by
    change am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length)) = _
    rw [hnext, haddr, hs.stack]
    rfl
  have hpre : StorePreReadable p (storeAddrAt p am (3 + am.tail.length)) 8 s := by
    refine ⟨⟨hs.rip, ?_⟩, ?_⟩
    · rw [ha]
      exact hs.slot_readable hp slot
    · rw [ha]
      exact fun j hj htable ↦ hp.slot_avoid slot hj (.inr htable)
  have hn : (movM64R64Effect p src am s).rip ≠ boundary.rip := by
    change p + BitVec.ofNat 64 (3 + am.tail.length) ≠ boundary.rip
    rw [← hlen]
    exact fun he ↦ hboundary (he ▸ loadInstruction_next_inProgram copy hin)
  obtain ⟨t, hrun, ht, he⟩ := hstep.advances hready
    (hcode.mono fun x hx ↦ loadCode_subset_programImage copy x
      (loadInstruction_code_subset copy _ hin x hx)) hpre hn
  have hc : (movM64R64Effect p src am s).components =
      [.mem (slotAddress initial slot.val) 8, .rip] := by
    rw [movM64R64Effect_components, ha]
  have hav : (movM64R64Effect p src am s).Avoids Extracted.programImage := by
    intro x hx c hmem hcov
    rw [hc] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hcov
      exact hp.slot_avoid slot hj (.inl (heq ▸ ⟨x.2, hx⟩))
    · exact hcov
  refine ⟨t, hrun, ht, he.codeIn hav hcode, ?_⟩
  have hv : (Operand.mem (slotAddress initial slot.val) : Operand 64).read t =
      v.registers src := by
    have hw := he.writes
    change (Operand.mem (storeAddrAt p am (3 + am.tail.length) s) : Operand 64).read t =
      (Operand.reg src : Operand 64).read s at hw
    rw [ha] at hw
    exact hw.trans (hs.registers src hsrc)
  have hprogress := hs.slot hp he slot (by rw [hc]; exact fun _ h ↦ h) hv
  change Progress initial (execute initial v (.store src slot))
    (p + BitVec.ofNat 64 (3 + am.tail.length)) t at hprogress
  rwa [hnext] at hprogress

theorem advance_clear (_hp : Pre copy initial) (hboundary : ¬ InProgram boundary.rip)
    (hstep : StepEffect (fun s ↦ s.RIP = p) (codeRange p bytes) (xorR32R32Effect p 2 2 2))
    (hin : (p, bytes) ∈ loadInstructionBytes copy) (hlen : bytes.length = 2)
    (hnext : p + 2 = next) :
    AdvanceTriple boundary 1 (Progress initial v p) Extracted.programImage
      (fun _ t ↦ Progress initial (execute initial v .clear) next t) := by
  intro s hready hcode hs
  have hn : (xorR32R32Effect p 2 2 2 s).rip ≠ boundary.rip := by
    change p + BitVec.ofNat 64 2 ≠ boundary.rip
    rw [← hlen]
    exact fun he ↦ hboundary (he ▸ loadInstruction_next_inProgram copy hin)
  obtain ⟨t, hrun, ht, he⟩ := hstep.advances hready
    (hcode.mono fun x hx ↦ loadCode_subset_programImage copy x
      (loadInstruction_code_subset copy _ hin x hx)) hs.rip hn
  refine ⟨t, hrun, ht, he.codeIn (xorR32R32Effect_avoids p 2 2 2 s _) hcode, ?_⟩
  have hv : (Operand.reg 2 : Operand 64).read t = 0 := by
    have hw := he.writes
    simp only [xorR32R32Effect, BitVec.xor_self, Write.AllHold,
      BitVec.setWidth_zero] at hw
    exact hw
  have hprogress := hs.reg he (by decide : (2 : BitVec 5) ≠ 4) (by simp) hv
  change Progress initial (execute initial v .clear) (p + 2) t at hprogress
  rwa [hnext] at hprogress

theorem advance_nop (_hp : Pre copy initial) (hboundary : ¬ InProgram boundary.rip)
    {length : Nat}
    (hstep : StepEffect (fun s ↦ s.RIP = p) (codeRange p bytes) (fun _ ↦ nopEffect p length))
    (hin : (p, bytes) ∈ loadInstructionBytes copy) (hlen : bytes.length = length)
    (hnext : p + BitVec.ofNat 64 length = next) :
    AdvanceTriple boundary 1 (Progress initial v p) Extracted.programImage
      (fun _ t ↦ Progress initial (execute initial v .nop) next t) := by
  intro s hready hcode hs
  have hn : (nopEffect p length).rip ≠ boundary.rip := by
    change p + BitVec.ofNat 64 length ≠ boundary.rip
    rw [← hlen]
    exact fun he ↦ hboundary (he ▸ loadInstruction_next_inProgram copy hin)
  obtain ⟨t, hrun, ht, he⟩ := hstep.advances hready
    (hcode.mono fun x hx ↦ loadCode_subset_programImage copy x
      (loadInstruction_code_subset copy _ hin x hx)) hs.rip hn
  refine ⟨t, hrun, ht, he.codeIn (nopEffect_avoids p length _) hcode, ?_⟩
  have hprogress := hs.noop he (by simp)
  change Progress initial (execute initial v .nop) (p + BitVec.ofNat 64 length) t at hprogress
  rwa [hnext] at hprogress

end Sha3.Proofs.Permutation.Load
