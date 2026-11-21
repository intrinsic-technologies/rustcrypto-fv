import K256.Proofs.Common.CallMemory
import K256.Proofs.Common.Finish
import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Verify.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

abbrev localSp (s : RamState) := stackPtr s - 536

abbrev stack (s : RamState) := Stack.region s verifyingKeyVerify.minStackBytes

def parserMemory (s : RamState) : Ram :=
  let sp := stackPtr s
  let m := memStore s.external (sp - 8) (s.regValue .r15)
  let m := memStore m (sp - 16) (s.regValue .r14)
  let m := memStore m (sp - 24) (s.regValue .r12)
  let m := memStore m (sp - 32) (s.regValue .rbx)
  memStore m (sp - 544) (0x102fe9 : BitVec 64)

structure Saved (s : RamState) (m : Ram) : Prop where
  r15 : memLoad m (stackPtr s - 8) 64 = s.regValue .r15
  r14 : memLoad m (stackPtr s - 16) 64 = s.regValue .r14
  r12 : memLoad m (stackPtr s - 24) 64 = s.regValue .r12
  rbx : memLoad m (stackPtr s - 32) 64 = s.regValue .rbx
  ret : memLoad m (stackPtr s) 64 = (returnBoundary s).rip

structure Memory (s : RamState) (m : Ram) : Prop where
  frame : RamWriteFrame s.external m [stack s]
  saved : Saved s m

theorem parserMemory_state {s : RamState} {key message signature : ByteArray}
    (call : ValidCall verifyingKeyVerify s [key, message, signature]) :
    Memory s (parserMemory s) ∧ memLoad (parserMemory s) (stackPtr s - 544) 64 = 0x102fe9 := by
  have push {m : Ram} {off : Nat} (depth : off ≤ 13000) (v : BitVec 64)
      (w : RamWriteFrame s.external m [stack s]) :
      RamWriteFrame s.external (memStore m (stackPtr s - BitVec.ofNat 64 off) v) [stack s] :=
    w.memStore v ⟨_, List.mem_cons_self, Common.stackRange call.stackAvailable depth (by omega)⟩
  refine ⟨⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
  · exact push (off := 544) (by decide) _ (push (off := 32) (by decide) _
      (push (off := 24) (by decide) _ (push (off := 16) (by decide) _
        (push (off := 8) (by decide) _ (.refl _ _)))))
  all_goals unfold parserMemory
  all_goals first | change _ = memLoad s.external (stackPtr s) 64 | skip
  all_goals simp (disch := store_disch) only [memLoad_memStore_same, memLoad_memStore_of_rangeApart]

theorem Memory.advance {s : RamState} {key message signature : ByteArray} {m n : Ram}
    (cur : Memory s m) (call : ValidCall verifyingKeyVerify s [key, message, signature])
    {rs : List MemoryRegion} (writes : RamWriteFrame m n rs)
    (bounds : ∀ r ∈ rs, (stackPtr s).toNat - 13000 ≤ r.start ∧
      r.start + r.size ≤ (stackPtr s).toNat - 32) : Memory s n := by
  have depth : 13000 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have low := call.stackAvailable.1
  change (stackPtr s).toNat - 13000 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 13000)) < 2^32 at low
  have slot (off : Nat) (h : off ≤ 32) :
      memLoad n (stackPtr s - BitVec.ofNat 64 off) 64 =
      memLoad m (stackPtr s - BitVec.ofNat 64 off) 64 := by
    apply writes.memLoad_eq
    have addr := Common.stackOffset call.stackAvailable (off := off) (show off ≤ 13000 by omega)
    refine ⟨by rw [addr]; omega, fun r hr => Or.inr ?_⟩
    rw [addr]
    have := (bounds r hr).2
    omega
  refine ⟨cur.frame.trans writes ?_, (slot 8 (by decide)).trans cur.saved.r15,
    (slot 16 (by decide)).trans cur.saved.r14, (slot 24 (by decide)).trans cur.saved.r12,
    (slot 32 (by decide)).trans cur.saved.rbx, ?_⟩
  · intro r hr
    obtain ⟨lo, hi⟩ := bounds r hr
    refine ⟨_, List.mem_singleton_self _, lo, ?_⟩
    change _ ≤ (stackPtr s).toNat - 13000 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 13000))
    omega
  · simpa using (slot 0 (by decide)).trans (by simpa using cur.saved.ret)

end K256.Proofs.Verify.Wrapper
