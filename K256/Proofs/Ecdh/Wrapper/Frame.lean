import K256.Proofs.Common.CallMemory
import K256.Proofs.Common.Finish
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

abbrev regions (initial : RamState) :=
  #v[outputRegion ecdhDiffieHellman initial, Stack.region initial ecdhDiffieHellman.minStackBytes]

abbrev localSp (initial : RamState) := initial.regValue .rsp - 6152

def savedSlots : List (Nat × Syntax.Reg) :=
  [(8, .rbp), (16, .r15), (24, .r14), (32, .r13), (40, .r12), (48, .rbx)]

structure Saved (initial : RamState) (mem : Ram) : Prop where
  registers : ∀ kv ∈ savedSlots,
    memLoad mem (initial.regValue .rsp - BitVec.ofNat 64 kv.1) 64 = initial.regValue kv.2
  ret : memLoad mem (initial.regValue .rsp) 64 = (returnBoundary initial).rip

theorem Saved.of_frame {s : RamState} {secret peer : ByteArray} {m n : Ram}
    {footprint : List MemoryRegion} (saved : Saved s m)
    (call : ValidCall ecdhDiffieHellman s [secret, peer]) (frame : RamWriteFrame m n footprint)
    (below : ∀ r ∈ footprint, r.start + r.size ≤ (s.regValue .rsp).toNat - 48) : Saved s n := by
  have room : 10088 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have low := call.stackAvailable.1
  change (s.regValue .rsp).toNat - 10088 + ((s.regValue .rsp).toNat + 8 -
    ((s.regValue .rsp).toNat - 10088)) < 2^32 at low
  have slot (off : Nat) (h : off ≤ 48) :
      memLoad n (s.regValue .rsp - BitVec.ofNat 64 off) 64 =
      memLoad m (s.regValue .rsp - BitVec.ofNat 64 off) 64 := by
    apply frame.memLoad_eq
    have addr := Common.stackOffset call.stackAvailable (off := off)
      (show off ≤ 10088 by omega)
    change (s.regValue .rsp - BitVec.ofNat 64 off).toNat = (s.regValue .rsp).toNat - off at addr
    refine ⟨by rw [addr]; omega, fun r hr => Or.inr ?_⟩
    rw [addr]
    have := below r hr
    omega
  constructor
  · intro kv h
    apply (slot _ ?_).trans (saved.registers kv h)
    simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simpa using (slot 0 (by decide)).trans (by simpa using saved.ret)

end K256.Proofs.Ecdh.Wrapper
