import K256.Proofs.Verify.Wrapper.Inputs
import K256.Proofs.Common.Refine.Lemma.Region

namespace K256.Proofs.Verify.Hash.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Verify.Wrapper

variable {s : RamState} {key message sig : ByteArray} {m : Ram}

def footprint (s : RamState) : List MemoryRegion := [⟨(stackPtr s).toNat - 880, 696⟩]

theorem stackBounds (call : ValidCall verifyingKeyVerify s [key,message,sig]) :
    13000 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 := by
  have depth : 13000 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have low := call.stackAvailable.1
  change (stackPtr s).toNat - 13000 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 13000)) < 2^32 at low
  omega

theorem frameSlot (call : ValidCall verifyingKeyVerify s [key,message,sig])
    {p : BitVec 64} {off len : Nat} (addr : p = stackPtr s - BitVec.ofNat 64 off)
    (depth : off ≤ 880) (fits : len + 184 ≤ off) : InRegions (footprint s) p len := by
  subst p
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  change (stackPtr s).toNat - 880 ≤ _ ∧ _ ≤ (stackPtr s).toNat - 880 + 696 ∧ _
  rw [Common.stackOffset call.stackAvailable (off := off) (show off ≤ 13000 by omega)]
  obtain ⟨room,low⟩ := stackBounds call
  omega

theorem advance (call : ValidCall verifyingKeyVerify s [key,message,sig]) (cur : Memory s m)
    {m' : Ram} (h : RamWriteFrame m m' (footprint s)) : Memory s m' := by
  apply cur.advance call h
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  obtain ⟨room,low⟩ := stackBounds call
  change _ ≤ (stackPtr s).toNat - 880 ∧ (stackPtr s).toNat - 880 + 696 ≤ _
  omega

theorem writable (call : ValidCall verifyingKeyVerify s [key,message,sig]) (cur : Memory s m)
    {p : BitVec 64} {off len : Nat} (addr : p = stackPtr s - BitVec.ofNat 64 off)
    (depth : off ≤ 13000) (fits : len ≤ off + 8) (pos : 0 < len) :
    Writable Extracted.programImage m p len := by
  rw [addr]
  exact (Common.stackWritable call depth fits pos).of_frame cur.frame

theorem messageMemory (call : ValidCall verifyingKeyVerify s [key,message,sig]) (cur : Memory s m) :
    let src := s.regValue .rsi
    (⟨src.toNat,message.size⟩ : MemoryRegion).HasBytes m message ∧
    Readable m src message.size := by
  let msgRegion : MemoryRegion := ⟨(s.regValue .rsi).toNat,message.size⟩
  have valid : ValidInput s msgRegion message := call.inputsInMemory.2.1
  have bytes := (inputMemory call cur.frame).2.1
  refine ⟨bytes, ?_⟩
  simpa only [registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    (Readable.of_hasBytes bytes valid.2.1)

theorem messageApart (call : ValidCall verifyingKeyVerify s [key,message,sig]) (pos : 0 < message.size) :
    (s.regValue .rsi).toNat + message.size ≤ (stackPtr s).toNat - 13000 ∨
      (stackPtr s).toNat + 8 ≤ (s.regValue .rsi).toNat := by
  let msgRegion : MemoryRegion := ⟨(s.regValue .rsi).toNat,message.size⟩
  have disj : (stack s).Disjoint msgRegion := (call.separation.2 _ (List.mem_singleton_self _)).2
    _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have apart := apart_of_disjoint disj (by
    change 0 < (stackPtr s).toNat + 8 - ((stackPtr s).toNat - 13000)
    omega) pos
  change (stackPtr s).toNat - 13000 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 13000)) ≤
    (s.regValue .rsi).toNat ∨ (s.regValue .rsi).toNat + message.size ≤ (stackPtr s).toNat - 13000 at apart
  omega

end K256.Proofs.Verify.Hash.Update
