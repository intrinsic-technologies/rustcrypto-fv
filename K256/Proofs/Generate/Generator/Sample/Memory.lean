import K256.Proofs.Generate.Generator.Sample.State
import K256.Proofs.Common.Refine.Lemma.Region

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

variable {s : RamState} {random : ByteArray} {fr : Activation} {a : Registers}

theorem regionsWithinStack (call : ValidCall signingKeyGenerateFromRng s [random])
    (entry : Entry s fr a) :
    RegionsWithin (regions fr) [Stack.region s signingKeyGenerateFromRng.minStackBytes] := by
  intro r hr
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  have room : 10584 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  have sp : s.regValue .rsp = stackPtr s := rfl
  have hlow : (stackPtr s - 10584).toNat = (stackPtr s).toNat - 10584 :=
    stackOffset (off := 10584) call (by decide)
  have hsp : (stackPtr s - 288).toNat = (stackPtr s).toNat - 288 :=
    stackOffset (off := 288) call (by decide)
  have hdesc : (stackPtr s - 208).toNat = (stackPtr s).toNat - 208 :=
    stackOffset (off := 208) call (by decide)
  rcases hr with rfl | rfl
  · change (stackPtr s).toNat - 10584 ≤ fr.low.toNat ∧
      fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤
      (stackPtr s).toNat - 10584 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 10584))
    rw [entry.low, entry.rsp, sp, hlow, hsp]
    omega
  · change (stackPtr s).toNat - 10584 ≤ fr.rsi.toNat ∧ fr.rsi.toNat + 16 ≤
      (stackPtr s).toNat - 10584 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 10584))
    rw [entry.descriptor, sp, hdesc]
    omega

theorem stackFrame (call : ValidCall signingKeyGenerateFromRng s [random])
    (entry : Entry s fr a) {mem : Ram} (frame : RamWriteFrame fr.original mem (regions fr)) :
    RamWriteFrame s.external mem [Stack.region s signingKeyGenerateFromRng.minStackBytes] :=
  entry.writes.trans frame (regionsWithinStack call entry)

theorem stackWritableAt (call : ValidCall signingKeyGenerateFromRng s [random])
    (entry : Entry s fr a) {mem : Ram} (frame : RamWriteFrame fr.original mem (regions fr))
    {off len : Nat} (depth : off ≤ 10584) (fits : len ≤ off + 8) (pos : 0 < len) :
    Writable Extracted.programImage mem (stackPtr s - BitVec.ofNat 64 off) len :=
  ((stackWritable call depth fits pos).of_frame entry.writes).of_frame frame

theorem inputLoad (call : ValidCall signingKeyGenerateFromRng s [random])
    {mem : Ram} (frame : RamWriteFrame s.external mem [Stack.region s signingKeyGenerateFromRng.minStackBytes])
    (off : Nat) (fits : off + 8 ≤ random.size) :
    let addr := s.regValue .rsi + BitVec.ofNat 64 off
    LoadOk mem addr 8 ∧ memLoad mem addr 64 = memLoad s.external addr 64 := by
  let r := registerRegion s .rsi random.size
  let stack := Stack.region s signingKeyGenerateFromRng.minStackBytes
  have hr : ValidInput s r random := call.inputsInMemory.1
  have low : (s.regValue .rsi).toNat + random.size < 2^32 := hr.2.1
  have haddr : (s.regValue .rsi + BitVec.ofNat 64 off).toNat = (s.regValue .rsi).toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  have read := Readable.of_hasBytes hr.2.2 hr.2.1
  change Readable s.external (BitVec.ofNat 64 (s.regValue .rsi).toNat) random.size at read
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at read
  have sep : MemorySeparation [outputRegion signingKeyGenerateFromRng s, stack] [r] := call.separation
  have disj := (sep.2 stack (by simp)).2 r List.mem_cons_self
  have apart := apart_of_disjoint disj (by
    change 0 < (stackPtr s).toNat + 8 - ((stackPtr s).toNat - 10584)
    omega) (by change 0 < random.size; omega)
  change stack.start + stack.size ≤ (s.regValue .rsi).toNat ∨
    (s.regValue .rsi).toNat + random.size ≤ stack.start at apart
  exact ⟨LoadOk.of_region (read.of_frame frame) (by rw [haddr]; omega) (by rw [haddr]; omega),
    frame.memLoad_eq ⟨by rw [haddr]; omega, fun x hx => by
      obtain rfl := List.mem_singleton.mp hx
      change (s.regValue .rsi + BitVec.ofNat 64 off).toNat + 8 ≤ stack.start ∨
        stack.start + stack.size ≤ (s.regValue .rsi + BitVec.ofNat 64 off).toNat
      rw [haddr]
      omega⟩⟩

end K256.Proofs.Generate.Generator.Sample
