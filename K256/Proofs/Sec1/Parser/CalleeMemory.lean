import K256.Proofs.Sec1.Parser.HeaderReturn
import K256.Proofs.Sec1.Parser.Packing.CopyInput

namespace K256.Proofs.Sec1.Parser

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine K256.Spec.Program Prelude

private theorem savedSlots_of_lowerWrites {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    {m m' : Ram} (slots : Result.SavedSlots s m) {regions : List MemoryRegion}
    (frame : RamWriteFrame m m' regions)
    (bounds : ∀ r ∈ regions, (s.regValue .rsp).toNat - 1928 ≤ r.start ∧
      r.start + r.size ≤ (s.regValue .rsp).toNat - 288) : Result.SavedSlots s m' := by
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have low := call.stackAvailable.1
  change (s.regValue .rsp).toNat - 1928 + ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 1928)) < 2^32 at low
  have load (off : BitVec 64) (small : off.toNat ≤ 280) :
      memLoad m' (s.regValue .rsp - off) 64 = memLoad m (s.regValue .rsp - off) 64 := by
    have addr : (s.regValue .rsp - off).toNat = (s.regValue .rsp).toNat - off.toNat :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    apply frame.memLoad_eq
    refine ⟨by rw [addr]; omega, fun r hr => Or.inr ?_⟩
    have := (bounds r hr).2
    rw [addr]
    omega
  have zero := load 0 (by decide)
  rw [show s.regValue .rsp - (0 : BitVec 64) = s.regValue .rsp by bv_omega] at zero
  refine ⟨(load 264 (by decide)).trans slots.savedR15, (load 272 (by decide)).trans slots.savedR14,
    (load 280 (by decide)).trans slots.savedR12, (load 256 (by decide)).trans slots.parserRet,
    (load 16 (by decide)).trans slots.wrapperRbx, (load 8 (by decide)).trans slots.wrapperR14,
    zero.trans slots.wrapperRet, slots.writes.trans frame ?_⟩
  intro r hr
  refine ⟨_, List.mem_cons_self, (bounds r hr).1, ?_⟩
  change r.start + r.size ≤ (s.regValue .rsp).toNat - 1928 +
    ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 1928))
  have := (bounds r hr).2
  omega

theorem packingSavedSlots {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    {m : Ram} (frame : RamWriteFrame (headerMemory s) m [Packing.packingWindow (s.regValue .rsp - 600)]) :
    Result.SavedSlots s m := by
  apply savedSlots_of_lowerWrites call (headerSavedSlots call) frame
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  change (s.regValue .rsp).toNat - 1928 ≤ ((s.regValue .rsp - 600) - 8).toNat ∧
    ((s.regValue .rsp - 600) - 8).toNat + 233 ≤ (s.regValue .rsp).toNat - 288
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  rw [show s.regValue .rsp - 600 - 8 = s.regValue .rsp - 608 by bv_omega,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 608 ≤ _; omega)]
  change _ ≤ (s.regValue .rsp).toNat - 608 ∧ (s.regValue .rsp).toNat - 608 + 233 ≤ _
  omega

def affineWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp - 1200).toNat, 1192⟩, ⟨(sp + 160).toNat, 89⟩]

theorem affineSavedSlots {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    {m m' : Ram} (slots : Result.SavedSlots s m) (frame : RamWriteFrame m m' (affineWrites (s.regValue .rsp - 600))) :
    Result.SavedSlots s m' := by
  apply savedSlots_of_lowerWrites call slots frame
  intro r hr
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have addr (off : BitVec 64) (small : off.toNat ≤ 1928) :
      (s.regValue .rsp - off).toNat = (s.regValue .rsp).toNat - off.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  simp only [affineWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · dsimp only
    rw [show s.regValue .rsp - 600 - 1200 = s.regValue .rsp - 1800 by bv_omega, addr 1800 (by decide)]
    change _ ≤ (s.regValue .rsp).toNat - 1800 ∧ (s.regValue .rsp).toNat - 1800 + 1192 ≤ _
    omega
  · dsimp only
    rw [show s.regValue .rsp - 600 + 160 = s.regValue .rsp - 440 by bv_omega, addr 440 (by decide)]
    change _ ≤ (s.regValue .rsp).toNat - 440 ∧ (s.regValue .rsp).toNat - 440 + 89 ≤ _
    omega

theorem affineTagUnchanged {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) {m m' : Ram}
    (sp : BitVec 64) (body : sp = s.regValue .rsp - 600)
    (frame : RamWriteFrame m m' (affineWrites sp)) :
    memLoad m' (sp + 4) 8 = memLoad m (sp + 4) 8 := by
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have start : sp.toNat = (s.regValue .rsp).toNat - 600 := by
    rw [body, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 600 ≤ _; omega)]
    rfl
  have h₁ : (sp - 1200).toNat = sp.toNat - 1200 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1200 ≤ _; omega)]; rfl
  have h₂ : (sp + 160).toNat = sp.toNat + 160 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change sp.toNat + 160 < 2^64; have := (s.regValue .rsp).isLt; omega)]
    rfl
  have h₃ : (sp + 4).toNat = sp.toNat + 4 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change sp.toNat + 4 < 2^64; have := (s.regValue .rsp).isLt; omega)]
    rfl
  apply frame.memLoad_eq
  refine ⟨by rw [h₃]; have := (s.regValue .rsp).isLt; omega, ?_⟩
  intro r hr
  simp only [affineWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inr (by dsimp only; rw [h₁, h₃]; omega)
  · exact Or.inl (by dsimp only; rw [h₂, h₃]; omega)

end K256.Proofs.Sec1.Parser
