import K256.Proofs.Sec1.Wrapper.Entry
import K256.Proofs.Common.Refine.Lemma.Frame

namespace K256.Proofs.Sec1.Parser

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Spec.Program Prelude

theorem stackRange {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    {off n : Nat} (depth : off ≤ 1928) (fits : n ≤ off + 8) :
    InRegions [Stack.region s publicKeyFromSec1Bytes.minStackBytes]
      (s.regValue .rsp - BitVec.ofNat 64 off) n := by
  have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
  have low := call.stackAvailable.1
  change (s.regValue .rsp).toNat - 1928 + ((s.regValue .rsp).toNat + 8 -
    ((s.regValue .rsp).toNat - 1928)) < 2^32 at low
  have index : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
  have start : (s.regValue .rsp - BitVec.ofNat 64 off).toNat = (s.regValue .rsp).toNat - off := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, index]; omega), index]
  refine ⟨_, List.mem_cons_self, ?_⟩
  change (s.regValue .rsp).toNat - 1928 ≤ _ ∧ _ + n ≤
    (s.regValue .rsp).toNat - 1928 + ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 1928)) ∧
    _ + n ≤ 2 ^ 64
  rw [start]
  omega

theorem parserMemory_frame {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes]) :
    RamWriteFrame s.external (Wrapper.parserMemory s) [Stack.region s publicKeyFromSec1Bytes.minStackBytes] :=
  (((RamWriteFrame.refl _ _).memStore _ (stackRange (off := 8) call (by decide) (by decide))).memStore _
    (stackRange (off := 16) call (by decide) (by decide))).memStore _
    (stackRange (off := 256) call (by decide) (by decide))

theorem inputs_of_stackFrame {s : RamState} {bytes : ByteArray} {mem : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (frame : RamWriteFrame s.external mem [Stack.region s publicKeyFromSec1Bytes.minStackBytes]) :
    (registerRegion s .rsi bytes.size).HasBytes mem bytes ∧
    ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2 := by
  let t := { s with external := mem }
  let stack := Stack.region s publicKeyFromSec1Bytes.minStackBytes
  let region := registerRegion s .rsi bytes.size
  have valid : ValidInput s region bytes := call.inputsInMemory.1
  have sep : MemorySeparation [outputRegion publicKeyFromSec1Bytes s, stack] [region] := call.separation
  obtain ⟨avoids, apart⟩ := sep.2 stack (by simp)
  have writes : MemoryWriteFrame s t #v[stack] :=
    RamWriteFrame.memoryWriteFrame frame (fun _ none _ hr => none _ (by simpa only [List.mem_singleton,
      Vector.mem_singleton] using hr))
  refine ⟨Common.hasBytes_of_memoryWriteFrame writes valid.2.2 valid.2.1 ?_, ?_⟩
  · intro r hr x hin
    obtain rfl := Vector.mem_singleton.mp hr
    exact fun hs => apart region List.mem_cons_self x hs hin
  · have loaded := Common.programLoaded_of_memoryWriteFrame writes call.programLoaded (by
      intro r hr
      obtain rfl := Vector.mem_singleton.mp hr
      exact fun a hs h => avoids a hs (Or.inl h))
    exact fun x hx => loaded x.1 x.2 (Common.programSections_fetchByte_of_mem hx)

end K256.Proofs.Sec1.Parser
