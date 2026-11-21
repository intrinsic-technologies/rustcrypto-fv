import K256.Proofs.Generate.Generator.Multiply.Loop.Memory
import K256.Proofs.Ecdh.Multiply.Loop.State

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem PeerWindowMemory.of_frame {fr : Activation} {m n : Ram} {d : Nat} {peer : Projective} {writes : List MemoryRegion}
    (s : PeerWindowMemory fr m d peer) (frame : RamWriteFrame m n writes)
    (within : RegionsWithin writes (coreWrites fr))
    (left : Outside writes fr.rcx 960) (right : Outside writes (fr.rcx + 960) 960)
    (first : Outside writes fr.r9 33) (second : Outside writes (fr.r9 + 33) 33)
    (slots : ∀ offset ∈ ([0x1a0,0x1c0,0x1c8,0x248,0x258,0x260,0x268] : List (BitVec 64)),
      Outside writes (fr.rsp - 0xcb8 + offset) 8) : PeerWindowMemory fr n d peer := by
  have digits {base : BitVec 64} {v : Vector (BitVec 8) 33}
      (out : Outside writes base 33) (old : WordsAt m base 8 v) : WordsAt n base 8 v := by
    intro i hi
    apply (frame.memLoad_eq _).trans (old i hi)
    have room := out.1
    have addr : (wordAddr base 8 i).toNat = base.toNat + i := by
      simp only [wordAddr, Nat.reduceDiv, Nat.one_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show i < 2^64 by omega), Nat.mod_eq_of_lt (show base.toNat + i < 2^64 by omega)]
    exact Affine.outside_subregion out (by omega) (by change _ + 1 ≤ _; omega)
  refine ⟨s.frame.trans frame within,s.firstTable.of_frame frame left,s.secondTable.of_frame frame right,
    digits first s.firstDigits,digits second s.secondDigits,?_⟩
  intro kv hk
  apply (frame.memLoad_eq (slots kv.1 ?_)).trans (s.locals kv hk)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

end K256.Proofs.Generate.Generator.Multiply
