import K256.Proofs.Signing.Composition.Memory
import K256.Proofs.Signing.Composition.Reach
import K256.Proofs.Signing.Nonce.Start
import K256.Proofs.Signing.Transfer.Verify

namespace K256.Proofs.Signing.Composition

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)

theorem initializeNonce {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (decoded : Keys.decodeSecret domain secret = some d)
    {a : Registers} {m : Ram} (entry : Digest s d msg a m) :
    ∃ b n, Reach (core .l105758 a m) (core .l105886 b n) ∧ Outer s d msg (initialNonceState d msg) b n := by
  obtain ⟨room, limit, spNat⟩ := stackBounds call
  have depth : 2232 ≤ (sp s).toNat := by omega
  have low : (sp s).toNat + 1160 < 2^32 := by omega
  have align : (sp s).toNat % 16 = 0 := by
    have entryAlign := call.stackAvailable.2.2.2
    change (stackPtr s).toNat % 16 = 8 at entryAlign
    rw [spNat]
    omega
  have stackBase : (stackPtr s - 11192).toNat = (stackPtr s).toNat - 11192 :=
    Common.stackOffset (off := 11192) call.stackAvailable (by decide)
  have initBase : (sp s - 2232).toNat = (sp s).toNat - 2232 :=
    BitVec.toNat_sub_of_le (show (2232 : BitVec 64) ≤ sp s from depth)
  have stack : Writable Extracted.programImage m (sp s - 2232) 3392 :=
    (entry.toMemory.window call).sub (by rw [stackBase, initBase]; omega)
      (by rw [stackBase, initBase]; omega)
  have valid : 0 < d ∧ d < domain.n := by
    dsimp only [Keys.decodeSecret] at decoded
    split at decoded
    next good =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at good
      obtain rfl := Option.some.inj decoded
      exact ⟨good.1.2, good.2⟩
    next => contradiction
  obtain ⟨b,n,run,regs,fp,writes,digest,order,ptr,state⟩ :=
    Nonce.start entry.rsp entry.df entry.r13 entry.widths entry.fp.1 entry.fp.2.1 entry.fp.2.2
      (entry.toMemory.image call) stack depth low align entry.hash entry.keyPtr entry.key valid.1 valid.2
  have inside : RegionsWithin (Nonce.initializationRegions (sp s))
      [Stack.region s signingKeyTrySign.minStackBytes] := by
    rw [stackRegion call]
    intro r hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    simp only [Nonce.initializationRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [stackBase] <;> omega
  have apart : ∀ i ∈ protectedOffsets,
      Outside (Nonce.initializationRegions (sp s)) (sp s + BitVec.ofNat 64 i) 8 := by
    intro i hi
    simp only [protectedOffsets, List.mem_cons, List.not_mem_nil, or_false] at hi
    have ilt : i ≤ 1288 := by omega
    have addr : (sp s + BitVec.ofNat 64 i).toNat = (sp s).toNat + i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨by rw [addr]; omega, ?_⟩
    intro r hr
    simp only [Nonce.initializationRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [addr] <;> omega
  have lifted := Transfer.verifyReaches
    (src := .l105758) (dst := .l105758) (src' := .l105886) (dst' := .l105886)
    (by simp only [Transfer.sharedLabels, List.mem_cons, true_or, or_true])
    (by simp only [Transfer.sharedLabels, List.mem_cons, true_or, or_true]) run
  exact ⟨b,n,appendStack lifted [resume .l102795 0x102795],
    ⟨entry.toCoreMemory.preserve writes inside apart, regs,
      ⟨(congrArg Value.width (fp 39 (by decide))).trans entry.fp.1,
       (congrArg Value.width (fp 50 (by decide))).trans entry.fp.2.1,
       (congrArg Value.width (fp 51 (by decide))).trans entry.fp.2.2⟩,
      digest, order, ptr, state⟩⟩

end K256.Proofs.Signing.Composition
