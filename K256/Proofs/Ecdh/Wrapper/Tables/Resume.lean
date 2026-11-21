import K256.Proofs.Ecdh.Wrapper.Tables.Memory
import K256.Proofs.Ecdh.Scalar.Calls
import K256.Proofs.Ecdh.Transfer
import K256.Proofs.Ecdh.Multiply.Loop.Local
import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Tables

namespace K256.Proofs.Ecdh.Wrapper.Tables

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR Generate.Generator.Multiply.Caller

open_generator_loop Body.Tables (windowMemcpyArgWidths)

theorem resume {l next : Label} {a b : Arguments} {initial m : Ram} {sp ret : BitVec 64}
    {dst src len : Nat}
    (window : Writable Extracted.programImage m (sp - 8) 6112)
    (dfit : dst + len ≤ 6104) (sfit : src + len ≤ 6104)
    (sep : dst + len ≤ src ∨ src + len ≤ dst) (low : ret.toNat < 2^32)
    (call : program.runBlock (dialect Extracted.programImage) ⟨l,a,initial⟩ =
      .call ⟨.l12a820, b, memStore m (sp - 8) ret⟩ (callFrame next ret))
    (rsp : b[4].get 64 = sp - 8) (rdi : b[7].get 64 = sp + BitVec.ofNat 64 dst)
    (rsi : b[6].get 64 = sp + BitVec.ofNat 64 src) (rdx : b[2].get 64 = BitVec.ofNat 64 len)
    (df : b[22].get 1 = 0) (r9 : b[9].width = 64) :
    ∃ c, Reaches l a initial next c (callMemory m sp ret dst src len) ∧
      c[4] = ⟨64, sp⟩ ∧ ParseSignature.ArgumentWidths c ∧
      ∀ i : Fin Reg.count, i.val ∈ memcpyPreserved → c[i] = b[i] := by
  let pushed := memStore m (sp - 8) ret
  have shifted (n : Nat) (small : n ≤ 6104) :
      (BitVec.ofNat 64 n - (0 - 8)).toNat = n + 8 := by
    rw [show BitVec.ofNat 64 n - (0 - 8) = BitVec.ofNat 64 (n + 8) by rw [BitVec.ofNat_add]; bv_omega]
    exact Nat.mod_eq_of_lt (by omega)
  have count : (BitVec.ofNat 64 len).toNat = len := Nat.mod_eq_of_lt (by omega)
  have fit (k : Nat) (h : k + len ≤ 6104) :
      (BitVec.ofNat 64 k - (0 - 8)).toNat + (BitVec.ofNat 64 len).toNat ≤ 6112 := by
    rw [shifted k (by omega), count]
    omega
  have d := window.of_offsets (rfl : sp + BitVec.ofNat 64 dst = _) (addr_sub sp 8) (fit dst dfit)
  have r := window.readable.of_offsets (rfl : sp + BitVec.ofNat 64 src = _) (addr_sub sp 8) (fit src sfit)
  have dn := toNat_of_offsets (rfl : sp + BitVec.ofNat 64 dst = _) (addr_sub sp 8) window.readable.low (fit dst dfit)
  have sn := toNat_of_offsets (rfl : sp + BitVec.ofNat 64 src = _) (addr_sub sp 8) window.readable.low (fit src sfit)
  rw [shifted dst (by omega)] at dn
  rw [shifted src (by omega)] at sn
  have bound := window.readable.low
  have slot : Readable m (sp - 8) 8 := window.readable.sub (Nat.le_refl _) (by omega)
  have tag : memLoad pushed (sp - 8) 64 = ret := memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨out, run, store, gate, _, back, keep⟩ := Generate.Serialize.memcpy rdi rsi rdx rsp df
    (r.memStore _ ret) (d.memStore _ ret) (by omega) (RangeApart.of_toNat (by omega) (by omega) (by omega))
    (slot.memStore _ ret) (tag ▸ low)
  have widths := windowMemcpyArgWidths run r9
  have path := Scalar.resumeCall call (Ecdh.Transfer.generateExec (by decide) rfl run) (tag ▸ gate)
  rw [count] at store
  exact ⟨out.values, by unfold callMemory; rw [← store]; exact path, by simpa only [BitVec.sub_add_cancel] using back, widths, keep⟩

end K256.Proofs.Ecdh.Wrapper.Tables
