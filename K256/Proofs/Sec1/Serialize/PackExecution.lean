import K256.Proofs.Sec1.Serialize.Pack
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Sec1.Serialize

open Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

private def packWriteAddr (dst : BitVec 64) (i : Nat) : BitVec 64 :=
  if i = 0 then dst else wordAddr dst 64 i

private theorem packWriteAddr_eq (dst : BitVec 64) (i : Nat) :
    packWriteAddr dst i = wordAddr dst 64 i := by
  by_cases hi : i = 0
  · subst i
    exact (BitVec.add_zero dst).symm
  · simp only [packWriteAddr, hi, ite_false]

private def writePackedWords (mem : Ram) (dst : BitVec 64)
    (words : Vector (BitVec 64) 4) (n : Nat) (hn : n ≤ 4) : Ram :=
  match n with
  | 0 => mem
  | n + 1 => memStore (writePackedWords mem dst words n (by omega))
      (packWriteAddr dst n) words[n]

private theorem packAddress {mem : Ram} {base : BitVec 64} {len i : Nat}
    (hr : Readable mem base len) (hi : 8 * i + 8 ≤ len) :
    (wordAddr base 64 i).toNat = base.toNat + 8 * i := by
  have hl := hr.low
  simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 8 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem packReadOk {mem : Ram} {base : BitVec 64} {len i : Nat}
    (hr : Readable mem base len) (hi : 8 * i + 8 ≤ len) : LoadOk mem (wordAddr base 64 i) 8 :=
  LoadOk.of_region hr (by rw [packAddress hr hi]; omega) (by rw [packAddress hr hi]; omega)

private theorem packWriteFrame {mem : Ram} {dst : BitVec 64}
    (hr : Readable mem dst 32) (words : Vector (BitVec 64) 4) (n : Nat) (hn : n ≤ 4) :
    RamWriteFrame mem (writePackedWords mem dst words n hn) [⟨dst.toNat, 32⟩] := by
  induction n with
  | zero => exact RamWriteFrame.refl _ _
  | succ n ih =>
    change RamWriteFrame mem (memStore (writePackedWords mem dst words n (by omega))
      (packWriteAddr dst n) words[n]) [⟨dst.toNat, 32⟩]
    apply (ih (by omega)).memStore
    refine ⟨⟨dst.toNat, 32⟩, List.mem_singleton_self _, ?_⟩
    change dst.toNat ≤ (packWriteAddr dst n).toNat ∧
      (packWriteAddr dst n).toNat + 8 ≤ dst.toNat + 32 ∧
      (packWriteAddr dst n).toNat + 8 ≤ 2 ^ 64
    have hl := hr.low
    rw [packWriteAddr_eq, packAddress hr (by omega)]
    omega

private theorem packedWordsAt {mem : Ram} {dst : BitVec 64}
    (hr : Readable mem dst 32) (words : Vector (BitVec 64) 4) (n : Nat) (hn : n ≤ 4)
    (i : Nat) (hi : i < n) :
    memLoad (writePackedWords mem dst words n hn) (wordAddr dst 64 i) 64 = words[i] := by
  induction n with
  | zero => omega
  | succ n ih =>
    change memLoad (memStore (writePackedWords mem dst words n (by omega))
      (packWriteAddr dst n) words[n]) (wordAddr dst 64 i) 64 = _
    rw [packWriteAddr_eq]
    by_cases h : i = n
    · subst i
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rw [memLoad_memStore_of_rangeApart]
      · exact ih (by omega) (by omega)
      · have hl := hr.low
        apply RangeApart.of_toNat <;>
          simp only [packAddress hr (by omega : 8 * i + 8 ≤ 32),
            packAddress hr (by omega : 8 * n + 8 ≤ 32), Nat.reduceDiv] <;> omega

theorem packExecution {code : CodeMap}
    (hcode : ∀ x ∈ codeRange 0x1148d0 bytes_l1148d0, x ∈ code)
    {args : Vector Value Reg.count} {mem : Ram} {sp src dst ret : BitVec 64}
    {a : Vector (BitVec 64) 5}
    (hsp : args[4] = ⟨64, sp⟩) (hsrc : args[6] = ⟨64, src⟩) (hdst : args[7] = ⟨64, dst⟩)
    (hr : Readable mem src 40) (hw : Writable code mem dst 32)
    (hwords : WordsAt mem src 64 a)
    (hretRead : Readable mem sp 8) (hret : memLoad mem sp 64 = ret)
    (hretLow : ret.toNat < 2 ^ 32)
    (hsep : sp.toNat + 8 ≤ dst.toNat ∨ dst.toNat + 32 ≤ sp.toNat) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l1148d0, args, mem⟩, []⟩ out ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧ out.values[0] = ⟨64, dst⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 5, 7, 11, 12, 13, 14, 15, 22, 39, 50, 51] →
        out.values[i] = args[i]) ∧
      RamWriteFrame mem out.store [⟨dst.toNat, 32⟩] ∧
      WordsAt out.store dst 64 (packWords a) := by
  let writes (n : Nat) (hn : n ≤ 4) := writePackedWords mem dst (packWords a) n hn
  have frame (n : Nat) (hn : n ≤ 4) : RamWriteFrame mem (writes n hn) [⟨dst.toNat, 32⟩] :=
    packWriteFrame hw.readable _ n hn
  have hload (i : Nat) (hi : i < 5) : LoadOk mem (wordAddr src 64 i) 8 :=
    packReadOk hr (by omega)
  have hstore (i off len : Nat) (hi : i < 4) (hof : off + len ≤ bytes_l1148d0.length) :
      StoreOk code (writes i (by omega)) (packWriteAddr dst i) 8
        (0x1148d0 + BitVec.ofNat 64 off) len := by
    rw [packWriteAddr_eq]
    exact ParseSignature.storeOk_of_codeRange
      ((hw.of_frame (frame i (by omega))).sub
        (by rw [packAddress hw.readable (by omega)]; omega)
        (by rw [packAddress hw.readable (by omega)]; omega))
      hcode hof
  have hreturnRead : LoadOk (writes 4 (by decide)) sp 8 :=
    let hr' := hretRead.of_frame (frame 4 (by decide))
    ⟨hr'.low, hr'.present⟩
  have hreturn : memLoad (writes 4 (by decide)) sp 64 = ret := by
    rw [(frame 4 (by decide)).memLoad_eq, hret]
    exact ⟨by have := hretRead.low; omega, by simpa only [List.mem_singleton, forall_eq] using hsep⟩
  have load0 : LoadOk mem src 8 :=
    LoadOk.of_region hr (Nat.le_refl _) (by omega)
  have load1 : LoadOk mem (src + 8) 8 := hload 1 (by decide)
  have load2 : LoadOk mem (src + 16) 8 := hload 2 (by decide)
  have load3 : LoadOk mem (src + 24) 8 := hload 3 (by decide)
  have load4 : LoadOk mem (src + 32) 8 := hload 4 (by decide)
  have word0 : memLoad mem src 64 = a[0] := by
    simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using hwords 0 (by decide)
  have word1 : memLoad mem (src + 8) 64 = a[1] := hwords 1 (by decide)
  have word2 : memLoad mem (src + 16) 64 = a[2] := hwords 2 (by decide)
  have word3 : memLoad mem (src + 24) 64 = a[3] := hwords 3 (by decide)
  have word4 : memLoad mem (src + 32) 64 = a[4] := hwords 4 (by decide)
  have hspBits : Value.get 64 args[4] = sp := congrArg (Value.get 64) hsp
  have hsrcBits : Value.get 64 args[6] = src := congrArg (Value.get 64) hsrc
  have hdstBits : Value.get 64 args[7] = dst := congrArg (Value.get 64) hdst
  have evaluate : ∃ out,
      program.runBlock (dialect code) ⟨.l1148d0, args, mem⟩ = .returned out ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧ out.values[0] = ⟨64, dst⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 5, 7, 11, 12, 13, 14, 15, 22, 39, 50, 51] →
        out.values[i] = args[i]) ∧
      out.store = writes 4 (by decide) := by
    refine ⟨?_, ?eval, ?tag, ?stack, ?result, ?regs, ?store⟩
    case eval =>
      cfg_eval [b_l1148d0_1, hspBits, hsrcBits, hdstBits]
      simp only [load0, load1, load2, load3, load4, word0, word1, word2, word3, word4, ↓reduceIte]
      refine (ite_eq_left (hstore 0 80 3 (by decide) (by decide))).trans ?_
      refine (ite_eq_left (hstore 1 83 4 (by decide) (by decide))).trans ?_
      refine (ite_eq_left (hstore 2 87 4 (by decide) (by decide))).trans ?_
      refine (ite_eq_left (hstore 3 91 4 (by decide) (by decide))).trans ?_
      refine (ite_eq_left (show LoadOk (writes 4 (by decide)) sp 8 ∧
        (memLoad (writes 4 (by decide)) sp 64).toNat < 2^32 from
        ⟨hreturnRead, hreturn ▸ hretLow⟩)).trans ?_
      rfl
    case tag => exact congrArg (fun v => some (⟨64, v⟩ : Value)) hreturn
    case stack => rfl
    case result => rfl
    case regs =>
      intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    case store => rfl
  obtain ⟨out, heval, htag, hstack, hresult, hregs, hmem⟩ := evaluate
  refine ⟨out, Program.Exec.done ?_, htag, hstack, hresult, hregs, hmem ▸ frame 4 (by decide), ?_⟩
  · simp only [Program.step, heval, Transfer.next]
  · rw [hmem]
    exact packedWordsAt hw.readable (packWords a) 4 (by decide)

end K256.Proofs.Sec1.Serialize
