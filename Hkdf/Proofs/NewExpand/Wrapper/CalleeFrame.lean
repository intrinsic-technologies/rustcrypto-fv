import Hkdf.Proofs.NewExpand.Wrapper.Frame
import Hkdf.Proofs.Common.CallFrame.Stack

namespace Hkdf.Proofs.NewExpand.Wrapper

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem stackContains {s : RamState} {a : Nat} (reserve : Nat) :
    (Stack.region s reserve).Contains a ↔
      (stackPtr s).toNat - reserve ≤ a ∧ a < (stackPtr s).toNat + 8 := by
  unfold MemoryRegion.Contains
  rw [stack_region_end]
  rfl

theorem savedFrame_of_frame {initial s t : RamState} {n : Nat}
    {regions : Vector MemoryRegion n} (saved : SavedFrame initial s)
    (rbp : t.regValue .rbp = s.regValue .rbp)
    (stack : Stack.Valid initial hkdfSha256NewExpandMinStackBytes)
    (frame : MemoryWriteFrame s t regions)
    (apart : ∀ a, (stackPtr initial).toNat - 40 ≤ a → a < (stackPtr initial).toNat + 8 →
      ∀ r ∈ regions, ¬ r.Contains a) : SavedFrame initial t := by
  have low : 2632 ≤ (stackPtr initial).toNat := (stack_bounds stack).1
  have high := (stack_bounds stack).2
  have start : (stackPtr initial - 40).toNat = (stackPtr initial).toNat - 40 :=
    stack_sub_toNat stack (show 40 ≤ 2632 by decide)
  have same : (Component.mem (stackPtr initial - 40) 48).Agrees s t := by
    apply frame_agrees_of_disjoint frame
    · rw [start]
      omega
    · intro region member address contains
      change (stackPtr initial - 40).toNat ≤ address ∧
        address < (stackPtr initial - 40).toNat + 48 at contains
      rw [start] at contains
      exact apart address contains.1 (by omega) region member
  let offsets : List Nat := [40,32,24,16,8,0]
  have bound (offset : Nat) (member : offset ∈ offsets) : offset ≤ 40 := by
    simp only [offsets, List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have slots := agrees_memLoad_slots same offsets (40 - ·)
    (fun offset member ↦ by have := bound offset member; omega)
  have slot (offset : Nat) (member : offset ∈ offsets) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    have split : (40 : BitVec 64) =
        BitVec.ofNat 64 offset + BitVec.ofNat 64 (40 - offset) := by
      rw [← BitVec.ofNat_add, Nat.add_sub_of_le (bound offset member)]
      rfl
    have word := slots offset member
    rw [split, ← BitVec.sub_sub, BitVec.sub_add_cancel] at word
    exact word
  exact ⟨rbp.trans saved.rbp, (slot 40 (by decide)).trans saved.rbx,
    (slot 32 (by decide)).trans saved.r12, (slot 24 (by decide)).trans saved.r13,
    (slot 16 (by decide)).trans saved.r14, (slot 8 (by decide)).trans saved.r15,
    by rw [← saved.ret]; simpa using slot 0 (by decide)⟩

private theorem innerStack {initial s : RamState} {a : Nat}
    (stack : Stack.Valid initial hkdfSha256NewExpandMinStackBytes)
    (rsp : stackPtr s = stackPtr initial - 368) :
    (Stack.region s 2264).Contains a ↔
      (stackPtr initial).toNat - 2632 ≤ a ∧ a < (stackPtr initial).toNat - 360 := by
  have low : 2632 ≤ (stackPtr initial).toNat := stack.2.2.1
  rw [stackContains, rsp, show (stackPtr initial - 368).toNat = (stackPtr initial).toNat - 368 from
    stack_sub_toNat stack (show 368 ≤ 2632 by decide)]
  omega

theorem extractReturn [Bindings] {initial s t : RamState}
    {salt : Option ByteArray} {ikm : ByteArray}
    (stack : Stack.Valid initial hkdfSha256NewExpandMinStackBytes)
    (entry : ExtractEntry initial s salt ikm)
    (result : CalleeResult s t (returnBoundary initial) 176 2264)
    (hmac : HmacAt t (s.regValue .rdi + 32) (RFC5869.extract .sha256 salt ikm) ByteArray.empty) :
    ExtractReturn initial t (RFC5869.extract .sha256 salt ikm) := by
  have low : 2632 ≤ (stackPtr initial).toNat := stack.2.2.1
  have bounds (r) (hr : r ∈ #v[registerRegion s .rdi 176, Stack.region s 2264])
      (a) (ha : r.Contains a) :
      (stackPtr initial).toNat - 2632 ≤ a ∧ a < (stackPtr initial).toNat - 184 := by
    rcases (show r = registerRegion s .rdi 176 ∨ r = Stack.region s 2264 by simpa using hr)
      with rfl | rfl
    · change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 176 at ha
      rw [entry.dest, show (stackPtr initial - 360).toNat = (stackPtr initial).toNat - 360 from
        stack_sub_toNat stack (show 360 ≤ 2632 by decide)] at ha
      exact (show ∀ x y : Nat, 2632 ≤ x → x - 360 ≤ y ∧ y < x - 360 + 176 →
          x - 2632 ≤ y ∧ y < x - 184 by omega) _ _ low ha
    · have := (innerStack stack entry.rsp).mp ha
      omega
  refine ⟨entry.run.of_callee result ?_, savedFrame_of_frame entry.saved
      (result.abi.1 .rbp (by simp)) stack result.frame ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr a ha
    have := bounds r hr a ha
    exact ⟨_, Vector.mem_singleton_self _, (stackContains 2632).mpr ⟨this.1, by omega⟩⟩
  · intro a hlo hhi r hr ha
    have := bounds r hr a ha
    omega
  · exact ⟨(result.abi.1 .r14 (by simp)).trans entry.args.info,
      (result.abi.1 .rbx (by simp)).trans entry.args.infoLength,
      (result.abi.1 .r15 (by simp)).trans entry.args.output,
      (result.abi.1 .r12 (by simp)).trans entry.args.length⟩
  · rw [show stackPtr t = _ from result.rsp, entry.boundary]
  · rw [result.rip, entry.boundary]
  · have addr : s.regValue .rdi + 32 = stackPtr initial - 328 := by
      rw [entry.dest, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.sub_eq_add_neg]
      rfl
    rw [addr] at hmac
    exact hmac

theorem expandFrame [Bindings] {initial s t : RamState} {prk info ikm : ByteArray}
    {salt : Option ByteArray} {length : Nat}
    (call : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    (entry : ExpandEntry initial s prk info length)
    (result : ExpandResult s t (returnBoundary initial) prk info length) :
    SavedFrame initial t ∧ MemoryWriteFrame initial t
      #v[deriveKeyOutputRegion initial (writtenLength length),
        Stack.region initial hkdfSha256NewExpandMinStackBytes] := by
  have low : 2632 ≤ (stackPtr initial).toNat := call.stack.2.2.1
  have output (k : Nat) : registerRegion s .rcx k = deriveKeyOutputRegion initial k := by
    unfold registerRegion deriveKeyOutputRegion
    rw [entry.output]
  have subStack (a : Nat) (h : (Stack.region s 2264).Contains a) :
      (stackPtr initial).toNat - 2632 ≤ a ∧ a < (stackPtr initial).toNat - 360 :=
    (innerStack call.stack entry.rsp).mp h
  constructor
  · apply savedFrame_of_frame entry.saved (result.abi.1 .rbp (by simp)) call.stack result.frame
    intro a hlo hhi r hr ha
    rcases (show r = registerRegion s .rcx (writtenLength length) ∨ r = Stack.region s 2264 by
      simpa using hr) with rfl | rfl
    · rw [output] at ha
      have contains : (Stack.region initial hkdfSha256NewExpandMinStackBytes).Contains a :=
        (stackContains 2632).mpr ⟨by omega, hhi⟩
      by_cases h : length ≤ 8160
      · simp only [writtenLength, h, ↓reduceIte] at ha
        have pos : 0 < length := by
          change _ ≤ a ∧ a < _ + length at ha
          omega
        exact (call.separationIfWritten pos h).1 ⟨0, by decide⟩ ⟨1, by decide⟩
          (by decide) _ ha contains
      · simp only [writtenLength, h, ↓reduceIte, deriveKeyOutputRegion, MemoryRegion.Contains,
          Nat.add_zero] at ha
        omega
    · have := subStack a ha
      omega
  · apply memoryWriteFrame_trans (frame_mono entry.run.frame ?_) (frame_mono result.frame ?_)
    · intro r hr a ha
      have eq := Vector.mem_singleton.mp hr
      subst r
      exact ⟨_, by simp, ha⟩
    · intro r hr a ha
      rcases (show r = registerRegion s .rcx (writtenLength length) ∨ r = Stack.region s 2264 by
        simpa using hr) with rfl | rfl
      · rw [output] at ha
        exact ⟨_, by simp, ha⟩
      · have h := subStack a ha
        exact ⟨Stack.region initial hkdfSha256NewExpandMinStackBytes, by simp,
          (stackContains 2632).mpr ⟨h.1, by omega⟩⟩

end Hkdf.Proofs.NewExpand.Wrapper
