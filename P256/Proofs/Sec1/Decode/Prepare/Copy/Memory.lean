import P256.Proofs.Sec1.Decode.Prepare.Memory
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare.Copy

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev Window (s : RamState) (f : Nat → UInt8) (size : Nat := 280) : Prop :=
  Bytes s.external (stackPtr s) size f

def update {α : Type} (f v : Nat → α) (off count : Nat) (i : Nat) : α :=
  if off ≤ i ∧ i < off + count then v (i-off) else f i

theorem update_map {α β : Type} (g : α → β) (f v : Nat → α) (off count : Nat) :
    update (fun i ↦ g (f i)) (fun i ↦ g (v i)) off count =
      fun i ↦ g (update f v off count i) := by
  funext i
  simp only [update]
  split <;> rfl

theorem window_registers {size : Nat} {s t : RamState} {f : Nat → UInt8} {cs : List Component}
    (h : Window s f size) (ag : AgreesExcept cs s t)
    (rsp : .reg 4 ∉ cs) (noMemory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) : Window t f size := by
  have sp : stackPtr t = stackPtr s := ag.read (n := 64) rsp
  change Bytes t.external (stackPtr t) size f
  rw [sp, ag.external noMemory]
  exact h

theorem window_store_bounded {size : Nat} {s t l : RamState} {f v : Nat → UInt8} {off src n : Nat}
    (small : size < 2^64) (h : Window s f size) (input : Window l v size)
    (bound : off+n/8 ≤ size) (srcBound : src+n/8 ≤ size)
    (ag : AgreesExcept [.mem (stackPtr s + BitVec.ofNat 64 off) (n/8), .rip] s t)
    (value : memLoad t.external (stackPtr s + BitVec.ofNat 64 off) n =
      memLoad l.external (stackPtr l + BitVec.ofNat 64 src) n) :
    Window t (update f (fun i ↦ v (src+i)) off (n/8)) size := by
  have sp : stackPtr t = stackPtr s := ag.read (n := 64) (r := 4) (by simp)
  intro i hi
  change t.external[stackPtr t + BitVec.ofNat 64 i]? = _
  rw [sp]
  unfold update
  by_cases inside : off ≤ i ∧ i < off+n/8
  · rw [ite_eq_left inside]
    have allocated : ∀ j < n/8,
        (t.external[stackPtr s + BitVec.ofNat 64 off + BitVec.ofNat 64 j]?).isSome := by
      intro j hj
      apply ag.grow
      have b := h (off+j) (by omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, b]
      rfl
    have b := Bytes.of_memLoad allocated (i-off) (by omega)
    rw [value] at b
    have inp := (input.sub src (n/8) srcBound) (i-off) (by omega)
    have load := Bytes.of_memLoad (m := l.external) (a := stackPtr l + BitVec.ofNat 64 src)
      (n := n) (fun j hj ↦ by rw [input.sub src (n/8) srcBound j hj]; rfl) (i-off) (by omega)
    have eq := Option.some.inj (load.symm.trans inp)
    rw [eq] at b
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' inside.1] using b
  · rw [ite_eq_right inside]
    rw [ag.byte ?_]
    · exact h i hi
    · intro c hc cover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j,hj,eq⟩ := cover
        have he : BitVec.ofNat 64 (off+j) = BitVec.ofNat 64 i := by
          apply (BitVec.add_right_inj (stackPtr s)).mp
          simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using eq.symm
        have he' := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off+j < 2^64),
          Nat.mod_eq_of_lt (by omega : i < 2^64)] at he'
        omega
      · exact cover.elim

theorem window_store {s t l : RamState} {f v : Nat → UInt8} {off src n : Nat}
    (h : Window s f) (input : Window l v)
    (bound : off+n/8 ≤ 280) (srcBound : src+n/8 ≤ 280)
    (ag : AgreesExcept [.mem (stackPtr s + BitVec.ofNat 64 off) (n/8), .rip] s t)
    (value : memLoad t.external (stackPtr s + BitVec.ofNat 64 off) n =
      memLoad l.external (stackPtr l + BitVec.ofNat 64 src) n) :
    Window t (update f (fun i ↦ v (src+i)) off (n/8)) :=
  window_store_bounded (by decide) h input bound srcBound ag value

theorem frame_store [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {off len : Nat} (pre : DecodePre s boundary bytes)
    (state : Frame s t) (ready : ReadyToStep u)
    (ag : AgreesExcept [.mem (stackPtr t + BitVec.ofNat 64 off) len, .rip] t u)
    (bound : off+len ≤ 280) : Frame s u := by
  apply state.after_effect pre ready ag ?_ (by simp)
  intro c hc a covered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨ScalarFrame.Work.region s 3680 32, by simp, stack_work pre state bound covered⟩
  · exact covered.elim

end P256.Proofs.Sec1.Decode.Prepare.Copy
