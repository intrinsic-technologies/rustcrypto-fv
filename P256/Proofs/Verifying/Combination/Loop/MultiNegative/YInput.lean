import P256.Proofs.Verifying.Combination.Loop.MultiNegative.YPre
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.YFrame
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem copy_y [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitData s t tables digits p q u v k point left)
    (i : Fin 8) (rip : t.RIP = 0x10f204)
    (stride : t.regValue .rax = BitVec.ofNat 64 (96*i.val)) :
    ∃ fuel w, Advances boundary fuel t w ∧ DigitData s w tables digits p q u v k point left ∧
      w.RIP = 0x10f22c ∧
      MontgomeryAt w (stackPtr s - 368) (Table.oddTable (if left then p else q) i).y ∧
      (∀ j < 96, w.external[stackPtr s - 240 + BitVec.ofNat 64 j]? =
        t.external[stackPtr s - 240 + BitVec.ofNat 64 j]?) := by
  have hp := y_pre pre state i rip stride
  obtain ⟨fuel,w,run,ready,_,effect⟩ := YCopy.run boundary pre.outerBoundary 0xf204 (by decide) t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf204 YCopy.bytes
      (by decide) (by decide +kernel)) hp
  have dst : yDestination t = stackPtr s - 368 :=
    scalar_stack_address state.rsp (offset := 40) (by decide) (by decide)
  have agrees : AgreesExcept (Copy32.components (stackPtr s - 368)) t w := by
    have h := YCopy.frame effect
    change AgreesExcept (Copy32.components (yDestination t)) t w at h
    rwa [dst] at h
  have writes : ∀ c ∈ Copy32.components (stackPtr s - 368), ∀ a, c.Covers a →
      (Component.mem (stackPtr s-368) 32).Covers a := by
    intro c hc a ha
    simp only [Copy32.components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals first | exact ha | exact ha.elim
  have frame : State s w := state.toFrameState.after_effect pre.toCalleePre (by decide) ready agrees
    (by
      intro c hc a ha
      exact ⟨workRegion s 1432, by simp,
        work_contains pre.toCalleePre (offset := 368) (by decide) (by decide) (writes c hc a ha)⟩)
    (by simp [Copy32.components])
  have kept (off len : Nat) (ho : off ≤ 408) (hl : len ≤ off+8)
      (apart : off+32 ≤ 368 ∨ 368+len ≤ off) (j : Nat) (hj : j<len) :=
    stack_byte pre agrees writes (by decide) (by decide) ho hl apart hj
  have data := data_of_frame pre state frame
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact agrees.read (n := 64) (r := 3) (by simp [Copy32.components])
      · exact agrees.read (n := 64) (r := 5) (by simp [Copy32.components])
      · exact agrees.read (n := 64) (r := 12) (by simp [Copy32.components])
      · exact agrees.read (n := 64) (r := 13) (by simp [Copy32.components])
      · exact agrees.read (n := 64) (r := 15) (by simp [Copy32.components]))
    (by
      intro off len h j hj
      rcases h with ⟨rfl,rfl⟩ | ⟨h,rfl⟩
      · exact kept 336 96 (by decide) (by decide) (by decide) j hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;>
          exact kept _ 8 (by decide) (by decide) (by decide) j hj)
  have sourceValue : MontgomeryAt t (ySource t) (Table.oddTable (if left then p else q) i).y := by
    simp only [ySource, stride, state.tableCursor]
    cases left
    · exact (state.rightTable i).2.1
    · simpa using (state.leftTable i).2.1
  have input : MemReadable t (ySource t) 32 := by
    have h := hp.readable
    refine ⟨?_, ?_⟩
    · have h0 := (h 0 (by simp)).low
      change (ySource t+0#64).toNat+8 ≤ 2^32 at h0
      rw [BitVec.add_zero] at h0
      have h3 := (h 24 (by simp)).low
      have h03 : (ySource t+24).toNat = (ySource t).toNat+24 := by
        rw [BitVec.toNat_add]; change ((ySource t).toNat+24)%2^64 = _; omega
      rw [h03] at h3
      omega
    · intro j hj
      have hn : j/8*8 ∈ ([0,8,16,24] : List Nat) := by
        have hq : j/8=0 ∨ j/8=1 ∨ j/8=2 ∨ j/8=3 := by omega
        rcases hq with hq|hq|hq|hq <;> simp [hq]
      have hv := (h (BitVec.ofNat 64 (j/8*8)) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
        rcases hn with h|h|h|h <;> simp [h])).mem (j%8) (by omega)
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, show j/8*8+j%8=j by omega] using hv
  have output : MemReadable w (yDestination t) 32 := by
    rw [dst]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := 368) (by decide) (by decide)) frame.allocated
  have value : MontgomeryAt w (yDestination t) (Table.oddTable (if left then p else q) i).y :=
    sourceValue.of_bytes_eq (YCopy.copy_bytes effect input output)
  rw [dst] at value
  exact ⟨fuel,w,run,data,effect.rip,value,kept 240 96 (by decide) (by decide) (by decide)⟩

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative
