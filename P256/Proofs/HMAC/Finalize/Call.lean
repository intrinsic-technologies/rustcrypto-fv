import P256.Proofs.HMAC.Finalize.Memory
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

theorem call_address [Bindings] {s t : RamState} (state : ScalarFrame.FrameState s t 0 672 328) :
    pushAddr t = stackPtr s - 336 := by
  rw [pushAddr, state.rsp, BitVec.sub_sub]
  rfl

theorem after_call [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : HashCalleePre s boundary 0x100f10 168 672) (state : ScalarFrame.FrameState s t 0 672 328)
    (ready : ReadyToStep u) (effect : (callEffect target ret t).Holds t u) :
    ScalarFrame.FrameState s u 0 672 336 := by
  exact state.after_call (stackPre pre) (by decide) (by decide) ready effect

theorem call_stack_byte [Bindings] {s t u : RamState} {target : RamState → BitVec 64}
    {ret : BitVec 64} (state : ScalarFrame.FrameState s t 0 672 328)
    (effect : (callEffect target ret t).Holds t u)
    {offset len : Nat} (ho : offset ≤ 328) (hl : len ≤ offset + 8) {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc hv
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hv.elim
  · obtain ⟨j, hj, he⟩ := hv
    rw [call_address state] at he
    have ha : stackPtr s - BitVec.ofNat 64 offset =
        (stackPtr s - 336) + BitVec.ofNat 64 (336-offset) := by
      rw [← BitVec.ofNat_sub_ofNat_of_le 336 offset (by omega) (by omega)]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [← BitVec.add_assoc (-(336 : BitVec 64)),
        show -(336 : BitVec 64) + 336#64 = 0#64 by decide +kernel, BitVec.zero_add]
    apply RangeApart.offsets (stackPtr s - 336) (a := 0) (b := 336-offset)
      (len := 8) (count := len) (by decide) (by omega) (.inl (by omega)) j hj i hi
    rw [show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero, ← ha]
    exact he.symm
  · exact hv.elim

structure CompressionSite where
  offset : Nat
  disp : BitVec 32
  bound : offset + 5 < 118431
  bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp
  target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5 (disp.signExtend 64) = 0x115990

def outerPadSite : CompressionSite :=
  ⟨0xf96, 0x149f5, by decide, by decide +kernel, by decide +kernel⟩

def innerTailSite : CompressionSite :=
  ⟨0x110c, 0x1487f, by decide, by decide +kernel, by decide +kernel⟩

def outerTailSite : CompressionSite :=
  ⟨0x13aa, 0x145e1, by decide, by decide +kernel, by decide +kernel⟩

theorem compression_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : HashCalleePre s boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState s t 0 672 328) (site : CompressionSite)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧
      (callEffect (fun _ => 0x115990)
        (Extracted.textAddress + BitVec.ofNat 64 site.offset + 5#64) t).Holds t u ∧
      ScalarFrame.FrameState s u 0 672 336 := by
  have writable : MemWritable t (pushAddr t) 8 := by
    rw [call_address state]
    exact P256.Proofs.Program.writable_of_grow
      (P256.Proofs.Program.stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (offset := 336) (by decide) (by decide)) state.allocated
  have apart : RangeApart (pushAddr t) 8
      (Extracted.textAddress + BitVec.ofNat 64 site.offset) 5 := by
    rw [call_address state]
    exact P256.Proofs.HMAC.Key.stack_code_apart (pre.toCalleePre)
      (offset := 336) (codeOffset := site.offset) (by decide) (by decide) (Nat.le_of_lt site.bound)
  obtain ⟨u, run, ready, effect⟩ :=
    (call_rel32_effect_step (Extracted.textAddress + BitVec.ofNat 64 site.offset) site.disp
      (by rw [site.target]; decide)).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) site.offset (encodeCallRel32 site.disp)
        (by simpa [encodeCallRel32, immBytes_length] using Nat.le_of_lt site.bound) site.bytes)
      ⟨rip, writable, apart⟩
      (by
        change branchTarget (Extracted.textAddress + BitVec.ofNat 64 site.offset) 5
          (site.disp.signExtend 64) ≠ boundary.rip
        rw [site.target]
        exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x15990 (by decide)))
  have converted : (callEffect (fun _ => 0x115990)
      (Extracted.textAddress + BitVec.ofNat 64 site.offset + 5#64) t).Holds t u := by
    simpa only [site.target] using effect
  exact ⟨u, run, ready, converted, after_call pre state ready converted⟩

end P256.Proofs.HMAC.Finalize
