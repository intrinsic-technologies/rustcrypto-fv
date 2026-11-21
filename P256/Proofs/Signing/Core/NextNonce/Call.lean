import P256.Proofs.Signing.Core.NextNonce.Memory
import P256.Proofs.Program.ScalarFrame.CallStep
import P256.Proofs.Program.CalleeStackRegion
import P256.Proofs.Nonce.Fill.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.NextNonce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

def layout : StackCallLayout 4584 32 72 2096 :=
  ⟨2288, 2240, 120, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem push_address [Bindings] {s t : RamState} (frame : Frame s t) :
    pushAddr t = stackPtr s - 2288 := by
  simp only [pushAddr, frame.rsp, frameBase, BitVec.sub_sub]
  rfl

theorem call_copy [Bindings] {s t u : RamState} (frame : Frame s t)
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (effect : (callEffect target ret t).Holds t u)
    {offset len : Nat} (bound : offset + len ≤ 2280) :
    ∀ i < len, u.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  rw [base_add s (by omega)]
  intro i hi
  exact ScalarFrame.call_byte (frameOffset := 2280) (by decide) frame.rsp effect
    (offset := 2280-offset) (len := len) (by omega) (by omega) hi

theorem call_pre [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    (pre : SignPre s boundary) (input : Loop s t state)
    (count : t.regValue .rdx = 32) (source : t.regValue .rsi = frameBase s + 40)
    (destination : t.regValue .rdi = frameBase s + 2160)
    (ready : ReadyToStep u)
    (effect : (callEffect (fun _ => 0x107330) 0x10cad9 t).Holds t u) :
    Nonce.Fill.Pre u boundary (frameBase s + 272) state := by
  have si : u.regValue .rsi = frameBase s + 40 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have di : u.regValue .rdi = frameBase s + 2160 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have sp : stackPtr u = stackPtr s - 2288 := effect.writes.1.trans (push_address input.frame)
  have sourceSub : u.regValue .rsi = stackPtr s - 2240 :=
    si.trans (base_add s (offset := 40) (by decide))
  have outputSub : u.regValue .rdi = stackPtr s - 120 :=
    di.trans (base_add s (offset := 2160) (by decide))
  have grow (a : BitVec 64) (ha : (s.external[a]?).isSome) : (u.external[a]?).isSome :=
    effect.agrees.grow a (input.frame.allocated a ha)
  have memory : MemoryWriteFrame t u #v[Stack.region s 4584] := by
    apply effect.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨Stack.region s 4584, by simp, ?_⟩
      rw [push_address input.frame] at ha
      exact ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) ha
    · exact ha.elim
  have loaded : ProgramLoaded u := by
    intro a b hb
    rw [memory a]
    · exact input.frame.loaded a b hb
    · intro region hr hin
      have eq : region = Stack.region s 4584 := by simpa using hr
      subst region
      exact pre.avoids _ (by simp) a hin (.inl ⟨b,hb⟩)
  have ret : (returnBoundary u).rip = 0x10cad9 := (callEffect_stack effect).1
  have cp := CalleePre.of_stack pre.toCalleePre layout
    (bindingsSupported_of_ready_agrees input.frame.bindingsSupported ready effect.agrees)
    (supportedMachine_of_ready_agrees input.frame.machine ready effect.agrees)
    (effect.agrees.directionFlagClear (by simp) input.frame.directionFlag)
    loaded grow effect.rip sp sourceSub outputSub
    (ret ▸ inProgram_of_textOffset 0xcad9 (by decide))
  have sub := layout.regions_within pre.stack sp sourceSub outputSub
  have bounds := stack_bounds pre.stack
  have orderNat : (frameBase s + 272).toNat = (stackPtr s).toNat - 2280 + 272 :=
    base_nat pre (offset := 272) (by decide)
  have siNat : (u.regValue .rsi).toNat = (stackPtr s).toNat - 2280 + 40 := by
    rw [si]; exact base_nat pre (by decide)
  have diNat : (u.regValue .rdi).toNat = (stackPtr s).toNat - 2280 + 2160 := by
    rw [di]; exact base_nat pre (by decide)
  have spNat : (stackPtr u).toNat = (stackPtr s).toNat - 2288 := by
    rw [sp]; exact stack_sub_toNat pre.stack (by decide)
  have order : Nat256At u (frameBase s + 272) Operations.domain.n :=
    ⟨input.generator.2.1.1, fun i hi =>
      (call_copy input.frame effect (offset := 272) (len := 32) (by decide) i hi).trans
        (input.generator.2.1.2 i hi)⟩
  refine ⟨cp, (effect.agrees.read (n := 64) (r := 2) (by simp)).trans count, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact pre.avoids _ (by simp) a (sub _ (by simp) _ ha)
  · change (frameBase s + 272).toNat + 32 < 2^32
    rw [orderNat]
    omega
  · intro a ha
    have inside : (Stack.region s 4584).Contains a.toNat := by
      change (frameBase s + 272).toNat ≤ a.toNat ∧ a.toNat < (frameBase s + 272).toNat + 32 at ha
      rw [orderNat] at ha
      change (stackPtr s).toNat - 4584 ≤ a.toNat ∧ a.toNat < (Stack.region s 4584).start + (Stack.region s 4584).size
      rw [stack_region_end]
      omega
    exact Option.isSome_iff_exists.mp (grow a (Option.isSome_iff_exists.mpr (pre.stack.2.1 a inside)))
  · intro region hr a ha hb
    change (frameBase s + 272).toNat ≤ a ∧ a < (frameBase s + 272).toNat + 32 at ha
    rw [orderNat] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (u.regValue .rsi).toNat ≤ a ∧ a < (u.regValue .rsi).toNat + 32 at hb
      rw [siNat] at hb
      omega
    · change (u.regValue .rdi).toNat ≤ a ∧ a < (u.regValue .rdi).toNat + 72 at hb
      rw [diNat] at hb
      omega
    · have high := hb.2
      rw [stack_region_end] at high
      change a < (stackPtr u).toNat + 8 at high
      rw [spNat] at high
      omega
  · rw [di]
    exact input.generator.copy (call_copy input.frame effect (offset := 2160) (len := 72) (by decide)) order

theorem call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    (pre : SignPre s boundary) (input : Loop s t state)
    (rip : t.RIP = 0x10cad4) (count : t.regValue .rdx = 32)
    (source : t.regValue .rsi = frameBase s + 40)
    (destination : t.regValue .rdi = frameBase s + 2160) :
    ∃ u, Advances boundary 1 t u ∧
      (callEffect (fun _ => 0x107330) 0x10cad9 t).Holds t u ∧
      Nonce.Fill.Pre u boundary (frameBase s + 272) state := by
  obtain ⟨u, run, ready, effect⟩ := ScalarFrame.call_step pre.toCalleePre
    (frameOffset := 2280) (by decide) (by decide)
    (readyToStep input.frame.machine input.frame.bindingsSupported) input.frame.loaded
    input.frame.allocated input.frame.rsp 0xcad4 0xffffa857 (by decide) (by decide +kernel)
    (by decide +kernel) (inProgram_of_textOffset 0x7330 (by decide)) rip
  exact ⟨u, run, effect, call_pre pre input count source destination ready effect⟩

end P256.Proofs.Signing.Core.NextNonce
