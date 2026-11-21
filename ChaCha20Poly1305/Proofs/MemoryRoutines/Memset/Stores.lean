import ChaCha20Poly1305.Proofs.MemoryRoutines.Memset.Arithmetic
import ChaCha20Poly1305.Proofs.MemoryRoutines.Stos
import ChaCha20Poly1305.Proofs.MemoryRoutines.Ranges
import ChaCha20Poly1305.Proofs.MemoryRoutines.Code

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Memset

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Common ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

def storeChanges (s : RamState) (length : Nat) : List Component :=
  [.reg 1, .reg 7, .mem (rdi.read s) length, .rip]

structure FillState [Bindings] (s t : RamState) (length offset : Nat) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  pointer : rdi.read t = rdi.read s + BitVec.ofNat 64 offset
  fill : ∀ i < offset, t.external[rdi.read s + BitVec.ofNat 64 i]? =
    some (UInt8.ofBitVec ((rax.read s).setWidth 8))
  agrees : AgreesExcept (storeChanges s length) s t

theorem FillState.initial [Bindings] (s : RamState) (length : Nat)
    (h : ReadyToStep s) (hc : CodeIn Extracted.programImage s) : FillState s s length 0 :=
  ⟨h, hc, by simp, by intro i hi; omega, AgreesExcept.refl _ _⟩

theorem FillState.move [Bindings] {s t u : RamState} {length offset : Nat}
    (h : FillState s t length offset) (hr : ReadyToStep u) (p : BitVec 64) (src : BitVec 5)
    (he : (movR64R64Effect p 1 src t).Holds t u) : FillState s u length offset := by
  refine ⟨hr, he.agrees.codeIn (by simp [Component.Covers]) h.code,
    (he.agrees.read (by simp)).trans h.pointer, ?_, ?_⟩
  · intro i hi
    rw [he.agrees.byte (by simp [Component.Covers])]
    exact h.fill i hi
  · apply (h.agrees.trans he.agrees).mono
    simp [storeChanges]

theorem FillState.store [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s u : RamState} {length offset : Nat} (h : FillState s u length offset)
    (hw : WritableRange s (rdi.read s) length)
    (hpattern : rax.read s = broadcast ((rax.read s).setWidth 8))
    (hdf : DirectionFlagClear s.RFLAGS) (kind : Stos.Kind) (p : BitVec 64)
    (hip : u.RIP = p) (hc : CodeIn (codeRange p kind.code) u)
    (htext : ∀ i < kind.code.length, InProgram (p + BitVec.ofNat 64 i))
    (hbound : offset + kind.bytes * (rcx.read u).toNat ≤ length)
    (halign : rcx.read u ≠ 0 → (rdi.read u).toNat % kind.bytes = 0)
    (boundary : ReturnBoundary) (hstart : p ≠ boundary.rip)
    (hend : p + BitVec.ofNat 64 kind.code.length ≠ boundary.rip) :
    ∃ fuel t, Advances boundary fuel u t ∧
      FillState s t length (offset + kind.bytes * (rcx.read u).toNat) ∧
      t.RIP = p + BitVec.ofNat 64 kind.code.length := by
  have hwu : WritableRange u (rdi.read u) (kind.bytes * (rcx.read u).toNat) := by
    rw [h.pointer]
    exact (hw.slice offset _ hbound).of_agrees h.agrees
  have hp : Stos.Pre kind p u :=
    ⟨hip, (h.agrees.directionFlagClear (by simp [storeChanges]) ⟨hdf⟩).df, hwu.readable.low,
      halign, hwu.readable.mem, hwu.tables,
      fun i hi j hj he ↦ hwu.code i hi (he ▸ htext j hj)⟩
  have hd := Stos.rep_stos_steps hstride kind p u h.ready hc hp
  have ha := Stos.rep_stos_advances hstride kind boundary p u h.ready hc hp hstart hend
  let t := nextStates (max (rcx.read u).toNat 1) u
  have hag := hd.agrees_of_ready h.ready
  have hwidth : AgreesExcept (storeChanges s length) u t := by
    apply hag.widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> simp_all [Component.isMem, storeChanges]
    · intro x c hc hcover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> try exact hcover.elim
      obtain ⟨i, hi, he⟩ := hcover
      refine ⟨.mem (rdi.read s) length, by simp [storeChanges], offset + i, by omega, ?_⟩
      rw [he, h.pointer, add_ofNat_add_ofNat]
  have hrax : rax.read u = rax.read s := h.agrees.read (by simp [storeChanges])
  have hstored (i : Nat) :
      storedByte ((Operand.reg 0 : Operand (8 * kind.bytes)).read u) (i % kind.bytes) =
        UInt8.ofBitVec ((rax.read s).setWidth 8) := by
    cases kind with
    | byte =>
      change storedByte ((rax.read u).setWidth 8) (i % 1) = _
      rw [hrax, Nat.mod_one, byte_storedByte]
    | qword =>
      change storedByte (rax.read u) (i % 8) = _
      rw [hrax]
      conv => lhs; rw [hpattern]
      exact broadcast_storedByte _ _ (Nat.mod_lt _ (by decide))
  refine ⟨_, t, ha, ⟨hd.ready, ?_, ?_, ?_, h.agrees.trans hwidth |>.mono (by simp)⟩,
    hd.rip.trans (congrArg (· + BitVec.ofNat 64 kind.code.length) hip)⟩
  · apply CodeIn.of_agreesExcept hwidth _ h.code
    intro x hx c hc hcover
    simp only [storeChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> try exact hcover.elim
    obtain ⟨i, hi, he⟩ := hcover
    exact hw.code i hi (he ▸ Machine.inProgram_of_mem hx)
  · rw [hd.rdiAfter, h.pointer, add_ofNat_add_ofNat]
  · intro i hi
    by_cases hsmall : i < offset
    · refine (hag.byte ?_).trans (h.fill i hsmall)
      intro c hc hcover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> try exact hcover.elim
      obtain ⟨j, hj, he⟩ := hcover
      rw [h.pointer, add_ofNat_add_ofNat] at he
      have hn := congrArg BitVec.toNat he
      have hl := hw.readable.low
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
      omega
    · have htail := hd.fill (i - offset) (by omega)
      rw [hstored, h.pointer, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega)] at htail
      exact htail

end ChaCha20Poly1305.Proofs.MemoryRoutines.Memset
