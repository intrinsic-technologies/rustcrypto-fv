import P256.Proofs.SignatureFromDer.Fixed.Decode.Input
import P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.FirstInput
import P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.SecondInput
import P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.FirstResult
import P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.SecondResult

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (CalleePre)
open P256.Proofs.Program.ScalarFrame

namespace P256.Proofs.SignatureFromDer.Fixed.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_argument [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Stage s t boundary)
    (second : Bool) (rip : t.RIP = if second then 0x109b47 else 0x109ada)
    (source : (if second then t.regValue .r14 else t.regValue .rsi) = s.regValue .rsi)
    (bytes : (registerRegion s .rsi 64).HasBytes s.external input) :
    ∃ u, Stage s u boundary ∧ u.RIP = (if second then 0x109b6b else 0x109afd) ∧
      (MemoryRegion.mk (stackPtr u + 72).toNat 32).HasBytes u.external
        (input.extract (if second then 32 else 0) (if second then 64 else 32)) ∧
      AgreesExcept (Copy32.components (stackPtr t + 72)) t u := by
  let off : Nat := if second then 32 else 0
  let src : RamState → BitVec 64 := fun v =>
    (if second then v.regValue .r14 else v.regValue .rsi) + BitVec.ofNat 64 off
  let dst : RamState → BitVec 64 := fun v => stackPtr v + 72
  let ip : BitVec 64 := if second then 0x109b47 else 0x109ada
  let next : BitVec 64 := if second then 0x109b6b else 0x109afd
  let code := if second then codeRange ip Copy.SecondInput.bytes else codeRange ip Copy.FirstInput.bytes
  have srcEq : src t = s.regValue .rsi + BitVec.ofNat 64 off := by dsimp only [src]; rw [source]
  have readable : MemReadable t (src t) 32 := by
    rw [srcEq]
    exact input_readable pre state.toFrame (by cases second <;> decide)
  have apart : RangeApart (dst t) 32 (src t) 32 := by
    rw [srcEq]
    exact input_stack_apart pre state.toFrame (by cases second <;> decide)
  have cp := copy_stack_pre pre state.toFrame (offset := 72) (by decide) rfl rip readable apart
  have block : AdvanceTriple boundary (Copy32.Pre ip src dst) code
      (Effect.post (Copy32.effect next src dst)) := by
    cases second
    · exact Program.ScalarFrame.Copy32Input.run boundary pre.outerBoundary 0x9ada (by decide)
    · exact Copy.SecondInput.run boundary pre.outerBoundary
  have hc : CodeIn code t := by
    cases second
    · exact Copy.FirstInput.code state.loaded
    · exact Copy.SecondInput.code state.loaded
  obtain ⟨u, ust, effect⟩ := copy_execute pre state block hc cp (offset := 72) (by decide) rfl
  have agree : AgreesExcept (Copy32.components (stackPtr t + 72)) t u := Copy32.frame effect
  have sp : stackPtr u = stackPtr t := agree.read (n := 64) (r := 4) (by simp [Copy32.components])
  have output : MemReadable u (dst t) 32 := by
    have h := stack_readable pre ust.toFrame (offset := 72) (len := 32) (by decide)
    simpa [dst, sp] using h
  have copied := Copy32.copy_bytes effect readable output
  rw [srcEq] at copied
  have extracted := copied_extract (offset := off) (by cases second <;> decide)
    (state.toFrame.input_bytes pre bytes) copied
  refine ⟨u, ust, effect.rip, ?_, agree⟩
  cases second <;> simpa [off, dst, sp] using extracted

theorem save_scalar [Bindings] {s t : RamState} {boundary : ReturnBoundary} {value : Nat}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Stage s t boundary)
    (second : Bool) (rip : t.RIP = if second then 0x109b8a else 0x109b1c)
    (scalar : Nat256At t (stackPtr t + 16) value) :
    ∃ u, Stage s u boundary ∧ u.RIP = (if second then 0x109bbe else 0x109b47) ∧
      Nat256At u (stackPtr u + (if second then 136 else 104)) value ∧
      AgreesExcept (Copy.Result.components (stackPtr t + (if second then 136 else 104))) t u := by
  let off : Nat := if second then 136 else 104
  let src : RamState → BitVec 64 := fun v => stackPtr v + 16
  let dst : RamState → BitVec 64 := fun v => stackPtr v + BitVec.ofNat 64 off
  let ip : BitVec 64 := if second then 0x109b8a else 0x109b1c
  let next : BitVec 64 := if second then 0x109bbe else 0x109b47
  let code := if second then codeRange ip Copy.SecondResult.bytes else codeRange ip Copy.FirstResult.bytes
  have readable : MemReadable t (src t) 32 := stack_readable pre state.toFrame (by decide)
  have apart : RangeApart (dst t) 32 (src t) 32 :=
    RangeApart.offsets (stackPtr t) (by cases second <;> decide) (by decide)
      (.inr (by cases second <;> decide))
  have cp := copy_stack_pre pre state.toFrame (offset := off)
    (by cases second <;> decide) rfl rip readable apart
  have block : AdvanceTriple boundary (Copy32.Pre ip src dst) code
      (Effect.post (Copy.Result.effect next src dst)) := by
    cases second
    · exact Copy.FirstResult.run boundary pre.outerBoundary
    · exact Copy.SecondResult.run boundary pre.outerBoundary
  have hc : CodeIn code t := by
    cases second
    · exact Copy.FirstResult.code state.loaded
    · exact Copy.SecondResult.code state.loaded
  obtain ⟨fuel, u, run, ready, _, effect⟩ := block t
    (Program.readyToStep state.machine state.bindingsSupported) hc cp
  have agree := Copy.Result.frame effect
  have dst' : dst t = stackPtr s - BitVec.ofNat 64 (184-off) :=
    Program.ScalarFrame.scalar_stack_address (frameOffset := 184) state.rsp (by decide)
      (by cases second <;> decide)
  have writes : WritesWithin (Copy.Result.components (dst t))
      #v[registerRegion s .rdi 72, workRegion s] := by
    intro c hmem a ha
    simp only [Copy.Result.components, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    rw [dst'] at ha
    exact ⟨workRegion s, by simp, Program.ScalarFrame.Work.contains pre
      (by cases second <;> decide) (by cases second <;> decide) ha⟩
  have ust := state.after pre run ready agree writes
    ((agree.read (n := 64) (r := 4) (by simp [Copy.Result.components])).trans state.rsp)
    (by simp [Copy.Result.components])
  have sp : stackPtr u = stackPtr t := agree.read (n := 64) (r := 4) (by simp [Copy.Result.components])
  have output : MemReadable u (dst t) 32 := by
    have h := stack_readable pre ust.toFrame (offset := off) (len := 32) (by cases second <;> decide)
    simpa [dst, sp] using h
  have payload := Copy.Result.copy_nat256 effect output scalar
  refine ⟨u, ust, effect.rip, ?_, ?_⟩
  · cases second <;> simpa [dst, off, sp] using payload
  · cases second <;> exact agree

end P256.Proofs.SignatureFromDer.Fixed.Decode
