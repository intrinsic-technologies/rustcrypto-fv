import P256.Proofs.PublicPoint.Normalize.Finish.Tag
import P256.Proofs.PublicPoint.Normalize.Finish.Epilogue
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Field.Preserve
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Instructions.CrossPageStore.Range
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step)

theorem tag_output [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    {select : Bool} (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944) (rip : t.RIP = 0x10eae1)
    (output : t.regValue .rbx = s.regValue .rdi)
    (tag : t.external[stackPtr s - 1616]? = some 0)
    (choice : (t.regValue .rbp).setWidth 8 = if select then 1 else 0)
    (hx : MontgomeryAt t (s.regValue .rdi) x)
    (hy : MontgomeryAt t (s.regValue .rdi + 32) y) :
    ∃ u, Advances boundary 6 t u ∧ FrameState s u 65 3352 1944 ∧ u.RIP = 0x10eaf6 ∧
      MontgomeryAt u (s.regValue .rdi) x ∧ MontgomeryAt u (s.regValue .rdi + 32) y ∧
      u.external[s.regValue .rdi + 64]? = some (if select then 0 else 1) := by
  obtain ⟨v, run, ready, ip, value, agrees⟩ := tag_registers pre state tag choice rip
  have frame := state.after_registers ready agrees (by simp [Component.Covers]) (by simp)
  have memory : v.external = t.external := agrees.external (by simp [Component.Covers])
  have out : v.regValue .rbx = s.regValue .rdi :=
    (agrees.read (n := 64) (r := 3) (by simp)).trans output
  have wr := (output_writable pre (by decide) frame.allocated).add 64 (len := 1) (by decide)
  have writable : MemWritable v (s.regValue .rdi + 64) 1 :=
    ⟨wr.low, wr.mem, wr.tables⟩
  obtain ⟨u, run1, ready1, effect⟩ :=
    (mov_m8_r8_legacy_effect_step 0x10eaf3 0 (by decide) (.base 3 (.d8 64))
      (by decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn frame.loaded) 0xeaf3 _
        (by decide) (by decide +kernel))
      ⟨ip, by change MemWritable v (v.regValue .rbx + 64) 1; rw [out]; exact writable,
        by change RangeApart (v.regValue .rbx + 64) 1 0x10eaf3 3
           rw [out]
           exact P256.Proofs.Common.Instructions.RangeApart.add_left
             (output_code pre (offset := 0xeaf3) (len := 3) (by decide)) 64 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xeaf6 (by decide)))
  have g : AgreesExcept [.mem (s.regValue .rdi + 64) 1, .rip] v u := by
    have g := effect.agrees
    simp only [storeEffect_components] at g
    change AgreesExcept [.mem (v.regValue .rbx + 64) 1, .rip] v u at g
    rwa [out] at g
  have finalFrame := frame.after_effect (frameOffset := 1944) pre (by decide) ready1 g
    (by intro c hc a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨registerRegion s .rdi 65, by simp,
            output_contains pre (offset := 64) (len := 1) (by decide) ha⟩
        · exact ha.elim)
    (by simp)
  have pointbytes {off : Nat} (ho : off < 64) :
      u.external[s.regValue .rdi + BitVec.ofNat 64 off]? =
        t.external[s.regValue .rdi + BitVec.ofNat 64 off]? := by
    rw [← memory]
    apply g.byte
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, he⟩ := ha
      have hn := congrArg BitVec.toNat ((BitVec.add_right_inj (s.regValue .rdi)).mp
        (by simpa only [BitVec.add_assoc] using he))
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at hn
      omega
    · exact ha.elim
  have byte : u.external[s.regValue .rdi + 64]? = some (if select then 0 else 1) := by
    have word := effect.writes
    change memLoad u.external (v.regValue .rbx + 64) 8 =
      (Operand.reg 0 : Operand 8).read v at word
    rw [out, value] at word
    have bytes := Bytes.of_memLoad (n := 8) (fun i hi => g.grow _ (writable.mem i hi))
    rw [word] at bytes
    cases select <;> simpa [storedByte] using bytes 0 (by decide)
  refine ⟨u, run.trans run1, finalFrame, effect.rip,
    hx.of_bytes_eq (fun i hi => pointbytes (by omega)), ?_, byte⟩
  apply hy.of_bytes_eq
  intro i hi
  change u.external[(s.regValue .rdi + BitVec.ofNat 64 32) + BitVec.ofNat 64 i]? =
    t.external[(s.regValue .rdi + BitVec.ofNat 64 32) + BitVec.ofNat 64 i]?
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact pointbytes (by omega)

end P256.Proofs.PublicPoint.Normalize.Finish
