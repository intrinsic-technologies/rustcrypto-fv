import K256.Proofs.Sec1.Sqrt.CallSites
import K256.Proofs.Common.Field.SqrtChain
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Branch.Triple

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program

inductive SquareLoop where
  | first44 | middle88 | last44

namespace SquareLoop

def site : SquareLoop → SquareCallSite
  | .first44 => ⟨0x18040, .r14R15⟩
  | .middle88 => ⟨0x184d0, .rbxR14⟩
  | .last44 => ⟨0x18950, .rbxR14⟩

theorem site_mem (loop : SquareLoop) : loop.site ∈ squareCallSites := by
  cases loop <;> decide +kernel

def counter : SquareLoop → BitVec 5
  | .first44 => 3
  | _ => 15

private def decBytes : SquareLoop → UInt8 × UInt8
  | .first44 => (0x48, 0xcb)
  | _ => (0x49, 0xcf)

theorem decrement [Bindings] (loop : SquareLoop) {s : RamState} {boundary : ReturnBoundary}
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programSections.toCodeMap s)
    (hrip : s.RIP = loop.site.pc + (60 : BitVec 64)) (hsp : stackPtr s ≠ boundary.rsp) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      (Operand.reg loop.counter : Operand 64).read t =
        (Operand.reg loop.counter : Operand 64).read s - 1 ∧
      t.RIP = (if (Operand.reg loop.counter : Operand 64).read t = 0
        then loop.site.pc + 65 else loop.site.pc) ∧
      AgreesExcept [.reg loop.counter, .flags, .rip] s t := by
  have hd : CodeIn (codeRange (loop.site.pc + 60)
      [loop.decBytes.1, 0xff, loop.decBytes.2]) s := by
    have h := textSlice hcode (loop.site.offset + 60)
      [loop.decBytes.1, 0xff, loop.decBytes.2] (by cases loop <;> decide +kernel)
      (by cases loop <;> decide +kernel)
    cases loop <;> exact h
  have hj : CodeIn (codeRange ((loop.site.pc + 60) + 3) [0x75, 0xbf]) s := by
    have h := textSlice hcode (loop.site.offset + 63)
      [0x75, 0xbf] (by cases loop <;> decide +kernel) (by cases loop <;> decide +kernel)
    cases loop <;> exact h
  obtain ⟨u, hsu, hru, he⟩ := dec_r64_effect_step (loop.site.pc + 60)
    loop.decBytes.1 loop.decBytes.2 (by cases loop <;> simp [RexWPrefix, decBytes])
    (by cases loop <;> decide) (by cases loop <;> decide) s hready hd hrip
  have hd' : (decR64Effect (loop.site.pc + 60) loop.counter s).Holds s u := by
    cases loop <;> exact he
  have hf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((Operand.reg loop.counter : Operand 64).read s - 1 == 0) := hd'.flags.2.2.2.1
  have hm := hd'.agrees.external (by simp [Component.Covers])
  have htarget : branchTarget ((loop.site.pc + 60) + 3) 2
      ((0xbf : BitVec 8).signExtend 64) = loop.site.pc := by cases loop <;> decide +kernel
  obtain ⟨t, hut, hrt, hb⟩ := jcc_rel8_effect_step ((loop.site.pc + 60) + 3) 5 0xbf
    u hru (hj.of_external_eq hm) ⟨hd'.rip, fun _ => htarget ▸ (by cases loop <;> decide +kernel)⟩
  have hag : AgreesExcept [.rip] u t := hb.agrees
  have hspu : stackPtr u = stackPtr s :=
    hd'.agrees.read (n := 64) (r := 4) (by cases loop <;> simp [counter])
  have hspt : stackPtr t = stackPtr s :=
    (hag.read (n := 64) (r := 4) (by simp)).trans hspu
  have hcnt : (Operand.reg loop.counter : Operand 64).read t =
      (Operand.reg loop.counter : Operand 64).read s - 1 := (hag.read (n := 64) (r := loop.counter) (by simp)).trans hd'.writes
  refine ⟨t, (Advances.of_step hsu (.inr fun e => hsp (hspu.symm.trans e))).trans
    (Advances.of_step hut (.inr fun e => hsp (hspt.symm.trans e))), hrt, hcnt, ?_,
    (hd'.agrees.trans hag).mono (by simp)⟩
  rw [hb.rip]
  change (if (!(StatusFlags.ofRFLAGS u.RFLAGS).ZF) then _ else _) = _
  rw [htarget, hf, hcnt]
  split <;> rename_i h
  · have hn : (Operand.reg loop.counter : Operand 64).read s - 1 ≠ 0 := by simpa using h
    simp only [hn, ↓reduceIte]
  · have hz : (Operand.reg loop.counter : Operand 64).read s - 1 = 0 := by simpa using h
    simp only [hz, ↓reduceIte]
    cases loop <;> rfl

theorem iterate [Bindings] (loop : SquareLoop) {boundary : ReturnBoundary}
    {α : Type} (sq : α → α) (I : α → RamState → Prop)
    (preserve : ∀ a s t, I a s → AgreesExcept [.reg loop.counter, .flags, .rip] s t → I a t)
    (body : ∀ a n s, I a s → s.RIP = loop.site.pc →
      (Operand.reg loop.counter : Operand 64).read s = BitVec.ofNat 64 (n + 1) →
      ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧
        CodeIn Extracted.programSections.toCodeMap u ∧ stackPtr u ≠ boundary.rsp ∧
        u.RIP = loop.site.pc + (60 : BitVec 64) ∧
        (Operand.reg loop.counter : Operand 64).read u = BitVec.ofNat 64 (n + 1) ∧ I (sq a) u)
    (n : Nat) (hn : n < 2 ^ 64) (a : α) (s : RamState)
    (hinv : I a s) (hip : s.RIP = loop.site.pc)
    (hc : (Operand.reg loop.counter : Operand 64).read s = BitVec.ofNat 64 (n + 1)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      t.RIP = loop.site.pc + (65 : BitVec 64) ∧ (Operand.reg loop.counter : Operand 64).read t = 0 ∧
      I (Common.Field.SqrtChain.iter sq (n + 1) a) t := by
  obtain ⟨k, u, hku, hru, hcode, hsp, hpc, hcount, hi⟩ := body a n s hinv hip hc
  obtain ⟨t, hkt, hrt, hct, htpc, hf⟩ := loop.decrement hru hcode hpc hsp
  have hval : (Operand.reg loop.counter : Operand 64).read t = BitVec.ofNat 64 n := by
    rw [hct, hcount, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have hit := preserve _ _ _ hi hf
  cases n with
  | zero =>
    exact ⟨_, t, hku.trans hkt, hrt, by simpa [hval] using htpc, hval, hit⟩
  | succ n =>
    have hne : (BitVec.ofNat 64 (n+1)) ≠ 0 := by
      intro he
      have hv := congrArg BitVec.toNat he
      change (n+1) % 2^64 = 0 at hv
      rw [Nat.mod_eq_of_lt hn] at hv
      omega
    obtain ⟨m, v, hmv, hrv, hpcv, hc0, hiv⟩ := loop.iterate sq I preserve body n (by omega)
      (sq a) t hit (by simpa only [hval, hne, ↓reduceIte] using htpc) hval
    exact ⟨_, v, (hku.trans hkt).trans hmv, hrv, hpcv, hc0, hiv⟩
termination_by n

end SquareLoop

end K256.Proofs.Sec1.Sqrt
