import Md5.Proofs.Buffered.Update.Counter.Effect
import Md5.Proofs.Buffered.Update.Counter.Step

namespace Md5.Proofs.Buffered.Update.Counter

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem inc_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Md5.Proofs.Memory.StorePre p (3 + am.tail.length)
      (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0xFF :: am.modrm 0 :: am.tail)) (incM64Effect p am) := by
  intro s h hcode hpre
  obtain ⟨hp, hw, _⟩ := hpre
  subst hp
  have hlen := am.tail_length_le
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 :=
    hcode.low_len (by simp; omega) (by omega) (by omega)
  refine ⟨_, inc_m64_step s h rex hrex am hv hx hb hcode.bytesAt hlow hw,
    afterStep_rmw_ready h _ _ _ _ _ hw.tables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, ?_, AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem add_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Md5.Proofs.Memory.StorePre p (3 + am.tail.length)
      (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0x01 :: am.modrm reg :: am.tail))
      (addM64R64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  intro s h hcode hpre
  obtain ⟨hp, hw, _⟩ := hpre
  subst hp
  have hlen := am.tail_length_le
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 :=
    hcode.low_len (by simp; omega) (by omega) (by omega)
  refine ⟨_, add_m64_r64_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hw,
    afterStep_rmw_ready h _ _ _ _ _ hw.tables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, ?_, AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end Md5.Proofs.Buffered.Update.Counter
