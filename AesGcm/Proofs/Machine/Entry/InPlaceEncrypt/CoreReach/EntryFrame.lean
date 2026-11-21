import AesGcm.Proofs.Machine.LIR.Fn102520.Frame
import AesGcm.Proofs.Machine.LIR.Aes128gcmEncryptInPlace.Frame
import AesGcm.Proofs.Machine.Runtime.StackGeometry
import AesGcm.Proofs.Machine.Runtime.Frame

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem core_entry_frame {code : CodeMap} {fr : Activation}
    {args regs : Values Value Reg.count} {mem childMem : Ram}
    (working : Atom.All code args mem (LIR.Aes128gcmEncryptInPlace.frameAt .l1013c8 fr))
    (setup : RamWriteFrame mem childMem [span (fr.rsp - 480) 64])
    (sp : regs[4].get 64 = fr.rsp - 480)
    (ret : memLoad childMem (fr.rsp - 480) 64 = 0x101409)
    (keep : ∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → regs[r] = args[r])
    (typed : GPRsTyped regs) :
    Atom.All code regs childMem (LIR.Fn102520.frameInfo.entryAtoms
      (activationOfValues childMem regs 0x101409 (fr.rsp - 2848))) := by
  obtain ⟨_, df, _, _, _, _, _, fp39, fp50, fp51, _, _, _, _, _, _, _,
    _, _, stack, room, align, s0r, s0, s1r, s1, s2r, s2, s3r, s3, slotSep, _⟩ := working
  change Writable code mem (fr.rsp - 2848) 2848 at stack
  change fr.low.toNat + 2848 ≤ fr.rsp.toNat at room
  change fr.rsp.toNat % 16 = 8 at align
  change 0x201d58 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208 at slotSep
  have childNat : (fr.rsp - (480 : BitVec 64)).toNat = fr.rsp.toNat - 480 :=
    stack_sub_toNat fr room (by decide : 480 ≤ 2848)
  have lowerNat : (fr.rsp - (2848 : BitVec 64)).toNat = fr.rsp.toNat - 2848 :=
    stack_sub_toNat fr room (Nat.le_refl _)
  have slotOutside (slot : BitVec 64) (hlo : 0x201208 ≤ slot.toNat)
      (hhi : slot.toNat + 8 ≤ 0x201238) :
      Outside [span (fr.rsp - 480) 64] slot 8 := by
    refine ⟨by omega, ?_⟩
    intro region hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, childNat]
    omega
  apply frame_entryAtoms
  · rintro ⟨r, hr⟩ hin
    simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hin
    have hv := typed.value ⟨r, by omega⟩
    refine hv.trans ?_
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> rfl
  · change regs[39] = ⟨32, regs[39].get 32⟩
    have h : regs[39] = ⟨32, fr.mxcsr⟩ := (keep 39 (by decide)).trans fp39
    rw [h]
    rfl
  · change regs[50] = ⟨16, regs[50].get 16⟩
    have h : regs[50] = ⟨16, fr.ftw⟩ := (keep 50 (by decide)).trans fp50
    rw [h]
    rfl
  · change regs[51] = ⟨16, regs[51].get 16⟩
    have h : regs[51] = ⟨16, fr.fcw⟩ := (keep 51 (by decide)).trans fp51
    rw [h]
    rfl
  · exact (keep 22 (by decide)).trans df
  · change Readable childMem (regs[4].get 64) 8
    rw [sp]
    exact (stack.of_frame setup).readable.sub (by rw [lowerNat, childNat]; omega)
      (by rw [lowerNat, childNat]; omega)
  · change memLoad childMem (regs[4].get 64) 64 = 0x101409
    rw [sp]
    exact ret
  · change (0x101409 : BitVec 64).toNat < 2 ^ 32
    decide
  · intro _
    change Writable code childMem (regs[4].get 64 - 2368) 2368
    rw [sp, show fr.rsp - (480 : BitVec 64) - 2368 = fr.rsp - 2848 by bv_omega]
    exact (stack.of_frame setup).sub (Nat.le_refl _)
      (Nat.add_le_add_left (by decide : 2368 ≤ 2848) _)
  · change (fr.rsp - (2848 : BitVec 64)).toNat + 2368 ≤ (regs[4].get 64).toNat
    rw [sp, childNat, lowerNat]
    omega
  · change (regs[4].get 64).toNat % 16 = 8
    rw [sp, childNat]
    omega
  · refine ⟨s0r.of_frame setup, (setup.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans s0,
      s1r.of_frame setup, (setup.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans s1,
      s2r.of_frame setup, (setup.memLoad_eq (slotOutside 0x201228 (by decide) (by decide))).trans s2,
      s3r.of_frame setup, (setup.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans s3,
      ?_, trivial⟩
    change 0x201b78 ≤ (regs[4].get 64).toNat ∨ (regs[4].get 64).toNat ≤ 0x201208
    rw [sp, childNat]
    omega

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
