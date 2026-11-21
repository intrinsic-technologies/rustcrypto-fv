import AesGcm.Proofs.Machine.GHASHInterface
import AesGcm.Proofs.Machine.LIR.Fn1034c0.Frame
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface
open AesGcm.Proofs.Machine.GHASH

theorem oneBlock_call (code : CodeMap) (hmultiply : MultiplyContract code) :
    CallContract LIR.lifted code .l1034c0 LIR.Fn1034c0.frameInfo
      (fun fr => [span (fr.rdi + 16) 16])
      (fun fr mem => Readable mem fr.rsi 16 ∧ Writable code mem fr.rdi 32 ∧
        (callStack fr).Disjoint (span fr.rdi 32))
      (fun fr mem =>
        let r := polyvalMultiplyWords
          (memLoad fr.original fr.rsi 64 ^^^ memLoad fr.original (fr.rdi + 16) 64)
          (memLoad fr.original (fr.rsi + 8) 64 ^^^ memLoad fr.original (fr.rdi + 24) 64)
          (memLoad fr.original fr.rdi 64) (memLoad fr.original (fr.rdi + 8) 64)
        memLoad mem (fr.rdi + 16) 64 = r.1 ∧ memLoad mem (fr.rdi + 24) 64 = r.2) := by
  intro fr loc hl hm hentry htypes hpre
  rcases loc with ⟨label, args, mem⟩
  dsimp only at hl hm hentry htypes hpre
  subst label mem
  change args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
    args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
    args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
    args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
    args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
    args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
    Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 128) 128 ∧
    fr.low.toNat + 128 ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True at hentry
  rcases hentry with ⟨hsp, hdf, h1, -, h3, h5, hsrc, hdst, h8, h9, h12, h13, h14, h15,
    h39, h50, h51, hreadret, hret, hretlow, hstack, hroom, halign, -⟩
  rcases hpre with ⟨hr, hw, hsep⟩
  have load0 : LoadOk fr.original fr.rsi 8 :=
    LoadOk.of_offsets hr (addr_self _) (addr_self _) (by decide)
  have load1 : LoadOk fr.original (fr.rsi + 8) 8 :=
    LoadOk.of_offsets hr rfl (addr_self _) (by decide)
  have hs : args[6].get 64 = fr.rsi := by rw [hsrc]; rfl
  let callee : Activation := {fr with
    rsi := memLoad fr.original fr.rsi 64
    rdx := memLoad fr.original (fr.rsi + 8) 64}
  have hstep : ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l1034c0, args, fr.original⟩ =
        .jump ⟨.l102bd0, nextArgs, fr.original⟩ ∧
      Atom.All code nextArgs fr.original (LIR.Fn102bd0.frameInfo.entryAtoms callee) ∧
      GPRsTyped nextArgs := by
    cfg_eval [hs]
    simp only [BitVec.ofNat_eq_ofNat] at load0 load1 ⊢
    simp only [load0, load1, ite_true]
    refine ⟨_, rfl, ?_, ?_⟩
    · change args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
        _ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
        _ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
        args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
        args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
        args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
        Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
        fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 128) 128 ∧
        fr.low.toNat + 128 ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True
      exact ⟨hsp, hdf, h1, rfl, h3, h5, rfl, hdst, h8, h9, h12, h13, h14, h15,
        h39, h50, h51, hreadret, hret, hretlow, hstack, hroom, halign, trivial⟩
    · apply GPRsTyped.of_updates htypes [0, 2, 6]
      · rintro ⟨r, hr⟩ hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with rfl | rfl | rfl <;> rfl
      · rintro ⟨r, hr⟩ hout
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
        have hc : r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨
            r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨nextArgs, hrun, hentry', htypes'⟩ := hstep
  obtain ⟨o, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    hmultiply callee ⟨.l102bd0, nextArgs, fr.original⟩ rfl rfl hentry' htypes' ⟨hw, hsep⟩
  refine ⟨o, .next ?_ hexec, htag, hdone, houtTypes, hframe, hpost⟩
  change (LIR.program.runBlock (dialect code) ⟨.l1034c0, args, fr.original⟩).next
    (dialect code) [] = .next ⟨⟨.l102bd0, nextArgs, fr.original⟩, []⟩
  rw [hrun]
  rfl

end AesGcm.Proofs.Machine.GHASHUpdate
