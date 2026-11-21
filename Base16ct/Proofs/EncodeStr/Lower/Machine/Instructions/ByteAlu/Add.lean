import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Slices.Byte.Add
namespace Base16ct.Proofs.EncodeStr.Lower

open X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Byte

theorem add_r11b_r10b_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x45, 0x00, 0xd3])
      (addR8R8Effect p 11 10) :=
  add_r8_r8_effect_step p 0x45 0xd3 (by unfold RexPrefix; decide +kernel)
    (by decide +kernel)

theorem add_r11b_r10b_triple [Bindings] (p : BitVec 64) :
    Triple (fun s ↦ s.RIP = p) (codeRange p [0x45, 0x00, 0xd3])
      (Effect.post (addR8R8Effect p 11 10)) :=
  Triple.of_effect (fun s _ ↦ addR8R8Effect_avoids p 11 10 s _)
    (add_r11b_r10b_effect_step p)

theorem add_r10b_r9b_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x45, 0x00, 0xca])
      (addR8R8Effect p 10 9) :=
  add_r8_r8_effect_step p 0x45 0xca (by unfold RexPrefix; decide +kernel)
    (by decide +kernel)

theorem add_r10b_r9b_triple [Bindings] (p : BitVec 64) :
    Triple (fun s ↦ s.RIP = p) (codeRange p [0x45, 0x00, 0xca])
      (Effect.post (addR8R8Effect p 10 9)) :=
  Triple.of_effect (fun s _ ↦ addR8R8Effect_avoids p 10 9 s _)
    (add_r10b_r9b_effect_step p)

end Base16ct.Proofs.EncodeStr.Lower
