import P256.Proofs.Common.Instructions.AddByte.Memory.Effect

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.AddByte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem add_rsp_disp8_imm8_effect_step [Bindings] (p : BitVec 64) (disp : BitVec 8)
    (imm : UInt8) :
    StepEffect (RmwPre p (.sib 4 none 0 (.d8 disp)) 1 5)
      (codeRange p [0x80, 0x44, 0x24, UInt8.ofBitVec disp, imm])
      (addM8Imm8Effect p 5 (.sib 4 none 0 (.d8 disp)) imm.toBitVec) := by
  have hm : (AddrMode.sib 4 none 0 (.d8 disp)).modrm 0 = 0x44 := by
    simp [AddrMode.modrm, AddrMode.mod, AddrMode.rm, Disp.mod]
  have hs : AddrMode.sibByte 4 none 0 = 0x24 := rfl
  have h := add_m8_imm8_effect_step p (.sib 4 none 0 (.d8 disp))
    ⟨by decide, fun _ => by decide⟩ rfl rfl imm
  rw [hm] at h
  simp only [AddrMode.tail, hs, Disp.bytes, immBytes_eight] at h
  simpa using h

end P256.Proofs.Common.Instructions.AddByte
