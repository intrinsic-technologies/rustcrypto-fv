import P256.Proofs.Sec1.Wrapper.Success.Call

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success

def serializeSite : CallSite 72 65 328 where
  codeOffset := 0x186b
  disp := 0xf500
  entry := 0x110d70
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryProgram := P256.Proofs.Program.inProgram_of_textOffset 0x10d70 (by decide)
  layout := ⟨240, 96, 232, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  stack := rfl

end P256.Proofs.Sec1.Wrapper.Success
