import Base16ct.Proofs.Copied.Md5.Spec.Program.Binary.Sections
import X86.UserProcess.CodeImage
import Prelude.ImageSections

namespace Base16ct.Proofs.Copied.Md5.Spec.Program.Extracted

def programSections : Prelude.ImageSections :=
  [⟨textAddress, textBytes⟩,
   ⟨rodataAddress, rodataBytes⟩]

def programImage : X86.UserProcess.CodeMap := programSections.toCodeMap

end Base16ct.Proofs.Copied.Md5.Spec.Program.Extracted
