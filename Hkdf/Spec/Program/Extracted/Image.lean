/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import Hkdf.Spec.Program.Extracted.Sections
import Hkdf.Spec.Program.Extracted.Symbols
import Prelude.ImageSections

namespace Hkdf.Spec.Program.Extracted

/-- The selected sections at their link-time addresses, code sections first -/
def programSections : Prelude.ImageSections :=
  [⟨textAddress, textBytes⟩,
   ⟨rodataAddress, rodataBytes⟩]

/-- The selected sections as the code map that the user-process model installs -/
def programImage : X86.UserProcess.CodeMap := programSections.toCodeMap

end Hkdf.Spec.Program.Extracted
