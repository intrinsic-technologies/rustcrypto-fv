/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import Prelude.Bytes.Include

namespace Base16ct.Spec.Program.Extracted

/-- Not position independent: Linux loads these addresses unchanged -/
def positionIndependent : Bool := false

/-- The link-time address of the code section `.text` -/
def textAddress : BitVec 64 := 0x100000

/-- The bytes of the code section `.text`, from `text.bin` -/
def textBytes : Prelude.Bytes.Chunked := include_chunked_bytes "text.bin"

/-- The bytes of the code section `.text` as a byte array -/
def textByteArray : ByteArray := textBytes.toByteArray

end Base16ct.Spec.Program.Extracted
