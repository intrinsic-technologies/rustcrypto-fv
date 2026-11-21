/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import Prelude.Bytes.Include

namespace Sha3.Spec.Program.Extracted

/-- Not position independent: Linux loads these addresses unchanged -/
def positionIndependent : Bool := false

/-- The link-time address of the code section `.text` -/
def textAddress : BitVec 64 := 0x100000

/-- The bytes of the code section `.text`, from `text.bin` -/
def textBytes : Prelude.Bytes.Chunked := include_chunked_bytes "text.bin"

/-- The bytes of the code section `.text` as a byte array -/
def textByteArray : ByteArray := textBytes.toByteArray

/-- The link-time address of the data section `.rodata` -/
def rodataAddress : BitVec 64 := 0x200000

/-- The bytes of the data section `.rodata`, from `rodata.bin` -/
def rodataBytes : Prelude.Bytes.Chunked := include_chunked_bytes "rodata.bin"

/-- The bytes of the data section `.rodata` as a byte array -/
def rodataByteArray : ByteArray := rodataBytes.toByteArray

end Sha3.Spec.Program.Extracted
