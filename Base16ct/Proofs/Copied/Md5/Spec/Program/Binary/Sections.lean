import Prelude.Bytes.Include

namespace Base16ct.Proofs.Copied.Md5.Spec.Program.Extracted

def textAddress : BitVec 64 := 0x100000

def textBytes : Prelude.Bytes.Chunked := include_chunked_bytes "text.bin"

def rodataAddress : BitVec 64 := 0x200000

def rodataBytes : Prelude.Bytes.Chunked := include_chunked_bytes "rodata.bin"

end Base16ct.Proofs.Copied.Md5.Spec.Program.Extracted
