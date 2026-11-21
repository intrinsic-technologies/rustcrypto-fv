import Standards.RFC.MD5.Conversion
import Standards.RFC.MD5.Padding
import Standards.RFC.MD5.Buffer
import Standards.RFC.MD5.Processing

/-!
# The MD5 message-digest algorithm

RFC 1321, "The MD5 Message-Digest Algorithm" (R. Rivest, April 1992): the output step of §3.5 and
the message digest of §3, composed from the steps in the other `Standards/RFC/MD5/` modules.

Source: https://www.rfc-editor.org/rfc/rfc1321
-/

namespace Standards.RFC.MD5

/--
The buffer A, B, C, D as 16 bytes, from the low-order byte of A to the high-order byte of D
(RFC 1321, §3.5)
-/
def Buffer.toBytes (buffer : Buffer) : Vector UInt8 16 :=
  (#v[buffer.A, buffer.B, buffer.C, buffer.D].map bytesOfWord).flatten

/--
The 16-byte MD5 message digest of a message of any number of bits, including zero
(RFC 1321, §3, Steps 1 to 5)
-/
def messageDigest (message : Array Bool) : Vector UInt8 16 :=
  let padded := appendLength message.size (appendPaddingBits message)
  let M := wordsOfBytes (bytesOfBits padded)
  (processBlocks Buffer.initial M).toBytes

end Standards.RFC.MD5
