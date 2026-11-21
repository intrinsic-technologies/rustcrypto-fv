import Hkdf.Spec.RFC5869

namespace Hkdf.Statements

open Hkdf.Spec

abbrev hkdf_sha256_new_expand_writes_okm_or_rejects_length.match_1.{u_1}
    (motive : Except RFC5869.ExpandError ByteArray → Sort u_1)
    (x : Except RFC5869.ExpandError ByteArray)
    (h_1 : (okm : ByteArray) → motive (.ok okm))
    (h_2 : Unit → motive (.error .invalidPrkLength))
    (h_3 : Unit → motive (.error .invalidLength)) : motive x :=
  Except.casesOn x (fun a => RFC5869.ExpandError.casesOn a (h_2 ()) (h_3 ())) (fun a => h_1 a)

end Hkdf.Statements
