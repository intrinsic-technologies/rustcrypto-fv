import Sha1.Proofs.Compress.Routine.Interface

namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec Sha1.Spec.Program Standards.NIST

theorem Context.state_zero (c : Context) : c.state 0 = c.H := rfl

theorem Context.state_succ (c : Context) {k : Nat} (hk : k < c.count) :
    c.state (k + 1) = SHA1.compress (c.state k) (c.message k) := by
  have hp : k < (SHA2.SHA256.parse (SHA2.bytesToBits c.blocks)).size := by
    rwa [Parser.parse_size]
  have hp' : k < (SHA2.SHA256.parse (SHA2.bytesToBits c.blocks)).toList.length := hp
  simp only [Context.state]
  rw [List.take_succ_eq_append_getElem hp', List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, Array.getElem_toList,
    Context.message, getElem?_pos (SHA2.SHA256.parse (SHA2.bytesToBits c.blocks)) k hp,
    Option.getD_some]

theorem Context.state_count (c : Context) :
    c.state c.count =
      (SHA2.SHA256.parse (SHA2.bytesToBits c.blocks)).foldl SHA1.compress c.H := by
  have hs : c.count = (SHA2.SHA256.parse (SHA2.bytesToBits c.blocks)).toList.length := by
    rw [Array.length_toList, Parser.parse_size]
    rfl
  unfold Context.state
  rw [hs, List.take_length, Array.foldl_toList]

end Sha1.Proofs.Compress.Routine
