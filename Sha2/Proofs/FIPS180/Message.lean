import Sha2.Spec.Program
import Sha2.Proofs.FIPS180.Encoding

namespace Sha2.Proofs.FIPS180
open Standards.NIST.SHA2
open Sha2.Spec.Program

theorem message_data (inputs : Array Input) :
    (message inputs).data = inputs.flatMap (fun input => input.bytes.data) := by
  unfold message
  rw [Array.flatMap_eq_foldl]
  have h (l : List Input) (acc : ByteArray) :
      (l.foldl (fun message input => message ++ input.bytes) acc).data =
        l.foldl (fun data input => data ++ input.bytes.data) acc.data := by
    induction l generalizing acc with
    | nil => rfl
    | cons x l ih =>
      simp only [List.foldl_cons, ih, ByteArray.data_append]
  simpa only [← Array.foldl_toList, ByteArray.data_empty] using h inputs.toList ByteArray.empty

theorem message_push (inputs : Array Input) (input : Input) :
    message (inputs.push input) = message inputs ++ input.bytes := by
  simp only [message, Array.foldl_push]

theorem message_append (inputs more : Array Input) :
    message (inputs ++ more) = message inputs ++ message more := by
  apply ByteArray.ext
  simp only [message_data, Array.flatMap_append, ByteArray.data_append]

theorem bytesToBits_message (inputs : Array Input) :
    bytesToBits (message inputs) = inputs.flatMap (fun input => bytesToBits input.bytes) := by
  simp only [bytesToBits, message_data, Array.flatMap_assoc]

end Sha2.Proofs.FIPS180
