import K256.Spec.Ecdsa
import K256.Proofs.Common.Encoding
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm

set_option autoImplicit false

namespace K256.Proofs.Signing

open K256.Spec
open Standards.NIST.SHA2 Standards.RFC.DeterministicSigning
open Standards.SECG.ECC.Encoding Standards.SECG.DomainParameters

private theorem fin_collision {m n : Nat} (code : Fin m → Fin n) (h : n < m) :
    ∃ i j, i.val < j.val ∧ code i = code j := by
  classical
  by_cases collision : ∃ i j, i ≠ j ∧ code i = code j
  · obtain ⟨i, j, different, equal⟩ := collision
    rcases Nat.lt_or_gt_of_ne (fun eq => different (Fin.ext eq)) with lt | gt
    · exact ⟨i, j, lt, equal⟩
    · exact ⟨j, i, gt, equal.symm⟩
  · have nodup : ((List.finRange m).map code).Nodup :=
      (List.nodup_finRange m).map code fun i j different equal =>
        collision ⟨i, j, different, equal⟩
    have len := nodup.length_le_of_subset (fun {i} _ => List.mem_finRange i)
    exact False.elim (Nat.not_le_of_lt h
      (by simpa only [List.length_map, List.length_finRange] using len))

private theorem foldOctets_lt (bytes : List UInt8) (initial limit : Nat)
    (bound : initial < limit) :
    bytes.foldl (fun value byte => 256 * value + byte.toNat) initial <
      256 ^ bytes.length * limit := by
  induction bytes generalizing initial limit with
  | nil =>
    simpa only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.one_mul] using bound
  | cons byte bytes ih =>
    rw [List.foldl_cons, List.length_cons, Nat.pow_succ, Nat.mul_assoc]
    have byteBound := byte.toNat_lt
    exact ih _ _ (by omega)

private theorem octetsToNat_lt (bytes : ByteArray) :
    octetsToNat bytes < 256 ^ bytes.size := by
  have bound := foldOctets_lt bytes.data.toList 0 1 Nat.zero_lt_one
  simpa only [octetsToNat, Array.foldl_toList, Array.length_toList, ByteArray.size_data,
    Nat.mul_one] using bound

private def SizedState (state : Nonce.State) : Prop :=
  state.key.size = 32 ∧ state.value.size = 32

private def stateCode (state : Nonce.State) (size : SizedState state) : Fin (2 ^ 512) :=
  ⟨octetsToNat (state.key ++ state.value), by
    have bound := octetsToNat_lt (state.key ++ state.value)
    rw [ByteArray.size_append, size.1, size.2] at bound
    have power : 256 ^ (32 + 32) = 2 ^ 512 := by decide +kernel
    exact power ▸ bound⟩

private theorem stateCode_injective {s t : Nonce.State} {hs : SizedState s} {ht : SizedState t}
    (equal : stateCode s hs = stateCode t ht) : s = t := by
  have codeEq : octetsToNat (s.key ++ s.value) = octetsToNat (t.key ++ t.value) :=
    congrArg Fin.val equal
  have sizeEq : (s.key ++ s.value).size = (t.key ++ t.value).size := by
    rw [ByteArray.size_append, ByteArray.size_append, hs.1, hs.2, ht.1, ht.2]
  have bytesEq : s.key ++ s.value = t.key ++ t.value := by
    rw [← Common.Encoding.natToOctets_octetsToNat (s.key ++ s.value), sizeEq, codeEq,
      Common.Encoding.natToOctets_octetsToNat]
  have keyEq := ByteArray.append_inj_left bytesEq (hs.1.trans ht.1.symm)
  rw [keyEq] at bytesEq
  have valueEq := (ByteArray.append_right_inj t.key).mp bytesEq
  cases s
  cases t
  cases keyEq
  cases valueEq
  rfl

def candidate (state : Nonce.State) : Nat × Nonce.State :=
  Nonce.candidate SHA256.hashBytes 64 32 Secp256k1.domain.n state

def retry (state : Nonce.State) : Nonce.State :=
  Nonce.reject SHA256.hashBytes 64 (candidate state).2

private def retryAfter : Nat → Nonce.State → Nonce.State
  | 0, state => state
  | count + 1, state => retryAfter count (retry state)

private theorem hashBytes_size (input : ByteArray) : (SHA256.hashBytes input).size = 32 :=
  Vector.size_toArray _

private theorem hmac_size (key input : ByteArray) :
    (Standards.RFC.HMAC.hmac SHA256.hashBytes 64 key input).size = 32 := by
  unfold Standards.RFC.HMAC.hmac
  exact hashBytes_size _

private theorem initialState_sized (d : Nat) (digest : ByteArray) :
    SizedState (Nonce.initialState SHA256.hashBytes 64 32 Secp256k1.domain.n d digest) := by
  exact ⟨hmac_size _ _, hmac_size _ _⟩

private theorem retry_sized (state : Nonce.State) : SizedState (retry state) :=
  ⟨hmac_size _ _, hmac_size _ _⟩

private theorem retryAfter_sized (count : Nat) {state : Nonce.State} (size : SizedState state) :
    SizedState (retryAfter count state) := by
  induction count generalizing state with
  | zero => exact size
  | succ count ih => exact ih (retry_sized state)

abbrev attempts {Signature : Type} (sign : Nat → Option Signature) :=
  Signing.signingAttempts SHA256.hashBytes 64 32 Secp256k1.domain.n sign

def attemptResult {Signature : Type} (sign : Nat → Option Signature)
    (state : Nonce.State) : Option Signature :=
  let nonce := (candidate state).1
  if 0 < nonce && nonce < Secp256k1.domain.n then sign nonce else none

theorem attempts_succ {Signature : Type} (sign : Nat → Option Signature)
    (count : Nat) (state : Nonce.State) :
    attempts sign (count + 1) state =
      (attemptResult sign state).orElse (fun _ => attempts sign count (retry state)) := by
  unfold attempts attemptResult retry
  rw [Signing.signingAttempts]
  change (let (nonce, next) := candidate state
          match (if 0 < nonce && nonce < Secp256k1.domain.n then sign nonce else none) with
          | some signature => some signature
          | none => Signing.signingAttempts SHA256.hashBytes 64 32 Secp256k1.domain.n sign count
              (Nonce.reject SHA256.hashBytes 64 next)) = _
  cases candidate state with
  | mk nonce next =>
    dsimp only
    cases (if 0 < nonce && nonce < Secp256k1.domain.n then sign nonce else none) <;> rfl

private theorem attempts_append {Signature : Type} (sign : Nat → Option Signature)
    (first second : Nat) (state : Nonce.State) :
    attempts sign (first + second) state =
      (attempts sign first state).orElse (fun _ => attempts sign second (retryAfter first state)) := by
  induction first generalizing state with
  | zero => rw [Nat.zero_add]; rfl
  | succ first ih =>
    rw [Nat.succ_add, attempts_succ, attempts_succ sign first]
    cases h : attemptResult sign state with
    | none => exact ih (retry state)
    | some signature => rfl

private theorem attempts_le {Signature : Type} (sign : Nat → Option Signature)
    (state : Nonce.State) {count budget : Nat} {signature : Signature}
    (le : count ≤ budget) (found : attempts sign count state = some signature) :
    attempts sign budget state = some signature := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [attempts_append, found]
  rfl

private theorem attempts_bound {Signature : Type} (sign : Nat → Option Signature)
    (state : Nonce.State) (size : SizedState state) {count : Nat} {signature : Signature}
    (found : attempts sign count state = some signature) :
    attempts sign (2 ^ 512) state = some signature := by
  induction count using Nat.strongRecOn with
  | ind count ih =>
    by_cases enough : count ≤ 2 ^ 512
    · exact attempts_le sign state enough found
    let code (i : Fin count) : Fin (2 ^ 512) :=
      stateCode (retryAfter i.val state) (retryAfter_sized i.val size)
    obtain ⟨i, j, increasing, collide⟩ := fin_collision code (Nat.lt_of_not_ge enough)
    have sameState : retryAfter i.val state = retryAfter j.val state :=
      stateCode_injective collide
    have jlt := j.isLt
    have split := attempts_append sign j.val (count - j.val) state
    rw [Nat.add_sub_of_le (Nat.le_of_lt jlt), found] at split
    cases hj : attempts sign j.val state with
    | some earlier =>
      rw [hj] at split
      have sameSignature : earlier = signature := Option.some.inj split.symm
      exact ih j.val jlt (sameSignature ▸ hj)
    | none =>
      rw [hj] at split
      have suffix : attempts sign (count - j.val) (retryAfter j.val state) = some signature :=
        split.symm
      have shorter : attempts sign (i.val + (count - j.val)) state = some signature := by
        rw [attempts_append, sameState]
        cases hi : attempts sign i.val state with
        | none => exact suffix
        | some earlier =>
          have impossible : some earlier = none := by
            rw [← Nat.add_sub_of_le (Nat.le_of_lt increasing), attempts_append, hi] at hj
            exact hj
          cases impossible
      exact ih _ (by omega) shorter

theorem signatureWithin_bound {d attempts : Nat} {message : ByteArray} {rs : Nat × Nat}
    (found : Ecdsa.signatureWithin d message attempts = some rs) :
    Ecdsa.signatureWithin d message (2 ^ 512) = some rs := by
  unfold Ecdsa.signatureWithin Signing.signWithin at found ⊢
  exact attempts_bound _ _ (initialState_sized _ _) found

end K256.Proofs.Signing
