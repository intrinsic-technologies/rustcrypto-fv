import AesGcm.Proofs.Machine.Fixslice.Representation
import AesGcm.Proofs.Machine.Common.SubBytes

namespace AesGcm.Proofs.Machine.Fixslice

local instance : HXor Bool Bool Bool := ⟨Bool.xor⟩
local instance : HAnd Bool Bool Bool := ⟨Bool.and⟩

def subBytesCircuit {α : Type} [HXor α α α] [HAnd α α α]
    (state : Fin 8 → α) : Fin 8 → α :=
  let u7 := state 0
  let u6 := state 1
  let u5 := state 2
  let u4 := state 3
  let u3 := state 4
  let u2 := state 5
  let u1 := state 6
  let u0 := state 7
  let y14 := u3 ^^^ u5
  let y13 := u0 ^^^ u6
  let y12 := y13 ^^^ y14
  let t1 := u4 ^^^ y12
  let y15 := t1 ^^^ u5
  let t2 := y12 &&& y15
  let y6 := y15 ^^^ u7
  let y20 := t1 ^^^ u1
  let y9 := u0 ^^^ u3
  let y11 := y20 ^^^ y9
  let t12 := y9 &&& y11
  let y7 := u7 ^^^ y11
  let y8 := u0 ^^^ u5
  let t0 := u1 ^^^ u2
  let y10 := y15 ^^^ t0
  let y17 := y10 ^^^ y11
  let t13 := y14 &&& y17
  let t14 := t13 ^^^ t12
  let y19 := y10 ^^^ y8
  let t15 := y8 &&& y10
  let t16 := t15 ^^^ t12
  let y16 := t0 ^^^ y11
  let y21 := y13 ^^^ y16
  let t7 := y13 &&& y16
  let y18 := u0 ^^^ y16
  let y1 := t0 ^^^ u7
  let y4 := y1 ^^^ u3
  let t5 := y4 &&& u7
  let t6 := t5 ^^^ t2
  let t18 := t6 ^^^ t16
  let t22 := t18 ^^^ y19
  let y2 := y1 ^^^ u0
  let t10 := y2 &&& y7
  let t11 := t10 ^^^ t7
  let t20 := t11 ^^^ t16
  let t24 := t20 ^^^ y18
  let y5 := y1 ^^^ u6
  let t8 := y5 &&& y1
  let t9 := t8 ^^^ t7
  let t19 := t9 ^^^ t14
  let t23 := t19 ^^^ y21
  let y3 := y5 ^^^ y8
  let t3 := y3 &&& y6
  let t4 := t3 ^^^ t2
  let t17 := t4 ^^^ y20
  let t21 := t17 ^^^ t14
  let t26 := t21 &&& t23
  let t27 := t24 ^^^ t26
  let t31 := t22 ^^^ t26
  let t25 := t21 ^^^ t22
  let t28 := t25 &&& t27
  let t29 := t28 ^^^ t22
  let z14 := t29 &&& y2
  let z5 := t29 &&& y7
  let t30 := t23 ^^^ t24
  let t32 := t31 &&& t30
  let t33 := t32 ^^^ t24
  let t35 := t27 ^^^ t33
  let t36 := t24 &&& t35
  let t38 := t27 ^^^ t36
  let t39 := t29 &&& t38
  let t40 := t25 ^^^ t39
  let t43 := t29 ^^^ t40
  let z3 := t43 &&& y16
  let tc12 := z3 ^^^ z5
  let z12 := t43 &&& y13
  let z13 := t40 &&& y5
  let z4 := t40 &&& y1
  let tc6 := z3 ^^^ z4
  let t34 := t23 ^^^ t33
  let t37 := t36 ^^^ t34
  let t41 := t40 ^^^ t37
  let z8 := t41 &&& y10
  let z17 := t41 &&& y8
  let t44 := t33 ^^^ t37
  let z0 := t44 &&& y15
  let z9 := t44 &&& y12
  let z10 := t37 &&& y3
  let z1 := t37 &&& y6
  let tc5 := z1 ^^^ z0
  let tc11 := tc6 ^^^ tc5
  let z11 := t33 &&& y4
  let t42 := t29 ^^^ t33
  let t45 := t42 ^^^ t41
  let z7 := t45 &&& y17
  let tc8 := z7 ^^^ tc6
  let z16 := t45 &&& y14
  let z6 := t42 &&& y11
  let tc16 := z6 ^^^ tc8
  let z15 := t42 &&& y9
  let tc20 := z15 ^^^ tc16
  let tc1 := z15 ^^^ z16
  let tc2 := z10 ^^^ tc1
  let tc21 := tc2 ^^^ z11
  let tc3 := z9 ^^^ tc2
  let s0 := tc3 ^^^ tc16
  let s3 := tc3 ^^^ tc11
  let s1 := s3 ^^^ tc16
  let tc13 := z13 ^^^ tc1
  let z2 := t33 &&& u7
  let tc4 := z0 ^^^ z2
  let tc7 := z12 ^^^ tc4
  let tc9 := z8 ^^^ tc7
  let tc10 := tc8 ^^^ tc9
  let tc17 := z14 ^^^ tc10
  let s5 := tc21 ^^^ tc17
  let tc26 := tc17 ^^^ tc20
  let s2 := tc26 ^^^ z17
  let tc14 := tc4 ^^^ tc12
  let tc18 := tc13 ^^^ tc14
  let s6 := tc10 ^^^ tc18
  let s7 := z12 ^^^ tc18
  let s4 := tc14 ^^^ s3
  fun p ↦ match p.val with
  | 0 => s7
  | 1 => s6
  | 2 => s5
  | 3 => s4
  | 4 => s3
  | 5 => s2
  | 6 => s1
  | _ => s0

def invSubBytesCircuit {α : Type} [HXor α α α] [HAnd α α α]
    (state : Fin 8 → α) : Fin 8 → α :=
  let u7 := state 0
  let u6 := state 1
  let u5 := state 2
  let u4 := state 3
  let u3 := state 4
  let u2 := state 5
  let u1 := state 6
  let u0 := state 7
  let t23 := u0 ^^^ u3
  let t8 := u1 ^^^ t23
  let m2 := t23 &&& t8
  let t4 := u4 ^^^ t8
  let t22 := u1 ^^^ u3
  let t2 := u0 ^^^ u1
  let t1 := u3 ^^^ u4
  let t9 := u7 ^^^ t1
  let m7 := t22 &&& t9
  let t24 := u4 ^^^ u7
  let t10 := t2 ^^^ t24
  let m14 := t2 &&& t10
  let r5 := u6 ^^^ u7
  let t3 := t1 ^^^ r5
  let t13 := t2 ^^^ r5
  let t19 := t22 ^^^ r5
  let t17 := u2 ^^^ t19
  let t25 := u2 ^^^ t1
  let r13 := u1 ^^^ u6
  let t20 := t24 ^^^ r13
  let m9 := t20 &&& t17
  let r17 := u2 ^^^ u5
  let t6 := t22 ^^^ r17
  let m1 := t13 &&& t6
  let y5 := u0 ^^^ r17
  let m4 := t19 &&& y5
  let m5 := m4 ^^^ m1
  let m17 := m5 ^^^ t24
  let r18 := u5 ^^^ u6
  let t27 := t1 ^^^ r18
  let t15 := t10 ^^^ t27
  let m11 := t1 &&& t15
  let m15 := m14 ^^^ m11
  let m21 := m17 ^^^ m15
  let m12 := t4 &&& t27
  let m13 := m12 ^^^ m11
  let t14 := t10 ^^^ r18
  let m3 := t14 ^^^ m1
  let m16 := m3 ^^^ m2
  let m20 := m16 ^^^ m13
  let r19 := u2 ^^^ u4
  let t16 := r13 ^^^ r19
  let t26 := t3 ^^^ t16
  let m6 := t3 &&& t16
  let m8 := t26 ^^^ m6
  let m18 := m8 ^^^ m7
  let m22 := m18 ^^^ m13
  let m25 := m22 &&& m20
  let m26 := m21 ^^^ m25
  let m10 := m9 ^^^ m6
  let m19 := m10 ^^^ m15
  let m23 := m19 ^^^ t25
  let m28 := m23 ^^^ m25
  let m24 := m22 ^^^ m23
  let m30 := m26 &&& m24
  let m39 := m23 ^^^ m30
  let m48 := m39 &&& y5
  let m57 := m39 &&& t19
  let m36 := m24 ^^^ m25
  let m31 := m20 &&& m23
  let m27 := m20 ^^^ m21
  let m32 := m27 &&& m31
  let m29 := m28 &&& m27
  let m37 := m21 ^^^ m29
  let m42 := m37 ^^^ m39
  let m52 := m42 &&& t15
  let m61 := m42 &&& t1
  let p0 := m52 ^^^ m61
  let p16 := m57 ^^^ m61
  let m60 := m37 &&& t20
  let m51 := m37 &&& t17
  let m33 := m27 ^^^ m25
  let m38 := m32 ^^^ m33
  let m43 := m37 ^^^ m38
  let m49 := m43 &&& t16
  let p6 := m49 ^^^ m60
  let p13 := m49 ^^^ m51
  let m58 := m43 &&& t3
  let m50 := m38 &&& t9
  let m59 := m38 &&& t22
  let p1 := m58 ^^^ m59
  let p7 := p0 ^^^ p1
  let m34 := m21 &&& m22
  let m35 := m24 &&& m34
  let m40 := m35 ^^^ m36
  let m41 := m38 ^^^ m40
  let m45 := m42 ^^^ m41
  let m53 := m45 &&& t27
  let p8 := m50 ^^^ m53
  let p23 := p7 ^^^ p8
  let m62 := m45 &&& t4
  let p14 := m49 ^^^ m62
  let s6 := p14 ^^^ p23
  let m54 := m41 &&& t10
  let p2 := m54 ^^^ m62
  let p22 := p2 ^^^ p7
  let s0 := p13 ^^^ p22
  let p17 := m58 ^^^ p2
  let p15 := m54 ^^^ m59
  let m63 := m41 &&& t2
  let m44 := m39 ^^^ m40
  let m46 := m44 &&& t6
  let p5 := m46 ^^^ m51
  let p18 := m63 ^^^ p5
  let p24 := p5 ^^^ p7
  let p12 := m46 ^^^ m48
  let s3 := p12 ^^^ p22
  let m55 := m44 &&& t13
  let p9 := m55 ^^^ m63
  let s7 := p9 ^^^ p16
  let m47 := m40 &&& t8
  let p3 := m47 ^^^ m50
  let p19 := p2 ^^^ p3
  let s5 := p19 ^^^ p24
  let p11 := p0 ^^^ p3
  let p26 := p9 ^^^ p11
  let m56 := m40 &&& t23
  let p4 := m48 ^^^ m56
  let p20 := p4 ^^^ p6
  let p29 := p15 ^^^ p20
  let s1 := p26 ^^^ p29
  let p10 := m57 ^^^ p4
  let p27 := p10 ^^^ p18
  let s4 := p23 ^^^ p27
  let p25 := p6 ^^^ p10
  let p28 := p11 ^^^ p25
  let s2 := p17 ^^^ p28
  fun p ↦ match p.val with
  | 0 => s7
  | 1 => s6
  | 2 => s5
  | 3 => s4
  | 4 => s3
  | 5 => s2
  | 6 => s1
  | _ => s0

def subBytes (state : Planes) : Planes := subBytesCircuit state

def invSubBytes (state : Planes) : Planes := invSubBytesCircuit state

theorem getLsbD_subBytes (x : Planes) (p : Fin 8) (i : Nat) :
    (subBytes x p).getLsbD i =
      subBytesCircuit (fun q ↦ (x q).getLsbD i) p := by
  rcases p with ⟨p, hp⟩
  have h : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> subst p <;>
    (simp only [subBytes, subBytesCircuit, BitVec.getLsbD_xor, BitVec.getLsbD_and]; rfl)

theorem getLsbD_invSubBytes (x : Planes) (p : Fin 8) (i : Nat) :
    (invSubBytes x p).getLsbD i =
      invSubBytesCircuit (fun q ↦ (x q).getLsbD i) p := by
  rcases p with ⟨p, hp⟩
  have h : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> subst p <;>
    (simp only [invSubBytes, invSubBytesCircuit, BitVec.getLsbD_xor, BitVec.getLsbD_and]; rfl)

def subBytesNots (state : Planes) : Planes := fun p ↦
  if p.val = 0 ∨ p.val = 1 ∨ p.val = 5 ∨ p.val = 6 then ~~~state p else state p

theorem subBytesNots_involutive (x : Planes) : subBytesNots (subBytesNots x) = x := by
  funext p
  simp only [subBytesNots]
  split <;> simp_all only [BitVec.not_not]

theorem getLsbD_subBytesNots (x : Planes) (p : Fin 8) (i : Fin 64) :
    (subBytesNots x p).getLsbD i.val =
      if p.val = 0 ∨ p.val = 1 ∨ p.val = 5 ∨ p.val = 6
      then !(x p).getLsbD i.val else (x p).getLsbD i.val := by
  simp only [subBytesNots]
  split <;> simp only [BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]

theorem subBytesNots_encode (x : Blocks) :
    subBytesNots (encode x) = encode (fun b j ↦ x b j ^^^ 0x63) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show i = (⟨i, hi⟩ : Fin 64).val from rfl, getLsbD_subBytesNots,
    getLsbD_encode, getLsbD_encode, BitVec.getLsbD_xor]
  have h : ∀ p : Fin 8, (0x63 : BitVec 8).getLsbD p.val =
      decide (p.val = 0 ∨ p.val = 1 ∨ p.val = 5 ∨ p.val = 6) := by decide +kernel
  rw [h]
  split <;> simp_all

def subBytesByte (b : BitVec 8) : BitVec 8 :=
  fromBits (subBytesCircuit (fun p ↦ b.getLsbD p.val))

def invSubBytesByte (b : BitVec 8) : BitVec 8 :=
  fromBits (invSubBytesCircuit (fun p ↦ b.getLsbD p.val))

set_option maxRecDepth 4096 in
private theorem subBytesByte_eq_table : ∀ i : Fin 256,
    subBytesByte (BitVec.ofNat 8 i.val) =
      (Standards.NIST.AES.affine (AesGcm.Proofs.Machine.inverseTable (UInt8.ofNat i.val))).toBitVec ^^^
        0x63 := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem invSubBytesByte_eq_table : ∀ i : Fin 256,
    invSubBytesByte (BitVec.ofNat 8 i.val) =
      (AesGcm.Proofs.Machine.inverseTable (Standards.NIST.AES.invAffine
        (UInt8.ofBitVec (BitVec.ofNat 8 i.val ^^^ 0x63)))).toBitVec := by
  decide +kernel

theorem subBytesByte_eq (b : BitVec 8) :
    subBytesByte b =
      (Standards.NIST.AES.sbox (UInt8.ofBitVec b)).toBitVec ^^^ 0x63 := by
  rw [Standards.NIST.AES.sbox, AesGcm.Proofs.Machine.inverse_eq_inverseTable]
  have h := subBytesByte_eq_table ⟨b.toNat, b.isLt⟩
  change subBytesByte (BitVec.ofNat 8 b.toNat) =
    (Standards.NIST.AES.affine (AesGcm.Proofs.Machine.inverseTable
      (UInt8.ofBitVec (BitVec.ofNat 8 b.toNat)))).toBitVec ^^^ 0x63 at h
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

theorem invSubBytesByte_eq (b : BitVec 8) :
    invSubBytesByte b =
      (Standards.NIST.AES.invSbox (UInt8.ofBitVec (b ^^^ 0x63))).toBitVec := by
  rw [Standards.NIST.AES.invSbox, AesGcm.Proofs.Machine.inverse_eq_inverseTable]
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using invSubBytesByte_eq_table ⟨b.toNat, b.isLt⟩

theorem subBytes_encode (x : Blocks) :
    subBytes (encode x) = encode (fun b j ↦
      (Standards.NIST.AES.sbox (UInt8.ofBitVec (x b j))).toBitVec ^^^ 0x63) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_subBytes, getLsbD_encode _ _ ⟨i, hi⟩]
  simp only [getLsbD_encode _ _ (⟨i, hi⟩ : Fin 64)]
  have hb := congrArg (fun b ↦ b.getLsbD p.val)
    (subBytesByte_eq (x ⟨i % 4, by omega⟩ ⟨4 * (i / 4 % 4) + i / 16, by omega⟩))
  simpa only [subBytesByte, invSubBytesByte, getLsbD_fromBits] using hb

theorem invSubBytes_encode (x : Blocks) :
    invSubBytes (encode x) = encode (fun b j ↦
      (Standards.NIST.AES.invSbox (UInt8.ofBitVec (x b j ^^^ 0x63))).toBitVec) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_invSubBytes, getLsbD_encode _ _ ⟨i, hi⟩]
  simp only [getLsbD_encode _ _ (⟨i, hi⟩ : Fin 64)]
  have hb := congrArg (fun b ↦ b.getLsbD p.val)
    (invSubBytesByte_eq (x ⟨i % 4, by omega⟩ ⟨4 * (i / 4 % 4) + i / 16, by omega⟩))
  simpa only [subBytesByte, invSubBytesByte, getLsbD_fromBits] using hb

theorem decode_subBytes (x : Planes) :
    decode (subBytes x) = fun b j ↦
      (Standards.NIST.AES.sbox (UInt8.ofBitVec (decode x b j))).toBitVec ^^^ 0x63 := by
  have h := congrArg decode (subBytes_encode (decode x))
  simpa only [encode_decode, decode_encode] using h

theorem decode_invSubBytes (x : Planes) :
    decode (invSubBytes x) = fun b j ↦
      (Standards.NIST.AES.invSbox (UInt8.ofBitVec (decode x b j ^^^ 0x63))).toBitVec := by
  have h := congrArg decode (invSubBytes_encode (decode x))
  simpa only [encode_decode, decode_encode] using h

theorem subBytesNots_subBytes_encode (x : Blocks) :
    subBytesNots (subBytes (encode x)) = encode (fun b j ↦
      (Standards.NIST.AES.sbox (UInt8.ofBitVec (x b j))).toBitVec) := by
  rw [subBytes_encode, subBytesNots_encode]
  apply congrArg encode
  funext b j
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem invSubBytes_subBytesNots_encode (x : Blocks) :
    invSubBytes (subBytesNots (encode x)) = encode (fun b j ↦
      (Standards.NIST.AES.invSbox (UInt8.ofBitVec (x b j))).toBitVec) := by
  rw [subBytesNots_encode, invSubBytes_encode]
  apply congrArg encode
  funext b j
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem decode_subBytesNots (x : Planes) :
    decode (subBytesNots x) = fun b j ↦ decode x b j ^^^ 0x63 := by
  have h := congrArg decode (subBytesNots_encode (decode x))
  simpa only [encode_decode, decode_encode] using h

theorem decode_subBytesNots_subBytes (x : Planes) :
    decode (subBytesNots (subBytes x)) = fun b j ↦
      (Standards.NIST.AES.sbox (UInt8.ofBitVec (decode x b j))).toBitVec := by
  have h := congrArg decode (subBytesNots_subBytes_encode (decode x))
  simpa only [encode_decode, decode_encode] using h

theorem decode_invSubBytes_subBytesNots (x : Planes) :
    decode (invSubBytes (subBytesNots x)) = fun b j ↦
      (Standards.NIST.AES.invSbox (UInt8.ofBitVec (decode x b j))).toBitVec := by
  have h := congrArg decode (invSubBytes_subBytesNots_encode (decode x))
  simpa only [encode_decode, decode_encode] using h

theorem invSubBytes_subBytes (x : Planes) :
    invSubBytes (subBytes x) = x := by
  rw [← encode_decode x, subBytes_encode, invSubBytes_encode]
  apply congrArg encode
  funext b j
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero,
    UInt8.ofBitVec_toBitVec, AesGcm.Proofs.Machine.invSbox_sbox, UInt8.toBitVec_ofBitVec]

theorem subBytes_invSubBytes (x : Planes) :
    subBytes (invSubBytes x) = x := by
  rw [← encode_decode x, invSubBytes_encode, subBytes_encode]
  apply congrArg encode
  funext b j
  simp only [UInt8.ofBitVec_toBitVec, AesGcm.Proofs.Machine.sbox_invSbox, UInt8.toBitVec_ofBitVec,
    BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end AesGcm.Proofs.Machine.Fixslice
