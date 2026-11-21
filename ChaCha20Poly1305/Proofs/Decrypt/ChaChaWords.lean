import Standards.RFC.ChaCha20Poly1305.ChaCha20

namespace ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound

open Standards.RFC.ChaCha20Poly1305

def quarter (a b c d : BitVec 32) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let a := a+b
  let d := (d ^^^ a).rotateLeft 16
  let c := c+d
  let b := (b ^^^ c).rotateLeft 12
  let a := a+b
  let d := (d ^^^ a).rotateLeft 8
  let c := c+d
  let b := (b ^^^ c).rotateLeft 7
  (a,b,c,d)

theorem quarter_eq (a b c d : UInt32) :
    let t := quarterRound a b c d
    (t.1.toBitVec, t.2.1.toBitVec, t.2.2.1.toBitVec, t.2.2.2.toBitVec) =
      quarter a.toBitVec b.toBitVec c.toBitVec d.toBitVec := by rfl

def doubleRound (w : Vector UInt32 16) : Vector UInt32 16 :=
  let col0 := quarterRound w[0] w[4] w[8] w[12]
  let col1 := quarterRound w[1] w[5] w[9] w[13]
  let col2 := quarterRound w[2] w[6] w[10] w[14]
  let col3 := quarterRound w[3] w[7] w[11] w[15]
  let diag0 := quarterRound col0.1 col1.2.1 col2.2.2.1 col3.2.2.2
  let diag1 := quarterRound col1.1 col2.2.1 col3.2.2.1 col0.2.2.2
  let diag2 := quarterRound col2.1 col3.2.1 col0.2.2.1 col1.2.2.2
  let diag3 := quarterRound col3.1 col0.2.1 col1.2.2.1 col2.2.2.2
  #v[diag0.1, diag1.1, diag2.1, diag3.1, diag3.2.1, diag0.2.1, diag1.2.1, diag2.2.1, diag2.2.2.1, diag3.2.2.1, diag0.2.2.1, diag1.2.2.1, diag1.2.2.2, diag2.2.2.2, diag3.2.2.2, diag0.2.2.2]

set_option maxRecDepth 12000

private theorem etaWords (w : Vector UInt32 16) : #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]] = w := by
  apply Vector.ext
  intro i hi
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

set_option maxHeartbeats 900000

private theorem substRound0 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    let v := quarterRound w0 w4 w8 w12
    qround #v[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] 0 4 8 12 =
      #v[v.1, w1, w2, w3, v.2.1, w5, w6, w7, v.2.2.1, w9, w10, w11, v.2.2.2, w13, w14, w15] := by rfl

private theorem substRound1 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    let v := quarterRound w1 w5 w9 w13
    qround #v[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] 1 5 9 13 =
      #v[w0, v.1, w2, w3, w4, v.2.1, w6, w7, w8, v.2.2.1, w10, w11, w12, v.2.2.2, w14, w15] := by rfl

private theorem substRound2 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    let v := quarterRound w2 w6 w10 w14
    qround #v[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] 2 6 10 14 =
      #v[w0, w1, v.1, w3, w4, w5, v.2.1, w7, w8, w9, v.2.2.1, w11, w12, w13, v.2.2.2, w15] := by rfl

private theorem substRound3 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    let v := quarterRound w3 w7 w11 w15
    qround #v[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] 3 7 11 15 =
      #v[w0, w1, w2, v.1, w4, w5, w6, v.2.1, w8, w9, w10, v.2.2.1, w12, w13, w14, v.2.2.2] := by rfl

private theorem substRound4 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    let v := quarterRound w0 w5 w10 w15
    qround #v[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] 0 5 10 15 =
      #v[v.1, w1, w2, w3, w4, v.2.1, w6, w7, w8, w9, v.2.2.1, w11, w12, w13, w14, v.2.2.2] := by rfl

private theorem substRound5 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    let v := quarterRound w1 w6 w11 w12
    qround #v[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] 1 6 11 12 =
      #v[w0, v.1, w2, w3, w4, w5, v.2.1, w7, w8, w9, w10, v.2.2.1, v.2.2.2, w13, w14, w15] := by rfl

private theorem substRound6 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    let v := quarterRound w2 w7 w8 w13
    qround #v[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] 2 7 8 13 =
      #v[w0, w1, v.1, w3, w4, w5, w6, v.2.1, v.2.2.1, w9, w10, w11, w12, v.2.2.2, w14, w15] := by rfl

private theorem substRound7 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    let v := quarterRound w3 w4 w9 w14
    qround #v[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] 3 4 9 14 =
      #v[w0, w1, w2, v.1, v.2.1, w5, w6, w7, w8, v.2.2.1, w10, w11, w12, w13, v.2.2.2, w15] := by rfl

theorem doubleRound_eq (w : Vector UInt32 16) : innerBlock w = doubleRound w := by
  rw [← etaWords w]
  simp only [innerBlock, doubleRound, substRound0, substRound1, substRound2, substRound3, substRound4, substRound5, substRound6, substRound7]
  rfl

end ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
