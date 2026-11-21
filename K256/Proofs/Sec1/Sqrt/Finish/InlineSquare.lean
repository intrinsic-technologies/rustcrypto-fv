import K256.Proofs.Common.Field.Square

namespace K256.Proofs.Sec1.Sqrt.Finish
open X86Proofs K256.Proofs.Common.Field

def inlineSquareStage0 (a : Limbs) : Vector Word 9 :=
  let x0 : Word := a[4] * a[1]
  let x1 : Word := a[3] * a[2]
  let x2 : Word := x0 + x1
  let x3 : Word := x2 + x2
  let x4 : Word := (mulResult a[4] a[0]).snd
  let x5 : Word := (mulResult a[3] a[1]).snd
  let x6 : Word := x4 + x5
  let x7 : Word := a[3] * a[1]
  let x8 : Word := a[4] * a[0]
  let x9 : Word := BitVec.ofNat 64 (addSpec x7 x8).snd.CF.toNat
  let x10 : Word := x6 + x9
  let x11 : Word := x7 + x8
  let x12 : Word := shldResult 1 x10 x11
  let x13 : Word := (mulResult a[2] a[2]).snd
  let x14 : Word := x12 + x13
  let x15 : Word := x11 + x11
  let x16 : Word := a[2] * a[2]
  let x17 : Word := BitVec.ofNat 64 (addSpec x15 x16).snd.CF.toNat
  let x18 : Word := x14 + x17
  let x19 : Word := (mulResult a[4] a[4]).snd
  let x20 : Word := a[4] * a[4]
  let x21 : Word := shldResult 12 x19 x20
  #v[x0, x1, x2, x3, x15, x16, x18, x20, x21]

def inlineSquareStage1 (a : Limbs) (s0 : Vector Word 9) : Vector Word 5 :=
  let x22 : Word := (mulResult s0[8] 68719492368).snd
  let x23 : Word := s0[6] + x22
  let x24 : Word := s0[4] + s0[5]
  let x25 : Word := s0[8] * 68719492368
  let x26 : Word := BitVec.ofNat 64 (addSpec x24 x25).snd.CF.toNat
  let x27 : Word := x23 + x26
  let x28 : Word := x27 + 0
  let x29 : Word := x24 + x25
  let x30 : Word := 4503599627370493 &&& s0[7]
  let x31 : Word := (mulResult x30 68719492368).snd
  let x32 : Word := (mulResult a[2] a[1]).snd
  let x33 : Word := (mulResult a[3] a[0]).snd
  let x34 : Word := x32 + x33
  let x35 : Word := a[2] * a[1]
  let x36 : Word := a[3] * a[0]
  let x37 : Word := BitVec.ofNat 64 (addSpec x35 x36).snd.CF.toNat
  let x38 : Word := x34 + x37
  let x39 : Word := x35 + x36
  let x40 : Word := shldResult 1 x38 x39
  let x41 : Word := x31 + x40
  let x42 : Word := x30 * 68719492368
  let x43 : Word := x39 + x39
  #v[x28, x29, x41, x42, x43]

def inlineSquareStage2 (a : Limbs) (s0 : Vector Word 9) (s1 : Vector Word 5) : Vector Word 13 :=
  let x44 : Word := BitVec.ofNat 64 (addSpec s1[3] s1[4]).snd.CF.toNat
  let x45 : Word := s1[2] + x44
  let x46 : Word := s1[3] + s1[4]
  let x47 : Word := shldResult 12 x45 x46
  let x48 : Word := BitVec.ofNat 64 (addSpec s1[1] x47).snd.CF.toNat
  let x49 : Word := s1[0] + x48
  let x50 : Word := s1[1] + x47
  let x51 : Word := shldResult 12 x49 x50
  let x52 : Word := s0[3] + x51
  let x53 : Word := x52 <<< 4
  let x54 : Word := x53 &&& 72057594037927920
  let x55 : Word := x50 >>> 48
  let x56 : Word := (((x55.setWidth 32) &&& 15).setWidth 64)
  let x57 : Word := x54 ||| x56
  let x58 : Word := x57 * 4294968273
  let x59 : Word := a[0] * a[0]
  let x60 : Word := x58 + x59
  let x61 : Word := x60 &&& 4503599627370495
  let x62 : Word := a[2] * a[4]
  let x63 : Word := x62 + x62
  let x64 : Word := a[3] * a[3]
  let x65 : Word := x63 + x64
  #v[x46, x50, x51, x52, x57, x58, x59, x60, x61, x62, x63, x64, x65]

def inlineSquareStage3 (a : Limbs) (s0 : Vector Word 9) (s2 : Vector Word 13) : Vector Word 8 :=
  let x66 : Word := (mulResult a[3] a[2]).snd
  let x67 : Word := (mulResult a[4] a[1]).snd
  let x68 : Word := x66 + x67
  let x69 : Word := BitVec.ofNat 64 (addSpec s0[0] s0[1]).snd.CF.toNat
  let x70 : Word := x68 + x69
  let x71 : Word := shldResult 1 x70 s0[2]
  let x72 : Word := x71 + 0
  let x73 : Word := BitVec.ofNat 64 (addSpec s0[3] s2[2]).snd.CF.toNat
  let x74 : Word := x72 + x73
  let x75 : Word := shldResult 12 x74 s2[3]
  let x76 : Word := s2[12] + x75
  let x77 : Word := x76 &&& 4503599627370495
  let x78 : Word := x77 * 68719492368
  let x79 : Word := a[0] + a[0]
  let x80 : Word := x79 * a[1]
  let x81 : Word := x78 + x80
  let x82 : Word := (mulResult s2[4] 4294968273).snd
  let x83 : Word := (mulResult a[0] a[0]).snd
  let x84 : Word := x82 + x83
  let x85 : Word := BitVec.ofNat 64 (addSpec s2[5] s2[6]).snd.CF.toNat
  let x86 : Word := x84 + x85
  let x87 : Word := shldResult 12 x86 s2[7]
  #v[x75, x76, x77, x78, x79, x80, x81, x87]

def inlineSquareStage4 (a : Limbs) (s2 : Vector Word 13) (s3 : Vector Word 8) : Vector Word 13 :=
  let x88 : Word := s3[6] + s3[7]
  let x89 : Word := x88 &&& 4503599627370495
  let x90 : Word := s3[4] * a[2]
  let x91 : Word := a[1] * a[1]
  let x92 : Word := x90 + x91
  let x93 : Word := a[3] * a[4]
  let x94 : Word := x93 + x93
  let x95 : Word := (mulResult a[3] a[3]).snd
  let x96 : Word := (mulResult a[2] a[4]).snd
  let x97 : Word := shldResult 1 x96 s2[9]
  let x98 : Word := x95 + x97
  let x99 : Word := BitVec.ofNat 64 (addSpec s2[10] s2[11]).snd.CF.toNat
  let x100 : Word := x98 + x99
  let x101 : Word := x100 + 0
  let x102 : Word := BitVec.ofNat 64 (addSpec s2[12] s3[0]).snd.CF.toNat
  let x103 : Word := x101 + x102
  let x104 : Word := shldResult 12 x103 s3[1]
  let x105 : Word := x94 + x104
  let x106 : Word := x105 &&& 4503599627370495
  let x107 : Word := x106 * 68719492368
  let x108 : Word := x92 + x107
  let x109 : Word := (mulResult s3[2] 68719492368).snd
  #v[x88, x89, x90, x91, x92, x93, x94, x104, x105, x106, x107, x108, x109]

def inlineSquareStage5 (a : Limbs) (s2 : Vector Word 13) (s3 : Vector Word 8) (s4 : Vector Word 13) : Vector Word 8 :=
  let x110 : Word := (mulResult s3[4] a[1]).snd
  let x111 : Word := a[0] >>> 63
  let x112 : Word := x111 * a[1]
  let x113 : Word := x110 + x112
  let x114 : Word := s4[12] + x113
  let x115 : Word := BitVec.ofNat 64 (addSpec s3[3] s3[5]).snd.CF.toNat
  let x116 : Word := x114 + x115
  let x117 : Word := x116 + 0
  let x118 : Word := BitVec.ofNat 64 (addSpec s3[6] s3[7]).snd.CF.toNat
  let x119 : Word := x117 + x118
  let x120 : Word := shldResult 12 x119 s4[0]
  let x121 : Word := s4[11] + x120
  let x122 : Word := x121 &&& 4503599627370495
  let x123 : Word := 4503599627370494 &&& s2[0]
  let x124 : Word := (mulResult a[3] a[4]).snd
  let x125 : Word := shldResult 1 x124 s4[5]
  let x126 : Word := x125 + 0
  let x127 : Word := BitVec.ofNat 64 (addSpec s4[6] s4[7]).snd.CF.toNat
  let x128 : Word := x126 + x127
  let x129 : Word := shldResult 12 x128 s4[8]
  let x130 : Word := x129 * 68719492368
  let x131 : Word := x123 + x130
  #v[x111, x120, x121, x122, x123, x129, x130, x131]

def inlineSquareStage6 (a : Limbs) (s2 : Vector Word 13) (s3 : Vector Word 8) (s4 : Vector Word 13) (s5 : Vector Word 8) : Vector Word 5 :=
  let x132 : Word := (mulResult s3[4] a[2]).snd
  let x133 : Word := s5[0] * a[2]
  let x134 : Word := x132 + x133
  let x135 : Word := (mulResult a[1] a[1]).snd
  let x136 : Word := x134 + x135
  let x137 : Word := BitVec.ofNat 64 (addSpec s4[2] s4[3]).snd.CF.toNat
  let x138 : Word := x136 + x137
  let x139 : Word := (mulResult s4[9] 68719492368).snd
  let x140 : Word := x138 + x139
  let x141 : Word := BitVec.ofNat 64 (addSpec s4[4] s4[10]).snd.CF.toNat
  let x142 : Word := x140 + x141
  let x143 : Word := x142 + 0
  let x144 : Word := BitVec.ofNat 64 (addSpec s4[11] s5[1]).snd.CF.toNat
  let x145 : Word := x143 + x144
  let x146 : Word := shldResult 12 x145 s5[2]
  let x147 : Word := s5[7] + x146
  let x148 : Word := x147 &&& 4503599627370495
  let x149 : Word := s2[1] &&& 281474976710655
  let x150 : Word := (mulResult s5[5] 68719492368).snd
  let x151 : Word := x150 + 0
  let x152 : Word := BitVec.ofNat 64 (addSpec s5[4] s5[6]).snd.CF.toNat
  let x153 : Word := x151 + x152
  #v[x146, x147, x148, x149, x153]

def inlineSquareStage7 (_a : Limbs) (s5 : Vector Word 8) (s6 : Vector Word 5) : Vector Word 1 :=
  let x154 : Word := s6[4] + 0
  let x155 : Word := BitVec.ofNat 64 (addSpec s5[7] s6[0]).snd.CF.toNat
  let x156 : Word := x154 + x155
  let x157 : Word := shldResult 12 x156 s6[1]
  let x158 : Word := s6[3] + x157
  #v[x158]

def inlineSquareWords (a : Limbs) : Limbs :=
  let s0 := inlineSquareStage0 a
  let s1 := inlineSquareStage1 a s0
  let s2 := inlineSquareStage2 a s0 s1
  let s3 := inlineSquareStage3 a s0 s2
  let s4 := inlineSquareStage4 a s2 s3
  let s5 := inlineSquareStage5 a s2 s3 s4
  let s6 := inlineSquareStage6 a s2 s3 s4 s5
  let s7 := inlineSquareStage7 a s5 s6
  #v[s2[8], s4[1], s5[3], s6[2], s7[0]]

private def w0 (a : Limbs) : Word := a[4] * a[1]
private def w1 (a : Limbs) : Word := a[3] * a[2]
private def w2 (a : Limbs) : Word := (w0 a) + (w1 a)
private def w3 (a : Limbs) : Word := (w2 a) + (w2 a)
private def w4 (a : Limbs) : Word := (mulResult a[4] a[0]).snd
private def w5 (a : Limbs) : Word := (mulResult a[3] a[1]).snd
private def w6 (a : Limbs) : Word := (w4 a) + (w5 a)
private def w7 (a : Limbs) : Word := a[3] * a[1]
private def w8 (a : Limbs) : Word := a[4] * a[0]
private def w9 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w7 a) (w8 a)).snd.CF.toNat
private def w10 (a : Limbs) : Word := (w6 a) + (w9 a)
private def w11 (a : Limbs) : Word := (w7 a) + (w8 a)
private def w12 (a : Limbs) : Word := shldResult 1 (w10 a) (w11 a)
private def w13 (a : Limbs) : Word := (mulResult a[2] a[2]).snd
private def w14 (a : Limbs) : Word := (w12 a) + (w13 a)
private def w15 (a : Limbs) : Word := (w11 a) + (w11 a)
private def w16 (a : Limbs) : Word := a[2] * a[2]
private def w17 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w15 a) (w16 a)).snd.CF.toNat
private def w18 (a : Limbs) : Word := (w14 a) + (w17 a)
private def w19 (a : Limbs) : Word := (mulResult a[4] a[4]).snd
private def w20 (a : Limbs) : Word := a[4] * a[4]
private def w21 (a : Limbs) : Word := shldResult 12 (w19 a) (w20 a)
private def w22 (a : Limbs) : Word := (mulResult (w21 a) 68719492368).snd
private def w23 (a : Limbs) : Word := (w18 a) + (w22 a)
private def w24 (a : Limbs) : Word := (w15 a) + (w16 a)
private def w25 (a : Limbs) : Word := (w21 a) * 68719492368
private def w26 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w24 a) (w25 a)).snd.CF.toNat
private def w27 (a : Limbs) : Word := (w23 a) + (w26 a)
private def w28 (a : Limbs) : Word := (w27 a) + 0
private def w29 (a : Limbs) : Word := (w24 a) + (w25 a)
private def w30 (a : Limbs) : Word := 4503599627370493 &&& (w20 a)
private def w31 (a : Limbs) : Word := (mulResult (w30 a) 68719492368).snd
private def w32 (a : Limbs) : Word := (mulResult a[2] a[1]).snd
private def w33 (a : Limbs) : Word := (mulResult a[3] a[0]).snd
private def w34 (a : Limbs) : Word := (w32 a) + (w33 a)
private def w35 (a : Limbs) : Word := a[2] * a[1]
private def w36 (a : Limbs) : Word := a[3] * a[0]
private def w37 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w35 a) (w36 a)).snd.CF.toNat
private def w38 (a : Limbs) : Word := (w34 a) + (w37 a)
private def w39 (a : Limbs) : Word := (w35 a) + (w36 a)
private def w40 (a : Limbs) : Word := shldResult 1 (w38 a) (w39 a)
private def w41 (a : Limbs) : Word := (w31 a) + (w40 a)
private def w42 (a : Limbs) : Word := (w30 a) * 68719492368
private def w43 (a : Limbs) : Word := (w39 a) + (w39 a)
private def w44 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w42 a) (w43 a)).snd.CF.toNat
private def w45 (a : Limbs) : Word := (w41 a) + (w44 a)
private def w46 (a : Limbs) : Word := (w42 a) + (w43 a)
private def w47 (a : Limbs) : Word := shldResult 12 (w45 a) (w46 a)
private def w48 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w29 a) (w47 a)).snd.CF.toNat
private def w49 (a : Limbs) : Word := (w28 a) + (w48 a)
private def w50 (a : Limbs) : Word := (w29 a) + (w47 a)
private def w51 (a : Limbs) : Word := shldResult 12 (w49 a) (w50 a)
private def w52 (a : Limbs) : Word := (w3 a) + (w51 a)
private def w53 (a : Limbs) : Word := (w52 a) <<< 4
private def w54 (a : Limbs) : Word := (w53 a) &&& 72057594037927920
private def w55 (a : Limbs) : Word := (w50 a) >>> 48
private def w56 (a : Limbs) : Word := ((((w55 a).setWidth 32) &&& 15).setWidth 64)
private def w57 (a : Limbs) : Word := (w54 a) ||| (w56 a)
private def w58 (a : Limbs) : Word := (w57 a) * 4294968273
private def w59 (a : Limbs) : Word := a[0] * a[0]
private def w60 (a : Limbs) : Word := (w58 a) + (w59 a)
private def w61 (a : Limbs) : Word := (w60 a) &&& 4503599627370495
private def w62 (a : Limbs) : Word := a[2] * a[4]
private def w63 (a : Limbs) : Word := (w62 a) + (w62 a)
private def w64 (a : Limbs) : Word := a[3] * a[3]
private def w65 (a : Limbs) : Word := (w63 a) + (w64 a)
private def w66 (a : Limbs) : Word := (mulResult a[3] a[2]).snd
private def w67 (a : Limbs) : Word := (mulResult a[4] a[1]).snd
private def w68 (a : Limbs) : Word := (w66 a) + (w67 a)
private def w69 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w0 a) (w1 a)).snd.CF.toNat
private def w70 (a : Limbs) : Word := (w68 a) + (w69 a)
private def w71 (a : Limbs) : Word := shldResult 1 (w70 a) (w2 a)
private def w72 (a : Limbs) : Word := (w71 a) + 0
private def w73 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w3 a) (w51 a)).snd.CF.toNat
private def w74 (a : Limbs) : Word := (w72 a) + (w73 a)
private def w75 (a : Limbs) : Word := shldResult 12 (w74 a) (w52 a)
private def w76 (a : Limbs) : Word := (w65 a) + (w75 a)
private def w77 (a : Limbs) : Word := (w76 a) &&& 4503599627370495
private def w78 (a : Limbs) : Word := (w77 a) * 68719492368
private def w79 (a : Limbs) : Word := a[0] + a[0]
private def w80 (a : Limbs) : Word := (w79 a) * a[1]
private def w81 (a : Limbs) : Word := (w78 a) + (w80 a)
private def w82 (a : Limbs) : Word := (mulResult (w57 a) 4294968273).snd
private def w83 (a : Limbs) : Word := (mulResult a[0] a[0]).snd
private def w84 (a : Limbs) : Word := (w82 a) + (w83 a)
private def w85 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w58 a) (w59 a)).snd.CF.toNat
private def w86 (a : Limbs) : Word := (w84 a) + (w85 a)
private def w87 (a : Limbs) : Word := shldResult 12 (w86 a) (w60 a)
private def w88 (a : Limbs) : Word := (w81 a) + (w87 a)
private def w89 (a : Limbs) : Word := (w88 a) &&& 4503599627370495
private def w90 (a : Limbs) : Word := (w79 a) * a[2]
private def w91 (a : Limbs) : Word := a[1] * a[1]
private def w92 (a : Limbs) : Word := (w90 a) + (w91 a)
private def w93 (a : Limbs) : Word := a[3] * a[4]
private def w94 (a : Limbs) : Word := (w93 a) + (w93 a)
private def w95 (a : Limbs) : Word := (mulResult a[3] a[3]).snd
private def w96 (a : Limbs) : Word := (mulResult a[2] a[4]).snd
private def w97 (a : Limbs) : Word := shldResult 1 (w96 a) (w62 a)
private def w98 (a : Limbs) : Word := (w95 a) + (w97 a)
private def w99 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w63 a) (w64 a)).snd.CF.toNat
private def w100 (a : Limbs) : Word := (w98 a) + (w99 a)
private def w101 (a : Limbs) : Word := (w100 a) + 0
private def w102 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w65 a) (w75 a)).snd.CF.toNat
private def w103 (a : Limbs) : Word := (w101 a) + (w102 a)
private def w104 (a : Limbs) : Word := shldResult 12 (w103 a) (w76 a)
private def w105 (a : Limbs) : Word := (w94 a) + (w104 a)
private def w106 (a : Limbs) : Word := (w105 a) &&& 4503599627370495
private def w107 (a : Limbs) : Word := (w106 a) * 68719492368
private def w108 (a : Limbs) : Word := (w92 a) + (w107 a)
private def w109 (a : Limbs) : Word := (mulResult (w77 a) 68719492368).snd
private def w110 (a : Limbs) : Word := (mulResult (w79 a) a[1]).snd
private def w111 (a : Limbs) : Word := a[0] >>> 63
private def w112 (a : Limbs) : Word := (w111 a) * a[1]
private def w113 (a : Limbs) : Word := (w110 a) + (w112 a)
private def w114 (a : Limbs) : Word := (w109 a) + (w113 a)
private def w115 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w78 a) (w80 a)).snd.CF.toNat
private def w116 (a : Limbs) : Word := (w114 a) + (w115 a)
private def w117 (a : Limbs) : Word := (w116 a) + 0
private def w118 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w81 a) (w87 a)).snd.CF.toNat
private def w119 (a : Limbs) : Word := (w117 a) + (w118 a)
private def w120 (a : Limbs) : Word := shldResult 12 (w119 a) (w88 a)
private def w121 (a : Limbs) : Word := (w108 a) + (w120 a)
private def w122 (a : Limbs) : Word := (w121 a) &&& 4503599627370495
private def w123 (a : Limbs) : Word := 4503599627370494 &&& (w46 a)
private def w124 (a : Limbs) : Word := (mulResult a[3] a[4]).snd
private def w125 (a : Limbs) : Word := shldResult 1 (w124 a) (w93 a)
private def w126 (a : Limbs) : Word := (w125 a) + 0
private def w127 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w94 a) (w104 a)).snd.CF.toNat
private def w128 (a : Limbs) : Word := (w126 a) + (w127 a)
private def w129 (a : Limbs) : Word := shldResult 12 (w128 a) (w105 a)
private def w130 (a : Limbs) : Word := (w129 a) * 68719492368
private def w131 (a : Limbs) : Word := (w123 a) + (w130 a)
private def w132 (a : Limbs) : Word := (mulResult (w79 a) a[2]).snd
private def w133 (a : Limbs) : Word := (w111 a) * a[2]
private def w134 (a : Limbs) : Word := (w132 a) + (w133 a)
private def w135 (a : Limbs) : Word := (mulResult a[1] a[1]).snd
private def w136 (a : Limbs) : Word := (w134 a) + (w135 a)
private def w137 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w90 a) (w91 a)).snd.CF.toNat
private def w138 (a : Limbs) : Word := (w136 a) + (w137 a)
private def w139 (a : Limbs) : Word := (mulResult (w106 a) 68719492368).snd
private def w140 (a : Limbs) : Word := (w138 a) + (w139 a)
private def w141 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w92 a) (w107 a)).snd.CF.toNat
private def w142 (a : Limbs) : Word := (w140 a) + (w141 a)
private def w143 (a : Limbs) : Word := (w142 a) + 0
private def w144 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w108 a) (w120 a)).snd.CF.toNat
private def w145 (a : Limbs) : Word := (w143 a) + (w144 a)
private def w146 (a : Limbs) : Word := shldResult 12 (w145 a) (w121 a)
private def w147 (a : Limbs) : Word := (w131 a) + (w146 a)
private def w148 (a : Limbs) : Word := (w147 a) &&& 4503599627370495
private def w149 (a : Limbs) : Word := (w50 a) &&& 281474976710655
private def w150 (a : Limbs) : Word := (mulResult (w129 a) 68719492368).snd
private def w151 (a : Limbs) : Word := (w150 a) + 0
private def w152 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w123 a) (w130 a)).snd.CF.toNat
private def w153 (a : Limbs) : Word := (w151 a) + (w152 a)
private def w154 (a : Limbs) : Word := (w153 a) + 0
private def w155 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w131 a) (w146 a)).snd.CF.toNat
private def w156 (a : Limbs) : Word := (w154 a) + (w155 a)
private def w157 (a : Limbs) : Word := shldResult 12 (w156 a) (w147 a)
private def w158 (a : Limbs) : Word := (w149 a) + (w157 a)

private theorem stage0_words (a : Limbs) : inlineSquareStage0 a  = #v[(w0 a), (w1 a), (w2 a), (w3 a), (w15 a), (w16 a), (w18 a), (w20 a), (w21 a)] := by
  rfl

private theorem stage1_words (a : Limbs) : inlineSquareStage1 a (#v[(w0 a), (w1 a), (w2 a), (w3 a), (w15 a), (w16 a), (w18 a), (w20 a), (w21 a)]) = #v[(w28 a), (w29 a), (w41 a), (w42 a), (w43 a)] := by
  rfl

private theorem stage2_words (a : Limbs) : inlineSquareStage2 a (#v[(w0 a), (w1 a), (w2 a), (w3 a), (w15 a), (w16 a), (w18 a), (w20 a), (w21 a)]) (#v[(w28 a), (w29 a), (w41 a), (w42 a), (w43 a)]) = #v[(w46 a), (w50 a), (w51 a), (w52 a), (w57 a), (w58 a), (w59 a), (w60 a), (w61 a), (w62 a), (w63 a), (w64 a), (w65 a)] := by
  rfl

private theorem stage3_words (a : Limbs) : inlineSquareStage3 a (#v[(w0 a), (w1 a), (w2 a), (w3 a), (w15 a), (w16 a), (w18 a), (w20 a), (w21 a)]) (#v[(w46 a), (w50 a), (w51 a), (w52 a), (w57 a), (w58 a), (w59 a), (w60 a), (w61 a), (w62 a), (w63 a), (w64 a), (w65 a)]) = #v[(w75 a), (w76 a), (w77 a), (w78 a), (w79 a), (w80 a), (w81 a), (w87 a)] := by
  rfl

private theorem stage4_words (a : Limbs) : inlineSquareStage4 a (#v[(w46 a), (w50 a), (w51 a), (w52 a), (w57 a), (w58 a), (w59 a), (w60 a), (w61 a), (w62 a), (w63 a), (w64 a), (w65 a)]) (#v[(w75 a), (w76 a), (w77 a), (w78 a), (w79 a), (w80 a), (w81 a), (w87 a)]) = #v[(w88 a), (w89 a), (w90 a), (w91 a), (w92 a), (w93 a), (w94 a), (w104 a), (w105 a), (w106 a), (w107 a), (w108 a), (w109 a)] := by
  rfl

private theorem stage5_words (a : Limbs) : inlineSquareStage5 a (#v[(w46 a), (w50 a), (w51 a), (w52 a), (w57 a), (w58 a), (w59 a), (w60 a), (w61 a), (w62 a), (w63 a), (w64 a), (w65 a)]) (#v[(w75 a), (w76 a), (w77 a), (w78 a), (w79 a), (w80 a), (w81 a), (w87 a)]) (#v[(w88 a), (w89 a), (w90 a), (w91 a), (w92 a), (w93 a), (w94 a), (w104 a), (w105 a), (w106 a), (w107 a), (w108 a), (w109 a)]) = #v[(w111 a), (w120 a), (w121 a), (w122 a), (w123 a), (w129 a), (w130 a), (w131 a)] := by
  rfl

private theorem stage6_words (a : Limbs) : inlineSquareStage6 a (#v[(w46 a), (w50 a), (w51 a), (w52 a), (w57 a), (w58 a), (w59 a), (w60 a), (w61 a), (w62 a), (w63 a), (w64 a), (w65 a)]) (#v[(w75 a), (w76 a), (w77 a), (w78 a), (w79 a), (w80 a), (w81 a), (w87 a)]) (#v[(w88 a), (w89 a), (w90 a), (w91 a), (w92 a), (w93 a), (w94 a), (w104 a), (w105 a), (w106 a), (w107 a), (w108 a), (w109 a)]) (#v[(w111 a), (w120 a), (w121 a), (w122 a), (w123 a), (w129 a), (w130 a), (w131 a)]) = #v[(w146 a), (w147 a), (w148 a), (w149 a), (w153 a)] := by
  rfl

private theorem stage7_words (a : Limbs) : inlineSquareStage7 a (#v[(w111 a), (w120 a), (w121 a), (w122 a), (w123 a), (w129 a), (w130 a), (w131 a)]) (#v[(w146 a), (w147 a), (w148 a), (w149 a), (w153 a)]) = #v[(w158 a)] := by
  rfl

private theorem inline_result (a : Limbs) : inlineSquareWords a = #v[(w61 a), (w89 a), (w122 a), (w148 a), (w158 a)] := by
  simp only [inlineSquareWords, stage0_words, stage1_words, stage2_words, stage3_words, stage4_words, stage5_words, stage6_words, stage7_words]
  rfl
private def w159 (a : Limbs) : Word := (w27 a) + (w48 a)
private def w160 (a : Limbs) : Word := shldResult 12 (w159 a) (w50 a)
private def w161 (a : Limbs) : Word := (w3 a) + (w160 a)
private def w162 (a : Limbs) : Word := (w161 a) <<< 4
private def w163 (a : Limbs) : Word := (w162 a) &&& 72057594037927920
private def w164 (a : Limbs) : Word := (w163 a) ||| (w56 a)
private def w165 (a : Limbs) : Word := (w164 a) * 4294968273
private def w166 (a : Limbs) : Word := (w165 a) + (w59 a)
private def w167 (a : Limbs) : Word := (w166 a) &&& 4503599627370495
private def w168 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w3 a) (w160 a)).snd.CF.toNat
private def w169 (a : Limbs) : Word := (w71 a) + (w168 a)
private def w170 (a : Limbs) : Word := shldResult 12 (w169 a) (w161 a)
private def w171 (a : Limbs) : Word := (w65 a) + (w170 a)
private def w172 (a : Limbs) : Word := (w171 a) &&& 4503599627370495
private def w173 (a : Limbs) : Word := (w172 a) * 68719492368
private def w174 (a : Limbs) : Word := (w173 a) + (w80 a)
private def w175 (a : Limbs) : Word := (mulResult (w164 a) 4294968273).snd
private def w176 (a : Limbs) : Word := (w175 a) + (w83 a)
private def w177 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w165 a) (w59 a)).snd.CF.toNat
private def w178 (a : Limbs) : Word := (w176 a) + (w177 a)
private def w179 (a : Limbs) : Word := shldResult 12 (w178 a) (w166 a)
private def w180 (a : Limbs) : Word := (w174 a) + (w179 a)
private def w181 (a : Limbs) : Word := (w180 a) &&& 4503599627370495
private def w182 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w65 a) (w170 a)).snd.CF.toNat
private def w183 (a : Limbs) : Word := (w100 a) + (w182 a)
private def w184 (a : Limbs) : Word := shldResult 12 (w183 a) (w171 a)
private def w185 (a : Limbs) : Word := (w94 a) + (w184 a)
private def w186 (a : Limbs) : Word := (w185 a) &&& 4503599627370495
private def w187 (a : Limbs) : Word := (w186 a) * 68719492368
private def w188 (a : Limbs) : Word := (w92 a) + (w187 a)
private def w189 (a : Limbs) : Word := (mulResult (w172 a) 68719492368).snd
private def w190 (a : Limbs) : Word := (w189 a) + (w113 a)
private def w191 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w173 a) (w80 a)).snd.CF.toNat
private def w192 (a : Limbs) : Word := (w190 a) + (w191 a)
private def w193 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w174 a) (w179 a)).snd.CF.toNat
private def w194 (a : Limbs) : Word := (w192 a) + (w193 a)
private def w195 (a : Limbs) : Word := shldResult 12 (w194 a) (w180 a)
private def w196 (a : Limbs) : Word := (w188 a) + (w195 a)
private def w197 (a : Limbs) : Word := (w196 a) &&& 4503599627370495
private def w198 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w94 a) (w184 a)).snd.CF.toNat
private def w199 (a : Limbs) : Word := (w125 a) + (w198 a)
private def w200 (a : Limbs) : Word := shldResult 12 (w199 a) (w185 a)
private def w201 (a : Limbs) : Word := (w200 a) * 68719492368
private def w202 (a : Limbs) : Word := (w123 a) + (w201 a)
private def w203 (a : Limbs) : Word := (mulResult (w186 a) 68719492368).snd
private def w204 (a : Limbs) : Word := (w138 a) + (w203 a)
private def w205 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w92 a) (w187 a)).snd.CF.toNat
private def w206 (a : Limbs) : Word := (w204 a) + (w205 a)
private def w207 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w188 a) (w195 a)).snd.CF.toNat
private def w208 (a : Limbs) : Word := (w206 a) + (w207 a)
private def w209 (a : Limbs) : Word := shldResult 12 (w208 a) (w196 a)
private def w210 (a : Limbs) : Word := (w202 a) + (w209 a)
private def w211 (a : Limbs) : Word := 4503599627370495 &&& (w210 a)
private def w212 (a : Limbs) : Word := 281474976710655 &&& (w50 a)
private def w213 (a : Limbs) : Word := (mulResult (w200 a) 68719492368).snd
private def w214 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w123 a) (w201 a)).snd.CF.toNat
private def w215 (a : Limbs) : Word := (w213 a) + (w214 a)
private def w216 (a : Limbs) : Word := BitVec.ofNat 64 (addSpec (w202 a) (w209 a)).snd.CF.toNat
private def w217 (a : Limbs) : Word := (w215 a) + (w216 a)
private def w218 (a : Limbs) : Word := shldResult 12 (w217 a) (w210 a)
private def w219 (a : Limbs) : Word := (w212 a) + (w218 a)

private theorem wordCongr {α : Type} (f : Word → Word → α) {a b c d : Word}
    (hab : a = b) (hcd : c = d) : f a c = f b d := by subst_vars; rfl

private theorem eq28_27 (a : Limbs) : (w28 a) = (w27 a) :=
  (BitVec.add_zero (w27 a)).trans (rfl : ((w27 a) : Word) = (w27 a))

private theorem eq49_159 (a : Limbs) : (w49 a) = (w159 a) :=
  wordCongr (fun x y : Word => x + y) (eq28_27 a) (rfl : ((w48 a) : Word) = (w48 a))

private theorem eq51_160 (a : Limbs) : (w51 a) = (w160 a) :=
  wordCongr (shldResult 12) (eq49_159 a) (rfl : ((w50 a) : Word) = (w50 a))

private theorem eq52_161 (a : Limbs) : (w52 a) = (w161 a) :=
  wordCongr (fun x y : Word => x + y) (rfl : ((w3 a) : Word) = (w3 a)) (eq51_160 a)

private theorem eq53_162 (a : Limbs) : (w53 a) = (w162 a) :=
  congrArg (fun x : Word => x <<< 4) (eq52_161 a)

private theorem eq54_163 (a : Limbs) : (w54 a) = (w163 a) :=
  wordCongr (fun x y : Word => x &&& y) (eq53_162 a) (rfl : (72057594037927920 : Word) = 72057594037927920)

private theorem eq57_164 (a : Limbs) : (w57 a) = (w164 a) :=
  wordCongr (fun x y : Word => x ||| y) (eq54_163 a) (rfl : ((w56 a) : Word) = (w56 a))

private theorem eq58_165 (a : Limbs) : (w58 a) = (w165 a) :=
  wordCongr (fun x y : Word => x * y) (eq57_164 a) (rfl : (4294968273 : Word) = 4294968273)

private theorem eq60_166 (a : Limbs) : (w60 a) = (w166 a) :=
  wordCongr (fun x y : Word => x + y) (eq58_165 a) (rfl : ((w59 a) : Word) = (w59 a))

private theorem eq61_167 (a : Limbs) : (w61 a) = (w167 a) :=
  wordCongr (fun x y : Word => x &&& y) (eq60_166 a) (rfl : (4503599627370495 : Word) = 4503599627370495)

private theorem eq72_71 (a : Limbs) : (w72 a) = (w71 a) :=
  (BitVec.add_zero (w71 a)).trans (rfl : ((w71 a) : Word) = (w71 a))

private theorem eq73_168 (a : Limbs) : (w73 a) = (w168 a) :=
  wordCongr (fun x y : Word => BitVec.ofNat 64 (addSpec x y).2.CF.toNat) (rfl : ((w3 a) : Word) = (w3 a)) (eq51_160 a)

private theorem eq74_169 (a : Limbs) : (w74 a) = (w169 a) :=
  wordCongr (fun x y : Word => x + y) (eq72_71 a) (eq73_168 a)

private theorem eq75_170 (a : Limbs) : (w75 a) = (w170 a) :=
  wordCongr (shldResult 12) (eq74_169 a) (eq52_161 a)

private theorem eq76_171 (a : Limbs) : (w76 a) = (w171 a) :=
  wordCongr (fun x y : Word => x + y) (rfl : ((w65 a) : Word) = (w65 a)) (eq75_170 a)

private theorem eq77_172 (a : Limbs) : (w77 a) = (w172 a) :=
  wordCongr (fun x y : Word => x &&& y) (eq76_171 a) (rfl : (4503599627370495 : Word) = 4503599627370495)

private theorem eq78_173 (a : Limbs) : (w78 a) = (w173 a) :=
  wordCongr (fun x y : Word => x * y) (eq77_172 a) (rfl : (68719492368 : Word) = 68719492368)

private theorem eq81_174 (a : Limbs) : (w81 a) = (w174 a) :=
  wordCongr (fun x y : Word => x + y) (eq78_173 a) (rfl : ((w80 a) : Word) = (w80 a))

private theorem eq82_175 (a : Limbs) : (w82 a) = (w175 a) :=
  wordCongr (fun x y : Word => (mulResult x y).2) (eq57_164 a) (rfl : (4294968273 : Word) = 4294968273)

private theorem eq84_176 (a : Limbs) : (w84 a) = (w176 a) :=
  wordCongr (fun x y : Word => x + y) (eq82_175 a) (rfl : ((w83 a) : Word) = (w83 a))

private theorem eq85_177 (a : Limbs) : (w85 a) = (w177 a) :=
  wordCongr (fun x y : Word => BitVec.ofNat 64 (addSpec x y).2.CF.toNat) (eq58_165 a) (rfl : ((w59 a) : Word) = (w59 a))

private theorem eq86_178 (a : Limbs) : (w86 a) = (w178 a) :=
  wordCongr (fun x y : Word => x + y) (eq84_176 a) (eq85_177 a)

private theorem eq87_179 (a : Limbs) : (w87 a) = (w179 a) :=
  wordCongr (shldResult 12) (eq86_178 a) (eq60_166 a)

private theorem eq88_180 (a : Limbs) : (w88 a) = (w180 a) :=
  wordCongr (fun x y : Word => x + y) (eq81_174 a) (eq87_179 a)

private theorem eq89_181 (a : Limbs) : (w89 a) = (w181 a) :=
  wordCongr (fun x y : Word => x &&& y) (eq88_180 a) (rfl : (4503599627370495 : Word) = 4503599627370495)

private theorem eq101_100 (a : Limbs) : (w101 a) = (w100 a) :=
  (BitVec.add_zero (w100 a)).trans (rfl : ((w100 a) : Word) = (w100 a))

private theorem eq102_182 (a : Limbs) : (w102 a) = (w182 a) :=
  wordCongr (fun x y : Word => BitVec.ofNat 64 (addSpec x y).2.CF.toNat) (rfl : ((w65 a) : Word) = (w65 a)) (eq75_170 a)

private theorem eq103_183 (a : Limbs) : (w103 a) = (w183 a) :=
  wordCongr (fun x y : Word => x + y) (eq101_100 a) (eq102_182 a)

private theorem eq104_184 (a : Limbs) : (w104 a) = (w184 a) :=
  wordCongr (shldResult 12) (eq103_183 a) (eq76_171 a)

private theorem eq105_185 (a : Limbs) : (w105 a) = (w185 a) :=
  wordCongr (fun x y : Word => x + y) (rfl : ((w94 a) : Word) = (w94 a)) (eq104_184 a)

private theorem eq106_186 (a : Limbs) : (w106 a) = (w186 a) :=
  wordCongr (fun x y : Word => x &&& y) (eq105_185 a) (rfl : (4503599627370495 : Word) = 4503599627370495)

private theorem eq107_187 (a : Limbs) : (w107 a) = (w187 a) :=
  wordCongr (fun x y : Word => x * y) (eq106_186 a) (rfl : (68719492368 : Word) = 68719492368)

private theorem eq108_188 (a : Limbs) : (w108 a) = (w188 a) :=
  wordCongr (fun x y : Word => x + y) (rfl : ((w92 a) : Word) = (w92 a)) (eq107_187 a)

private theorem eq109_189 (a : Limbs) : (w109 a) = (w189 a) :=
  wordCongr (fun x y : Word => (mulResult x y).2) (eq77_172 a) (rfl : (68719492368 : Word) = 68719492368)

private theorem eq114_190 (a : Limbs) : (w114 a) = (w190 a) :=
  wordCongr (fun x y : Word => x + y) (eq109_189 a) (rfl : ((w113 a) : Word) = (w113 a))

private theorem eq115_191 (a : Limbs) : (w115 a) = (w191 a) :=
  wordCongr (fun x y : Word => BitVec.ofNat 64 (addSpec x y).2.CF.toNat) (eq78_173 a) (rfl : ((w80 a) : Word) = (w80 a))

private theorem eq116_192 (a : Limbs) : (w116 a) = (w192 a) :=
  wordCongr (fun x y : Word => x + y) (eq114_190 a) (eq115_191 a)

private theorem eq117_192 (a : Limbs) : (w117 a) = (w192 a) :=
  (BitVec.add_zero (w116 a)).trans (eq116_192 a)

private theorem eq118_193 (a : Limbs) : (w118 a) = (w193 a) :=
  wordCongr (fun x y : Word => BitVec.ofNat 64 (addSpec x y).2.CF.toNat) (eq81_174 a) (eq87_179 a)

private theorem eq119_194 (a : Limbs) : (w119 a) = (w194 a) :=
  wordCongr (fun x y : Word => x + y) (eq117_192 a) (eq118_193 a)

private theorem eq120_195 (a : Limbs) : (w120 a) = (w195 a) :=
  wordCongr (shldResult 12) (eq119_194 a) (eq88_180 a)

private theorem eq121_196 (a : Limbs) : (w121 a) = (w196 a) :=
  wordCongr (fun x y : Word => x + y) (eq108_188 a) (eq120_195 a)

private theorem eq122_197 (a : Limbs) : (w122 a) = (w197 a) :=
  wordCongr (fun x y : Word => x &&& y) (eq121_196 a) (rfl : (4503599627370495 : Word) = 4503599627370495)

private theorem eq126_125 (a : Limbs) : (w126 a) = (w125 a) :=
  (BitVec.add_zero (w125 a)).trans (rfl : ((w125 a) : Word) = (w125 a))

private theorem eq127_198 (a : Limbs) : (w127 a) = (w198 a) :=
  wordCongr (fun x y : Word => BitVec.ofNat 64 (addSpec x y).2.CF.toNat) (rfl : ((w94 a) : Word) = (w94 a)) (eq104_184 a)

private theorem eq128_199 (a : Limbs) : (w128 a) = (w199 a) :=
  wordCongr (fun x y : Word => x + y) (eq126_125 a) (eq127_198 a)

private theorem eq129_200 (a : Limbs) : (w129 a) = (w200 a) :=
  wordCongr (shldResult 12) (eq128_199 a) (eq105_185 a)

private theorem eq130_201 (a : Limbs) : (w130 a) = (w201 a) :=
  wordCongr (fun x y : Word => x * y) (eq129_200 a) (rfl : (68719492368 : Word) = 68719492368)

private theorem eq131_202 (a : Limbs) : (w131 a) = (w202 a) :=
  wordCongr (fun x y : Word => x + y) (rfl : ((w123 a) : Word) = (w123 a)) (eq130_201 a)

private theorem eq139_203 (a : Limbs) : (w139 a) = (w203 a) :=
  wordCongr (fun x y : Word => (mulResult x y).2) (eq106_186 a) (rfl : (68719492368 : Word) = 68719492368)

private theorem eq140_204 (a : Limbs) : (w140 a) = (w204 a) :=
  wordCongr (fun x y : Word => x + y) (rfl : ((w138 a) : Word) = (w138 a)) (eq139_203 a)

private theorem eq141_205 (a : Limbs) : (w141 a) = (w205 a) :=
  wordCongr (fun x y : Word => BitVec.ofNat 64 (addSpec x y).2.CF.toNat) (rfl : ((w92 a) : Word) = (w92 a)) (eq107_187 a)

private theorem eq142_206 (a : Limbs) : (w142 a) = (w206 a) :=
  wordCongr (fun x y : Word => x + y) (eq140_204 a) (eq141_205 a)

private theorem eq143_206 (a : Limbs) : (w143 a) = (w206 a) :=
  (BitVec.add_zero (w142 a)).trans (eq142_206 a)

private theorem eq144_207 (a : Limbs) : (w144 a) = (w207 a) :=
  wordCongr (fun x y : Word => BitVec.ofNat 64 (addSpec x y).2.CF.toNat) (eq108_188 a) (eq120_195 a)

private theorem eq145_208 (a : Limbs) : (w145 a) = (w208 a) :=
  wordCongr (fun x y : Word => x + y) (eq143_206 a) (eq144_207 a)

private theorem eq146_209 (a : Limbs) : (w146 a) = (w209 a) :=
  wordCongr (shldResult 12) (eq145_208 a) (eq121_196 a)

private theorem eq147_210 (a : Limbs) : (w147 a) = (w210 a) :=
  wordCongr (fun x y : Word => x + y) (eq131_202 a) (eq146_209 a)

private theorem eq148_211 (a : Limbs) : (w148 a) = (w211 a) :=
  (wordCongr (fun x y : Word => x &&& y) (eq147_210 a) (rfl : (4503599627370495 : Word) = 4503599627370495)).trans (BitVec.and_comm _ _)

private theorem eq149_212 (a : Limbs) : (w149 a) = (w212 a) :=
  (wordCongr (fun x y : Word => x &&& y) (rfl : ((w50 a) : Word) = (w50 a)) (rfl : (281474976710655 : Word) = 281474976710655)).trans (BitVec.and_comm _ _)

private theorem eq150_213 (a : Limbs) : (w150 a) = (w213 a) :=
  wordCongr (fun x y : Word => (mulResult x y).2) (eq129_200 a) (rfl : (68719492368 : Word) = 68719492368)

private theorem eq151_213 (a : Limbs) : (w151 a) = (w213 a) :=
  (BitVec.add_zero (w150 a)).trans (eq150_213 a)

private theorem eq152_214 (a : Limbs) : (w152 a) = (w214 a) :=
  wordCongr (fun x y : Word => BitVec.ofNat 64 (addSpec x y).2.CF.toNat) (rfl : ((w123 a) : Word) = (w123 a)) (eq130_201 a)

private theorem eq153_215 (a : Limbs) : (w153 a) = (w215 a) :=
  wordCongr (fun x y : Word => x + y) (eq151_213 a) (eq152_214 a)

private theorem eq154_215 (a : Limbs) : (w154 a) = (w215 a) :=
  (BitVec.add_zero (w153 a)).trans (eq153_215 a)

private theorem eq155_216 (a : Limbs) : (w155 a) = (w216 a) :=
  wordCongr (fun x y : Word => BitVec.ofNat 64 (addSpec x y).2.CF.toNat) (eq131_202 a) (eq146_209 a)

private theorem eq156_217 (a : Limbs) : (w156 a) = (w217 a) :=
  wordCongr (fun x y : Word => x + y) (eq154_215 a) (eq155_216 a)

private theorem eq157_218 (a : Limbs) : (w157 a) = (w218 a) :=
  wordCongr (shldResult 12) (eq156_217 a) (eq147_210 a)

private theorem eq158_219 (a : Limbs) : (w158 a) = (w219 a) :=
  wordCongr (fun x y : Word => x + y) (eq149_212 a) (eq157_218 a)

private theorem squareLimbs_words (a : Limbs) : squareLimbs a = ((w167 a), (w181 a), (w197 a), (w211 a), (w219 a)) := by
  unfold squareLimbs
  extract_lets x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69
  have h5 : x5 = a[1] := rfl
  have h6 : x6 = a[4] := rfl
  have h7 : x7 = a[0] := rfl
  have h8 : x8 = a[2] := rfl
  have h9 : x9 = a[3] := rfl
  have h10 : x10 = (w62 a) := by
    dsimp only [x10]
    rw [h8, h6]
    rfl
  have h11 : x11 = (w93 a) := by
    dsimp only [x11]
    rw [h9, h6]
    rfl
  have h12 : x12 = (w16 a) := by
    dsimp only [x12]
    rw [h8]
    rfl
  have h13 : x13 = (w59 a) := by
    dsimp only [x13]
    rw [h7]
    rfl
  have h14 : x14 = (w7 a) := by
    dsimp only [x14]
    rw [h9, h5]
    rfl
  have h15 : x15 = (w35 a) := by
    dsimp only [x15]
    rw [h8, h5]
    rfl
  have h16 : x16 = (w36 a) := by
    dsimp only [x16]
    rw [h9, h7]
    rfl
  have h17 : x17 = (w8 a) := by
    dsimp only [x17]
    rw [h6, h7]
    rfl
  have h18 : x18 = (w0 a) := by
    dsimp only [x18]
    rw [h6, h5]
    rfl
  have h19 : x19 = (w79 a) := by
    dsimp only [x19]
    rw [h7]
    rfl
  have h20 : x20 = (w20 a) := by
    dsimp only [x20]
    rw [h6]
    rfl
  have h21 : x21 = (w1 a) := by
    dsimp only [x21]
    rw [h9, h8]
    rfl
  have h22 : x22 = (w64 a) := by
    dsimp only [x22]
    rw [h9]
    rfl
  have h23 : x23 = (w91 a) := by
    dsimp only [x23]
    rw [h5]
    rfl
  have h24 : x24 = (w30 a) := by
    dsimp only [x24]
    rw [h20]
    rfl
  have h25 : x25 = (w2 a) := by
    dsimp only [x25]
    rw [h18, h21]
    rfl
  have h26 : x26 = (w11 a) := by
    dsimp only [x26]
    rw [h14, h17]
    rfl
  have h27 : x27 = (w63 a) := by
    dsimp only [x27]
    rw [h10]
    rfl
  have h28 : x28 = (w80 a) := by
    dsimp only [x28]
    rw [h19, h5]
    rfl
  have h29 : x29 = (w39 a) := by
    dsimp only [x29]
    rw [h15, h16]
    rfl
  have h30 : x30 = (w90 a) := by
    dsimp only [x30]
    rw [h19, h8]
    rfl
  have h31 : x31 = (w94 a) := by
    dsimp only [x31]
    rw [h11]
    rfl
  have h32 : x32 = (w21 a) := by
    dsimp only [x32]
    rw [h6, h20]
    rfl
  have h33 : x33 = (w42 a) := by
    dsimp only [x33]
    rw [h24]
    rfl
  have h34 : x34 = (w65 a) := by
    dsimp only [x34]
    rw [h27, h22]
    rfl
  have h35 : x35 = (w3 a) := by
    dsimp only [x35]
    rw [h25]
    rfl
  have h36 : x36 = (w15 a) := by
    dsimp only [x36]
    rw [h26]
    rfl
  have h37 : x37 = (w92 a) := by
    dsimp only [x37]
    rw [h30, h23]
    rfl
  have h38 : x38 = (w43 a) := by
    dsimp only [x38]
    rw [h29]
    rfl
  have h39 : x39 = (w46 a) := by
    dsimp only [x39]
    rw [h33, h38]
    rfl
  have h40 : x40 = (w25 a) := by
    dsimp only [x40]
    rw [h32]
    rfl
  have h41 : x41 = (w24 a) := by
    dsimp only [x41]
    rw [h36, h12]
    rfl
  have h42 : x42 = (w123 a) := by
    dsimp only [x42]
    rw [h39]
    rfl
  have h43 : x43 = (w29 a) := by
    dsimp only [x43]
    rw [h41, h40]
    rfl
  have h44 : x44 = (w47 a) := by
    dsimp only [x44]
    rw [h24, h8, h5, h9, h7, h15, h16, h29, h33, h38, h39]
    rfl
  have h45 : x45 = (w50 a) := by
    dsimp only [x45]
    rw [h43, h44]
    rfl
  have h46 : x46 = (w160 a) := by
    dsimp only [x46]
    rw [h6, h7, h9, h5, h14, h17, h26, h8, h36, h12, h32, h41, h40, h43, h44, h45]
    rfl
  have h47 : x47 = (w161 a) := by
    dsimp only [x47]
    rw [h35, h46]
    rfl
  have h48 : x48 = (w164 a) := by
    dsimp only [x48]
    rw [h47, h45]
    rfl
  have h49 : x49 = (w170 a) := by
    dsimp only [x49]
    rw [h9, h8, h6, h5, h18, h21, h25, h35, h46, h47]
    rfl
  have h50 : x50 = (w171 a) := by
    dsimp only [x50]
    rw [h34, h49]
    rfl
  have h51 : x51 = (w165 a) := by
    dsimp only [x51]
    rw [h48]
    rfl
  have h52 : x52 = (w166 a) := by
    dsimp only [x52]
    rw [h51, h13]
    rfl
  have h53 : x53 = (w172 a) := by
    dsimp only [x53]
    rw [h50]
    rfl
  have h54 : x54 = (w173 a) := by
    dsimp only [x54]
    rw [h53]
    rfl
  have h55 : x55 = (w174 a) := by
    dsimp only [x55]
    rw [h54, h28]
    rfl
  have h56 : x56 = (w184 a) := by
    dsimp only [x56]
    rw [h9, h8, h6, h10, h27, h22, h34, h49, h50]
    rfl
  have h57 : x57 = (w185 a) := by
    dsimp only [x57]
    rw [h31, h56]
    rfl
  have h58 : x58 = (w179 a) := by
    dsimp only [x58]
    rw [h48, h7, h51, h13, h52]
    rfl
  have h59 : x59 = (w180 a) := by
    dsimp only [x59]
    rw [h55, h58]
    rfl
  have h60 : x60 = (w186 a) := by
    dsimp only [x60]
    rw [h57]
    rfl
  have h61 : x61 = (w187 a) := by
    dsimp only [x61]
    rw [h60]
    rfl
  have h62 : x62 = (w188 a) := by
    dsimp only [x62]
    rw [h37, h61]
    rfl
  have h63 : x63 = (w200 a) := by
    dsimp only [x63]
    rw [h9, h6, h11, h31, h56, h57]
    rfl
  have h64 : x64 = (w195 a) := by
    dsimp only [x64]
    rw [h53, h19, h5, h7, h54, h28, h55, h58, h59]
    rfl
  have h65 : x65 = (w201 a) := by
    dsimp only [x65]
    rw [h63]
    rfl
  have h66 : x66 = (w196 a) := by
    dsimp only [x66]
    rw [h62, h64]
    rfl
  have h67 : x67 = (w202 a) := by
    dsimp only [x67]
    rw [h42, h65]
    rfl
  have h68 : x68 = (w209 a) := by
    dsimp only [x68]
    rw [h19, h8, h7, h5, h30, h23, h60, h37, h61, h62, h64, h66]
    rfl
  have h69 : x69 = (w210 a) := by
    dsimp only [x69]
    rw [h67, h68]
    rfl
  rw [h52, h59, h66, h69, h45, h63, h42, h65, h67, h68]
  rfl

private theorem limbs_congr {a b c d e a' b' c' d' e' : Word}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e') :
    #v[a,b,c,d,e] = #v[a',b',c',d',e'] := by subst_vars; rfl

theorem inlineSquareWords_eq (a : Limbs) : inlineSquareWords a = squareWords a := by
  apply (inline_result a).trans
  apply Eq.trans _ (congrArg (fun t : Word × Word × Word × Word × Word =>
    #v[t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2]) (squareLimbs_words a)).symm
  exact limbs_congr (eq61_167 a) (eq89_181 a) (eq122_197 a) (eq148_211 a) (eq158_219 a)

end K256.Proofs.Sec1.Sqrt.Finish
