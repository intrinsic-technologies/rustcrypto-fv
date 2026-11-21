import K256.Proofs.Common.Field.Square
import X86Proofs.Instructions.Shrd.Operation

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field X86Proofs

def cubeProduct11FE67H (a b : Limbs) : Vector Word 6 :=
  let w11fe67h : Word := (mulResult b[0] a[3]).2
  let w11fe67 : Word := b[0] * a[3]
  let w11fe73h : Word := (mulResult b[1] a[2]).2
  let w11fe73 : Word := b[1] * a[2]
  let w11fe7fc : Word := BitVec.ofNat 64 (addSpec w11fe73 w11fe67).2.CF.toNat
  let w11fe7f : Word := w11fe73 + w11fe67
  let w11fe82 : Word := w11fe73h + w11fe67h + w11fe7fc
  let w11fe8dh : Word := (mulResult b[2] a[1]).2
  let w11fe8d : Word := b[2] * a[1]
  let w11fe96c : Word := BitVec.ofNat 64 (addSpec w11fe8d w11fe7f).2.CF.toNat
  let w11fe96 : Word := w11fe8d + w11fe7f
  let w11fe99 : Word := w11fe8dh + w11fe82 + w11fe96c
  let w11fea4h : Word := (mulResult b[3] a[0]).2
  let w11fea4 : Word := b[3] * a[0]
  let w11feadc : Word := BitVec.ofNat 64 (addSpec w11fea4 w11fe96).2.CF.toNat
  let w11fead : Word := w11fea4 + w11fe96
  let w11feb0 : Word := w11fea4h + w11fe99 + w11feadc
  let w11febbh : Word := (mulResult b[4] a[4]).2
  let w11febb : Word := b[4] * a[4]
  let w11fec1 : Word := shldResult 0xc w11febbh w11febb
  let w11fec6 : Word := w11febb &&& 0xfffffffffffff
  let w11fec9h : Word := (mulResult w11fec6 0x1000003d10).2
  let w11fec9 : Word := w11fec6 * 0x1000003d10
  let w11fed2c : Word := BitVec.ofNat 64 (addSpec w11fec9 w11fead).2.CF.toNat
  #v[w11fead, w11feb0, w11fec1, w11fec9h, w11fec9, w11fed2c]

def cubeProduct11FED2 (a b : Limbs) (s : Vector Word 6) : Vector Word 11 :=
  let w11fed2 : Word := s[4] + s[0]
  let w11fed5 : Word := s[3] + s[1] + s[5]
  let w11fedb : Word := shldResult 0xc w11fed5 w11fed2
  let w11fee8h : Word := (mulResult b[0] a[4]).2
  let w11fee8 : Word := b[0] * a[4]
  let w11fefdh : Word := (mulResult b[1] a[3]).2
  let w11fefd : Word := b[1] * a[3]
  let w11ff0bh : Word := (mulResult b[2] a[2]).2
  let w11ff0b : Word := b[2] * a[2]
  let w11ff1bh : Word := (mulResult b[3] a[1]).2
  let w11ff1b : Word := b[3] * a[1]
  let w11ff2ah : Word := (mulResult b[4] a[0]).2
  let w11ff2a : Word := b[4] * a[0]
  let w11ff43h : Word := (mulResult s[2] 0x1000003d10).2
  let w11ff43 : Word := s[2] * 0x1000003d10
  let w11ff46 : Word := w11fed5 >>> 0x34
  let w11ff4ac : Word := BitVec.ofNat 64 (addSpec w11fefd w11fee8).2.CF.toNat
  let w11ff4a : Word := w11fefd + w11fee8
  let w11ff4f : Word := w11fefdh + w11fee8h + w11ff4ac
  let w11ff54c : Word := BitVec.ofNat 64 (addSpec w11ff4a w11ff0b).2.CF.toNat
  let w11ff54 : Word := w11ff4a + w11ff0b
  let w11ff57 : Word := w11ff4f + w11ff0bh + w11ff54c
  let w11ff5cc : Word := BitVec.ofNat 64 (addSpec w11ff54 w11ff1b).2.CF.toNat
  let w11ff5c : Word := w11ff54 + w11ff1b
  #v[w11fed2, w11fedb, w11ff1bh, w11ff2ah, w11ff2a, w11ff43h, w11ff43, w11ff46, w11ff57, w11ff5cc, w11ff5c]

def cubeProduct11FF5F (a b : Limbs) (s : Vector Word 11) : Vector Word 15 :=
  let w11ff5f : Word := s[8] + s[2] + s[9]
  let w11ff64c : Word := BitVec.ofNat 64 (addSpec s[10] s[4]).2.CF.toNat
  let w11ff64 : Word := s[10] + s[4]
  let w11ff67 : Word := w11ff5f + s[3] + w11ff64c
  let w11ff6ac : Word := BitVec.ofNat 64 (addSpec w11ff64 s[6]).2.CF.toNat
  let w11ff6a : Word := w11ff64 + s[6]
  let w11ff6d : Word := w11ff67 + s[5] + w11ff6ac
  let w11ff70c : Word := BitVec.ofNat 64 (addSpec w11ff6a s[1]).2.CF.toNat
  let w11ff70 : Word := w11ff6a + s[1]
  let w11ff73 : Word := w11ff6d + s[7] + w11ff70c
  let w11ff79 : Word := w11ff73 >>> 0x34
  let w11ff7d : Word := shldResult 0xc w11ff73 w11ff70
  let w11ff85h : Word := (mulResult b[0] a[0]).2
  let w11ff85 : Word := b[0] * a[0]
  let w11ff95h : Word := (mulResult b[1] a[4]).2
  let w11ff95 : Word := b[1] * a[4]
  let w11ffa3 : Word := w11ff70 >>> 0x30
  let w11ffafh : Word := (mulResult b[2] a[3]).2
  let w11ffaf : Word := b[2] * a[3]
  let w11ffbfh : Word := (mulResult b[3] a[2]).2
  let w11ffbf : Word := b[3] * a[2]
  let w11ffd3h : Word := (mulResult b[4] a[1]).2
  let w11ffd3 : Word := b[4] * a[1]
  let w11ffd6 : Word := (BitVec.setWidth 32 w11ffa3).setWidth 64 &&& 0xf
  #v[s[0], w11ff70, w11ff79, w11ff7d, w11ff85h, w11ff85, w11ff95h, w11ff95, w11ffafh, w11ffaf, w11ffbfh, w11ffbf, w11ffd3h, w11ffd3, w11ffd6]

def cubeProduct11FFD9C (a b : Limbs) (s : Vector Word 15) : Vector Word 7 :=
  let w11ffd9c : Word := BitVec.ofNat 64 (addSpec s[9] s[7]).2.CF.toNat
  let w11ffd9 : Word := s[9] + s[7]
  let w11ffdc : Word := s[8] + s[6] + w11ffd9c
  let w11ffdfc : Word := BitVec.ofNat 64 (addSpec w11ffd9 s[11]).2.CF.toNat
  let w11ffdf : Word := w11ffd9 + s[11]
  let w11ffe2 : Word := w11ffdc + s[10] + w11ffdfc
  let w11ffe5c : Word := BitVec.ofNat 64 (addSpec s[13] w11ffdf).2.CF.toNat
  let w11ffe5 : Word := s[13] + w11ffdf
  let w11ffe8 : Word := w11ffe2 + s[12] + w11ffe5c
  let w11ffebc : Word := BitVec.ofNat 64 (addSpec w11ffe5 s[3]).2.CF.toNat
  let w11ffeb : Word := w11ffe5 + s[3]
  let w11ffee : Word := w11ffe8 + s[2] + w11ffebc
  let w11fff4 : Word := shldResult 0xc w11ffee w11ffeb
  let w11fff9 : Word := w11ffeb <<< 0x4
  let w120007 : Word := w11fff9 &&& 0xfffffffffffff0
  let w12000a : Word := w120007 ||| s[14]
  let w120017h : Word := (mulResult w12000a 0x1000003d1).2
  let w120017 : Word := w12000a * 0x1000003d1
  let w12001d : Word := w11ffee >>> 0x34
  let w120021c : Word := BitVec.ofNat 64 (addSpec w120017 s[5]).2.CF.toNat
  let w120021 : Word := w120017 + s[5]
  let w120026 : Word := w120017h + s[4] + w120021c
  let w12002b : Word := shldResult 0xc w120026 w120021
  let w120038h : Word := (mulResult b[0] a[1]).2
  #v[s[0], s[1], w11fff4, w12001d, w120021, w12002b, w120038h]

def cubeProduct120038 (a b : Limbs) (s : Vector Word 7) : Vector Word 12 :=
  let w120038 : Word := b[0] * a[1]
  let w12004ah : Word := (mulResult b[1] a[0]).2
  let w12004a : Word := b[1] * a[0]
  let w12005f : Word := s[4] &&& 0xfffffffffffff
  let w12006ah : Word := (mulResult b[2] a[4]).2
  let w12006a : Word := b[2] * a[4]
  let w12007ah : Word := (mulResult b[3] a[3]).2
  let w12007a : Word := b[3] * a[3]
  let w12008eh : Word := (mulResult b[4] a[2]).2
  let w12008e : Word := b[4] * a[2]
  let w120094c : Word := BitVec.ofNat 64 (addSpec w12007a w12006a).2.CF.toNat
  let w120094 : Word := w12007a + w12006a
  let w120097 : Word := w12007ah + w12006ah + w120094c
  let w12009ac : Word := BitVec.ofNat 64 (addSpec w12008e w120094).2.CF.toNat
  let w12009a : Word := w12008e + w120094
  let w12009d : Word := w120097 + w12008eh + w12009ac
  let w1200a0c : Word := BitVec.ofNat 64 (addSpec w12009a s[2]).2.CF.toNat
  let w1200a0 : Word := w12009a + s[2]
  let w1200a3 : Word := w12009d + s[3] + w1200a0c
  let w1200b3 : Word := w1200a0 &&& 0xfffffffffffff
  let w1200c0h : Word := (mulResult w1200b3 0x1000003d10).2
  let w1200c0 : Word := w1200b3 * 0x1000003d10
  let w1200c3c : Word := BitVec.ofNat 64 (addSpec w12004a w120038).2.CF.toNat
  let w1200c3 : Word := w12004a + w120038
  #v[s[0], s[1], s[5], s[6], w12004ah, w12005f, w1200a0, w1200a3, w1200c0h, w1200c0, w1200c3c, w1200c3]

def cubeProduct1200C8 (a b : Limbs) (s : Vector Word 12) : Vector Word 18 :=
  let w1200c8 : Word := s[4] + s[3] + s[10]
  let w1200cdc : Word := BitVec.ofNat 64 (addSpec s[11] s[9]).2.CF.toNat
  let w1200cd : Word := s[11] + s[9]
  let w1200d0 : Word := w1200c8 + s[8] + w1200cdc
  let w1200d3c : Word := BitVec.ofNat 64 (addSpec w1200cd s[2]).2.CF.toNat
  let w1200d3 : Word := w1200cd + s[2]
  let w1200d6 : Word := w1200d0 + 0x0 + w1200d3c
  let w1200dd : Word := shldResult 0xc s[7] s[6]
  let w1200e2 : Word := s[7] >>> 0x34
  let w1200e9 : Word := w1200d6 >>> 0x34
  let w1200ed : Word := shldResult 0xc w1200d6 w1200d3
  let w1200f7h : Word := (mulResult b[0] a[2]).2
  let w1200f7 : Word := b[0] * a[2]
  let w120109h : Word := (mulResult b[1] a[1]).2
  let w120109 : Word := b[1] * a[1]
  let w120119h : Word := (mulResult b[2] a[0]).2
  let w120119 : Word := b[2] * a[0]
  let w120128 : Word := w1200d3 &&& 0xfffffffffffff
  let w120130h : Word := (mulResult b[3] a[4]).2
  let w120130 : Word := b[3] * a[4]
  let w12013fh : Word := (mulResult b[4] a[3]).2
  let w12013f : Word := b[4] * a[3]
  let w12014ac : Word := BitVec.ofNat 64 (addSpec w12013f w120130).2.CF.toNat
  let w12014a : Word := w12013f + w120130
  #v[s[0], s[1], s[5], w1200dd, w1200e2, w1200e9, w1200ed, w1200f7h, w1200f7, w120109h, w120109, w120119h, w120119, w120128, w120130h, w12013fh, w12014ac, w12014a]

def cubeProduct12014D (s : Vector Word 18) : Vector Word 9 :=
  let w12014d : Word := s[15] + s[14] + s[16]
  let w120150c : Word := BitVec.ofNat 64 (addSpec s[17] s[3]).2.CF.toNat
  let w120150 : Word := s[17] + s[3]
  let w120153 : Word := w12014d + s[4] + w120150c
  let w120163 : Word := w120150 &&& 0xfffffffffffff
  let w120170h : Word := (mulResult w120163 0x1000003d10).2
  let w120170 : Word := w120163 * 0x1000003d10
  let w120173c : Word := BitVec.ofNat 64 (addSpec s[10] s[8]).2.CF.toNat
  let w120173 : Word := s[10] + s[8]
  let w120178 : Word := s[9] + s[7] + w120173c
  let w12017dc : Word := BitVec.ofNat 64 (addSpec w120173 s[12]).2.CF.toNat
  let w12017d : Word := w120173 + s[12]
  let w120182 : Word := w120178 + s[11] + w12017dc
  let w120187c : Word := BitVec.ofNat 64 (addSpec w12017d w120170).2.CF.toNat
  let w120187 : Word := w12017d + w120170
  let w12018a : Word := w120182 + w120170h + w120187c
  let w12018dc : Word := BitVec.ofNat 64 (addSpec w120187 s[6]).2.CF.toNat
  let w12018d : Word := w120187 + s[6]
  let w120190 : Word := w12018a + s[5] + w12018dc
  let w120193 : Word := shrdResult 0x34 w120150 w120153
  let w120198 : Word := w120153 >>> 0x34
  let w12019f : Word := shldResult 0xc w120190 w12018d
  let w1201a4 : Word := w120190 >>> 0x34
  let w1201a8 : Word := w12018d &&& 0xfffffffffffff
  #v[s[0], s[1], s[2], s[13], w120193, w120198, w12019f, w1201a4, w1201a8]

def cubeProduct1201AB (s : Vector Word 9) : Limbs :=
  let w1201ab : Word := s[5] * 0x1000003d10
  let w1201b2h : Word := (mulResult s[4] 0x1000003d10).2
  let w1201b2 : Word := s[4] * 0x1000003d10
  let w1201b5 : Word := s[0] &&& 0xfffffffffffff
  let w1201b8c : Word := BitVec.ofNat 64 (addSpec w1201b5 w1201b2).2.CF.toNat
  let w1201b8 : Word := w1201b5 + w1201b2
  let w1201bb : Word := w1201b2h + w1201ab + w1201b8c
  let w1201bec : Word := BitVec.ofNat 64 (addSpec w1201b8 s[6]).2.CF.toNat
  let w1201be : Word := w1201b8 + s[6]
  let w1201c1 : Word := w1201bb + s[7] + w1201bec
  let w1201c4 : Word := shldResult 0xc w1201c1 w1201be
  let w1201c9 : Word := w1201be &&& 0xfffffffffffff
  let top : Word := (s[1] &&& 0xffffffffffff) + w1201c4
  #v[s[2], s[3], s[8], w1201c9, top]

def cubeProduct (a b : Limbs) : Limbs :=
  let s := cubeProduct11FE67H a b
  let s := cubeProduct11FED2 a b s
  let s := cubeProduct11FF5F a b s
  let s := cubeProduct11FFD9C a b s
  let s := cubeProduct120038 a b s
  let s := cubeProduct1200C8 a b s
  let s := cubeProduct12014D s
  cubeProduct1201AB s

end K256.Proofs.Sec1.Affine.Uncompressed
