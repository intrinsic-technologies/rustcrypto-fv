import K256.Proofs.Common.Field.Square
import X86Proofs.Instructions.Shrd.Operation

namespace K256.Proofs.Sec1.Affine.Compressed

open X86Proofs K256.Proofs.Common.Field

def inputSquare120684H (a : Limbs) : Vector Word 8 :=
  let w120684h : Word := (mulResult a[3] a[0]).2
  let w120684 : Word := a[3] * a[0]
  let w120690h : Word := (mulResult a[2] a[1]).2
  let w120690 : Word := a[2] * a[1]
  let w120696c : Word := BitVec.ofNat 64 (addSpec w120690 w120684).2.CF.toNat
  let w120696 : Word := w120690 + w120684
  let w120699 : Word := w120684h + w120690h + w120696c
  let w12069c : Word := shldResult 0x1 w120699 w120696
  let w1206a4h : Word := (mulResult a[4] a[4]).2
  let w1206a4 : Word := a[4] * a[4]
  let w1206ba : Word := 0xffffffffffffd &&& w1206a4
  let w1206c7h : Word := (mulResult w1206ba 0x1000003d10).2
  let w1206c7 : Word := w1206ba * 0x1000003d10
  let w1206ca : Word := w120696 + w120696
  let w1206cdc : Word := BitVec.ofNat 64 (addSpec w1206c7 w1206ca).2.CF.toNat
  let w1206cd : Word := w1206c7 + w1206ca
  let w1206d5 : Word := w12069c + w1206c7h + w1206cdc
  let w1206d8 : Word := shldResult 0xc w1206a4h w1206a4
  let w1206e0 : Word := shldResult 0xc w1206d5 w1206cd
  let w1206edh : Word := (mulResult a[2] a[2]).2
  let w1206ed : Word := a[2] * a[2]
  let w1206f9h : Word := (mulResult w1206d8 0x1000003d10).2
  let w1206f9 : Word := w1206d8 * 0x1000003d10
  let w120705h : Word := (mulResult a[4] a[0]).2
  #v[w1206cd, w1206d5, w1206e0, w1206edh, w1206ed, w1206f9h, w1206f9, w120705h]

def inputSquare120705 (a : Limbs) (s : Vector Word 8) : Vector Word 7 :=
  let w120705 : Word := a[4] * a[0]
  let w120716h : Word := (mulResult a[3] a[1]).2
  let w120716 : Word := a[3] * a[1]
  let w120719 : Word := s[1] >>> 0x34
  let w12071dc : Word := BitVec.ofNat 64 (addSpec w120716 w120705).2.CF.toNat
  let w12071d : Word := w120716 + w120705
  let w120720 : Word := s[7] + w120716h + w12071dc
  let w120723 : Word := shldResult 0x1 w120720 w12071d
  let w120728 : Word := w12071d + w12071d
  let w12072bc : Word := BitVec.ofNat 64 (addSpec s[6] s[4]).2.CF.toNat
  let w12072b : Word := s[6] + s[4]
  let w12072e : Word := s[5] + s[3] + w12072bc
  let w120731c : Word := BitVec.ofNat 64 (addSpec w120728 w12072b).2.CF.toNat
  let w120731 : Word := w120728 + w12072b
  let w120734 : Word := w12072e + w120723 + w120731c
  let w120737c : Word := BitVec.ofNat 64 (addSpec w120731 s[2]).2.CF.toNat
  let w120737 : Word := w120731 + s[2]
  let w12073f : Word := w120734 + w120719 + w120737c
  let w120745 : Word := w12073f >>> 0x34
  let w120749 : Word := shldResult 0xc w12073f w120737
  let w120751 : Word := w120737 >>> 0x30
  let w120758h : Word := (mulResult a[0] a[0]).2
  let w120758 : Word := a[0] * a[0]
  let w120769 : Word := (BitVec.setWidth 32 w120751).setWidth 64 &&& 0xf
  #v[s[0], w120737, w120745, w120749, w120758h, w120758, w120769]

def inputSquare120777H (a : Limbs) (s : Vector Word 7) : Vector Word 7 :=
  let w120777h : Word := (mulResult a[3] a[2]).2
  let w120777 : Word := a[3] * a[2]
  let w120788h : Word := (mulResult a[4] a[1]).2
  let w120788 : Word := a[4] * a[1]
  let w12078bc : Word := BitVec.ofNat 64 (addSpec w120788 w120777).2.CF.toNat
  let w12078b : Word := w120788 + w120777
  let w12078e : Word := w120777h + w120788h + w12078bc
  let w120791 : Word := shldResult 0x1 w12078e w12078b
  let w120796 : Word := w12078b + w12078b
  let w120799c : Word := BitVec.ofNat 64 (addSpec w120796 s[3]).2.CF.toNat
  let w120799 : Word := w120796 + s[3]
  let w12079c : Word := w120791 + s[2] + w120799c
  let w1207a2 : Word := w12079c >>> 0x34
  let w1207a6 : Word := shldResult 0xc w12079c w120799
  let w1207ab : Word := w120799 <<< 0x4
  let w1207b9 : Word := w1207ab &&& 0xfffffffffffff0
  let w1207bc : Word := w1207b9 ||| s[6]
  let w1207c9h : Word := (mulResult w1207bc 0x1000003d1).2
  let w1207c9 : Word := w1207bc * 0x1000003d1
  let w1207ccc : Word := BitVec.ofNat 64 (addSpec w1207c9 s[5]).2.CF.toNat
  let w1207cc : Word := w1207c9 + s[5]
  let w1207d4 : Word := s[4] + w1207c9h + w1207ccc
  let w1207d7 : Word := shldResult 0xc w1207d4 w1207cc
  let w1207dc : Word := a[0] + a[0]
  #v[s[0], s[1], w1207a2, w1207a6, w1207cc, w1207d7, w1207dc]

def inputSquare1207E5H (a : Limbs) (s : Vector Word 7) : Vector Word 9 :=
  let w1207e5h : Word := (mulResult s[6] a[1]).2
  let w1207e5 : Word := s[6] * a[1]
  let w1207f4h : Word := (mulResult a[3] a[3]).2
  let w1207f4 : Word := a[3] * a[3]
  let w1207fd : Word := a[4] + a[4]
  let w120808h : Word := (mulResult w1207fd a[2]).2
  let w120808 : Word := w1207fd * a[2]
  let w12080ec : Word := BitVec.ofNat 64 (addSpec w120808 w1207f4).2.CF.toNat
  let w12080e : Word := w120808 + w1207f4
  let w120811 : Word := w1207f4h + w120808h + w12080ec
  let w120814c : Word := BitVec.ofNat 64 (addSpec w12080e s[3]).2.CF.toNat
  let w120814 : Word := w12080e + s[3]
  let w120817 : Word := w120811 + s[2] + w120814c
  let w120827 : Word := w120814 &&& 0xfffffffffffff
  let w120834h : Word := (mulResult w120827 0x1000003d10).2
  let w120834 : Word := w120827 * 0x1000003d10
  let w120837c : Word := BitVec.ofNat 64 (addSpec w120834 w1207e5).2.CF.toNat
  let w120837 : Word := w120834 + w1207e5
  let w12083a : Word := w1207e5h + w120834h + w120837c
  let w12083dc : Word := BitVec.ofNat 64 (addSpec w120837 s[5]).2.CF.toNat
  let w12083d : Word := w120837 + s[5]
  let w120843 : Word := w12083a + 0x0 + w12083dc
  let w12084a : Word := shldResult 0xc w120817 w120814
  let w12084f : Word := w120817 >>> 0x34
  #v[s[0], s[1], s[4], s[6], w1207fd, w12083d, w120843, w12084a, w12084f]

def inputSquare120856 (a : Limbs) (s : Vector Word 9) : Vector Word 7 :=
  let w120856 : Word := s[6] >>> 0x34
  let w12085a : Word := shldResult 0xc s[6] s[5]
  let w120867h : Word := (mulResult a[1] a[1]).2
  let w120867 : Word := a[1] * a[1]
  let w120873h : Word := (mulResult s[4] a[3]).2
  let w120873 : Word := s[4] * a[3]
  let w120879c : Word := BitVec.ofNat 64 (addSpec w120873 s[7]).2.CF.toNat
  let w120879 : Word := w120873 + s[7]
  let w12087c : Word := s[8] + w120873h + w120879c
  let w120882 : Word := w120879 &&& 0xfffffffffffff
  let w120885h : Word := (mulResult w120882 0x1000003d10).2
  let w120885 : Word := w120882 * 0x1000003d10
  let w120896h : Word := (mulResult s[3] a[2]).2
  let w120896 : Word := s[3] * a[2]
  let w12089cc : Word := BitVec.ofNat 64 (addSpec w120896 w120867).2.CF.toNat
  let w12089c : Word := w120896 + w120867
  let w12089f : Word := w120867h + w120896h + w12089cc
  let w1208a2c : Word := BitVec.ofNat 64 (addSpec w12089c w120885).2.CF.toNat
  let w1208a2 : Word := w12089c + w120885
  let w1208a5 : Word := w12089f + w120885h + w1208a2c
  let w1208a8c : Word := BitVec.ofNat 64 (addSpec w1208a2 w12085a).2.CF.toNat
  let w1208a8 : Word := w1208a2 + w12085a
  let w1208ae : Word := w1208a5 + w120856 + w1208a8c
  let w1208b1 : Word := shldResult 0xc w12087c w120879
  #v[s[0], s[1], s[2], s[5], w1208a8, w1208ae, w1208b1]

def inputSquareFinish (s : Vector Word 7) (masked : Word) : Limbs :=
  let w1208c8 : Word := s[5] >>> 0x34
  let w1208cc : Word := shldResult 0xc s[5] s[4]
  let w1208d4h : Word := (mulResult s[6] 0x1000003d10).2
  let w1208d4 : Word := s[6] * 0x1000003d10
  let w1208dac : Word := BitVec.ofNat 64 (addSpec w1208d4 masked).2.CF.toNat
  let w1208da : Word := w1208d4 + masked
  let w1208dd : Word := w1208d4h + 0x0 + w1208dac
  let w1208e1c : Word := BitVec.ofNat 64 (addSpec w1208da w1208cc).2.CF.toNat
  let w1208e1 : Word := w1208da + w1208cc
  let w1208e4 : Word := w1208c8 + w1208dd + w1208e1c
  let w1208e7 : Word := shldResult 0xc w1208e4 w1208e1
  let w1208fb : Word := s[1] &&& 0xffffffffffff
  let w1208fe : Word := w1208fb + w1208e7
  let w120913 : Word := s[2] &&& 0xfffffffffffff
  let w120916 : Word := s[3] &&& 0xfffffffffffff
  let w120921 : Word := s[4] &&& 0xfffffffffffff
  let w120924 : Word := w1208e1 &&& 0xfffffffffffff
  #v[w120913, w120916, w120921, w120924, w1208fe]

def inputSquare1208C0 (s : Vector Word 7) : Limbs :=
  inputSquareFinish s (0xffffffffffffe &&& s[0])

def inputSquare (a : Limbs) : Limbs :=
  let s := inputSquare120684H a
  let s := inputSquare120705 a s
  let s := inputSquare120777H a s
  let s := inputSquare1207E5H a s
  let s := inputSquare120856 a s
  inputSquare1208C0 s

def cubeProduct120934H (a b : Limbs) : Vector Word 6 :=
  let w120934h : Word := (mulResult b[0] a[3]).2
  let w120934 : Word := b[0] * a[3]
  let w120940h : Word := (mulResult b[1] a[2]).2
  let w120940 : Word := b[1] * a[2]
  let w120949c : Word := BitVec.ofNat 64 (addSpec w120940 w120934).2.CF.toNat
  let w120949 : Word := w120940 + w120934
  let w12094c : Word := w120940h + w120934h + w120949c
  let w12095fh : Word := (mulResult b[2] a[1]).2
  let w12095f : Word := b[2] * a[1]
  let w120968c : Word := BitVec.ofNat 64 (addSpec w12095f w120949).2.CF.toNat
  let w120968 : Word := w12095f + w120949
  let w12096b : Word := w12095fh + w12094c + w120968c
  let w12097bh : Word := (mulResult b[3] a[0]).2
  let w12097b : Word := b[3] * a[0]
  let w120984c : Word := BitVec.ofNat 64 (addSpec w12097b w120968).2.CF.toNat
  let w120984 : Word := w12097b + w120968
  let w120987 : Word := w12097bh + w12096b + w120984c
  let w12099ah : Word := (mulResult b[4] a[4]).2
  let w12099a : Word := b[4] * a[4]
  let w1209a0 : Word := shldResult 0xc w12099ah w12099a
  let w1209a5 : Word := w12099a &&& 0xfffffffffffff
  let w1209b2h : Word := (mulResult w1209a5 0x1000003d10).2
  let w1209b2 : Word := w1209a5 * 0x1000003d10
  let w1209b8c : Word := BitVec.ofNat 64 (addSpec w1209b2 w120984).2.CF.toNat
  #v[w120984, w120987, w1209a0, w1209b2h, w1209b2, w1209b8c]

def cubeProduct1209B8 (a b : Limbs) (s : Vector Word 6) : Vector Word 11 :=
  let w1209b8 : Word := s[4] + s[0]
  let w1209c0 : Word := s[3] + s[1] + s[5]
  let w1209c6 : Word := shldResult 0xc w1209c0 w1209b8
  let w1209ceh : Word := (mulResult b[0] a[4]).2
  let w1209ce : Word := b[0] * a[4]
  let w1209e3h : Word := (mulResult b[1] a[3]).2
  let w1209e3 : Word := b[1] * a[3]
  let w1209efh : Word := (mulResult b[2] a[2]).2
  let w1209ef : Word := b[2] * a[2]
  let w1209fdh : Word := (mulResult b[3] a[1]).2
  let w1209fd : Word := b[3] * a[1]
  let w120a09h : Word := (mulResult b[4] a[0]).2
  let w120a09 : Word := b[4] * a[0]
  let w120a22h : Word := (mulResult s[2] 0x1000003d10).2
  let w120a22 : Word := s[2] * 0x1000003d10
  let w120a25 : Word := w1209c0 >>> 0x34
  let w120a29c : Word := BitVec.ofNat 64 (addSpec w1209e3 w1209ce).2.CF.toNat
  let w120a29 : Word := w1209e3 + w1209ce
  let w120a2e : Word := w1209e3h + w1209ceh + w120a29c
  let w120a33c : Word := BitVec.ofNat 64 (addSpec w120a29 w1209ef).2.CF.toNat
  let w120a33 : Word := w120a29 + w1209ef
  let w120a36 : Word := w120a2e + w1209efh + w120a33c
  let w120a39c : Word := BitVec.ofNat 64 (addSpec w120a33 w1209fd).2.CF.toNat
  let w120a39 : Word := w120a33 + w1209fd
  #v[w1209b8, w1209c6, w1209fdh, w120a09h, w120a09, w120a22h, w120a22, w120a25, w120a36, w120a39c, w120a39]

def cubeProduct120A3C (a b : Limbs) (s : Vector Word 11) : Vector Word 15 :=
  let w120a3c : Word := s[8] + s[2] + s[9]
  let w120a3fc : Word := BitVec.ofNat 64 (addSpec s[10] s[4]).2.CF.toNat
  let w120a3f : Word := s[10] + s[4]
  let w120a42 : Word := w120a3c + s[3] + w120a3fc
  let w120a45c : Word := BitVec.ofNat 64 (addSpec w120a3f s[6]).2.CF.toNat
  let w120a45 : Word := w120a3f + s[6]
  let w120a48 : Word := w120a42 + s[5] + w120a45c
  let w120a4bc : Word := BitVec.ofNat 64 (addSpec w120a45 s[1]).2.CF.toNat
  let w120a4b : Word := w120a45 + s[1]
  let w120a4e : Word := w120a48 + s[7] + w120a4bc
  let w120a54 : Word := w120a4e >>> 0x34
  let w120a58 : Word := shldResult 0xc w120a4e w120a4b
  let w120a62h : Word := (mulResult b[0] a[0]).2
  let w120a62 : Word := b[0] * a[0]
  let w120a72h : Word := (mulResult b[1] a[4]).2
  let w120a72 : Word := b[1] * a[4]
  let w120a80 : Word := w120a4b >>> 0x30
  let w120a8ch : Word := (mulResult b[2] a[3]).2
  let w120a8c : Word := b[2] * a[3]
  let w120a9fh : Word := (mulResult b[3] a[2]).2
  let w120a9f : Word := b[3] * a[2]
  let w120ab4h : Word := (mulResult b[4] a[1]).2
  let w120ab4 : Word := b[4] * a[1]
  let w120ab7 : Word := (BitVec.setWidth 32 w120a80).setWidth 64 &&& 0xf
  #v[s[0], w120a4b, w120a54, w120a58, w120a62h, w120a62, w120a72h, w120a72, w120a8ch, w120a8c, w120a9fh, w120a9f, w120ab4h, w120ab4, w120ab7]

def cubeProduct120ABBC (a b : Limbs) (s : Vector Word 15) : Vector Word 7 :=
  let w120abbc : Word := BitVec.ofNat 64 (addSpec s[9] s[7]).2.CF.toNat
  let w120abb : Word := s[9] + s[7]
  let w120abe : Word := s[8] + s[6] + w120abbc
  let w120ac1c : Word := BitVec.ofNat 64 (addSpec w120abb s[11]).2.CF.toNat
  let w120ac1 : Word := w120abb + s[11]
  let w120ac4 : Word := w120abe + s[10] + w120ac1c
  let w120ac7c : Word := BitVec.ofNat 64 (addSpec s[13] w120ac1).2.CF.toNat
  let w120ac7 : Word := s[13] + w120ac1
  let w120aca : Word := w120ac4 + s[12] + w120ac7c
  let w120acdc : Word := BitVec.ofNat 64 (addSpec w120ac7 s[3]).2.CF.toNat
  let w120acd : Word := w120ac7 + s[3]
  let w120ad0 : Word := w120aca + s[2] + w120acdc
  let w120ad6 : Word := shldResult 0xc w120ad0 w120acd
  let w120adb : Word := w120acd <<< 0x4
  let w120ae9 : Word := w120adb &&& 0xfffffffffffff0
  let w120aec : Word := w120ae9 ||| s[14]
  let w120af9h : Word := (mulResult w120aec 0x1000003d1).2
  let w120af9 : Word := w120aec * 0x1000003d1
  let w120aff : Word := w120ad0 >>> 0x34
  let w120b03c : Word := BitVec.ofNat 64 (addSpec w120af9 s[5]).2.CF.toNat
  let w120b03 : Word := w120af9 + s[5]
  let w120b08 : Word := w120af9h + s[4] + w120b03c
  let w120b0d : Word := shldResult 0xc w120b08 w120b03
  let w120b1ah : Word := (mulResult b[0] a[1]).2
  #v[s[0], s[1], w120ad6, w120aff, w120b03, w120b0d, w120b1ah]

def cubeProduct120B1A (a b : Limbs) (s : Vector Word 7) : Vector Word 12 :=
  let w120b1a : Word := b[0] * a[1]
  let w120b2ch : Word := (mulResult b[1] a[0]).2
  let w120b2c : Word := b[1] * a[0]
  let w120b41 : Word := s[4] &&& 0xfffffffffffff
  let w120b4ch : Word := (mulResult b[2] a[4]).2
  let w120b4c : Word := b[2] * a[4]
  let w120b5ah : Word := (mulResult b[3] a[3]).2
  let w120b5a : Word := b[3] * a[3]
  let w120b6fh : Word := (mulResult b[4] a[2]).2
  let w120b6f : Word := b[4] * a[2]
  let w120b75c : Word := BitVec.ofNat 64 (addSpec w120b5a w120b4c).2.CF.toNat
  let w120b75 : Word := w120b5a + w120b4c
  let w120b78 : Word := w120b5ah + w120b4ch + w120b75c
  let w120b7bc : Word := BitVec.ofNat 64 (addSpec w120b6f w120b75).2.CF.toNat
  let w120b7b : Word := w120b6f + w120b75
  let w120b7e : Word := w120b78 + w120b6fh + w120b7bc
  let w120b81c : Word := BitVec.ofNat 64 (addSpec w120b7b s[2]).2.CF.toNat
  let w120b81 : Word := w120b7b + s[2]
  let w120b84 : Word := w120b7e + s[3] + w120b81c
  let w120b94 : Word := w120b81 &&& 0xfffffffffffff
  let w120ba1h : Word := (mulResult w120b94 0x1000003d10).2
  let w120ba1 : Word := w120b94 * 0x1000003d10
  let w120ba4c : Word := BitVec.ofNat 64 (addSpec w120b2c w120b1a).2.CF.toNat
  let w120ba4 : Word := w120b2c + w120b1a
  #v[s[0], s[1], s[5], s[6], w120b2ch, w120b41, w120b81, w120b84, w120ba1h, w120ba1, w120ba4c, w120ba4]

def cubeProduct120BA9 (a b : Limbs) (s : Vector Word 12) : Vector Word 18 :=
  let w120ba9 : Word := s[4] + s[3] + s[10]
  let w120baec : Word := BitVec.ofNat 64 (addSpec s[11] s[9]).2.CF.toNat
  let w120bae : Word := s[11] + s[9]
  let w120bb1 : Word := w120ba9 + s[8] + w120baec
  let w120bb4c : Word := BitVec.ofNat 64 (addSpec w120bae s[2]).2.CF.toNat
  let w120bb4 : Word := w120bae + s[2]
  let w120bb7 : Word := w120bb1 + 0x0 + w120bb4c
  let w120bbe : Word := shldResult 0xc s[7] s[6]
  let w120bc3 : Word := s[7] >>> 0x34
  let w120bca : Word := w120bb7 >>> 0x34
  let w120bce : Word := shldResult 0xc w120bb7 w120bb4
  let w120bd8h : Word := (mulResult b[0] a[2]).2
  let w120bd8 : Word := b[0] * a[2]
  let w120beah : Word := (mulResult b[1] a[1]).2
  let w120bea : Word := b[1] * a[1]
  let w120bf8h : Word := (mulResult b[2] a[0]).2
  let w120bf8 : Word := b[2] * a[0]
  let w120c05 : Word := w120bb4 &&& 0xfffffffffffff
  let w120c0dh : Word := (mulResult b[3] a[4]).2
  let w120c0d : Word := b[3] * a[4]
  let w120c1dh : Word := (mulResult b[4] a[3]).2
  let w120c1d : Word := b[4] * a[3]
  let w120c28c : Word := BitVec.ofNat 64 (addSpec w120c1d w120c0d).2.CF.toNat
  let w120c28 : Word := w120c1d + w120c0d
  #v[s[0], s[1], s[5], w120bbe, w120bc3, w120bca, w120bce, w120bd8h, w120bd8, w120beah, w120bea, w120bf8h, w120bf8, w120c05, w120c0dh, w120c1dh, w120c28c, w120c28]

def cubeProduct120C2B (s : Vector Word 18) : Vector Word 9 :=
  let w120c2b : Word := s[15] + s[14] + s[16]
  let w120c2ec : Word := BitVec.ofNat 64 (addSpec s[17] s[3]).2.CF.toNat
  let w120c2e : Word := s[17] + s[3]
  let w120c31 : Word := w120c2b + s[4] + w120c2ec
  let w120c41 : Word := w120c2e &&& 0xfffffffffffff
  let w120c4eh : Word := (mulResult w120c41 0x1000003d10).2
  let w120c4e : Word := w120c41 * 0x1000003d10
  let w120c51c : Word := BitVec.ofNat 64 (addSpec s[10] s[8]).2.CF.toNat
  let w120c51 : Word := s[10] + s[8]
  let w120c56 : Word := s[9] + s[7] + w120c51c
  let w120c5bc : Word := BitVec.ofNat 64 (addSpec w120c51 s[12]).2.CF.toNat
  let w120c5b : Word := w120c51 + s[12]
  let w120c5e : Word := w120c56 + s[11] + w120c5bc
  let w120c63c : Word := BitVec.ofNat 64 (addSpec w120c5b w120c4e).2.CF.toNat
  let w120c63 : Word := w120c5b + w120c4e
  let w120c66 : Word := w120c5e + w120c4eh + w120c63c
  let w120c69c : Word := BitVec.ofNat 64 (addSpec w120c63 s[6]).2.CF.toNat
  let w120c69 : Word := w120c63 + s[6]
  let w120c6c : Word := w120c66 + s[5] + w120c69c
  let w120c6f : Word := shrdResult 0x34 w120c2e w120c31
  let w120c74 : Word := w120c31 >>> 0x34
  let w120c7b : Word := shldResult 0xc w120c6c w120c69
  let w120c80 : Word := w120c6c >>> 0x34
  let w120c84 : Word := w120c69 &&& 0xfffffffffffff
  #v[s[0], s[1], s[2], s[13], w120c6f, w120c74, w120c7b, w120c80, w120c84]

def cubeProduct120C87 (s : Vector Word 9) : Limbs :=
  let w120c87 : Word := s[5] * 0x1000003d10
  let w120c8eh : Word := (mulResult s[4] 0x1000003d10).2
  let w120c8e : Word := s[4] * 0x1000003d10
  let w120c96 : Word := s[0] &&& 0xfffffffffffff
  let w120c99c : Word := BitVec.ofNat 64 (addSpec w120c96 w120c8e).2.CF.toNat
  let w120c99 : Word := w120c96 + w120c8e
  let w120c9c : Word := w120c8eh + w120c87 + w120c99c
  let w120c9fc : Word := BitVec.ofNat 64 (addSpec w120c99 s[6]).2.CF.toNat
  let w120c9f : Word := w120c99 + s[6]
  let w120ca2 : Word := w120c9c + s[7] + w120c9fc
  let w120ca5 : Word := 0xfffffffffffff &&& w120c9f
  let w120ca8 : Word := shldResult 0xc w120ca2 w120c9f
  let w120cb7 : Word := s[1] &&& 0xffffffffffff
  let w120cba : Word := w120cb7 + w120ca8
  #v[s[2], s[3], s[8], w120ca5, w120cba]

def cubeProduct (a b : Limbs) : Limbs :=
  let s := cubeProduct120934H a b
  let s := cubeProduct1209B8 a b s
  let s := cubeProduct120A3C a b s
  let s := cubeProduct120ABBC a b s
  let s := cubeProduct120B1A a b s
  let s := cubeProduct120BA9 a b s
  let s := cubeProduct120C2B s
  cubeProduct120C87 s

end K256.Proofs.Sec1.Affine.Compressed
