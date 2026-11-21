import K256.Proofs.Common.Field.Square
import X86Proofs.Instructions.Shrd.Operation

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field X86Proofs

def squareY11F919H (a : Limbs) : Vector Word 8 :=
  let w11f919h : Word := (mulResult a[3] a[0]).2
  let w11f919 : Word := a[3] * a[0]
  let w11f925h : Word := (mulResult a[2] a[1]).2
  let w11f925 : Word := a[2] * a[1]
  let w11f92ec : Word := BitVec.ofNat 64 (addSpec w11f925 w11f919).2.CF.toNat
  let w11f92e : Word := w11f925 + w11f919
  let w11f931 : Word := w11f925h + w11f919h + w11f92ec
  let w11f934 : Word := shldResult 0x1 w11f931 w11f92e
  let w11f93ch : Word := (mulResult a[4] a[4]).2
  let w11f93c : Word := a[4] * a[4]
  let w11f942 : Word := w11f92e + w11f92e
  let w11f94f : Word := shldResult 0xc w11f93ch w11f93c
  let w11f954 : Word := w11f93c &&& 0xffffffffffffd
  let w11f961h : Word := (mulResult w11f954 0x1000003d10).2
  let w11f961 : Word := w11f954 * 0x1000003d10
  let w11f967c : Word := BitVec.ofNat 64 (addSpec w11f961 w11f942).2.CF.toNat
  let w11f967 : Word := w11f961 + w11f942
  let w11f96f : Word := w11f961h + w11f934 + w11f967c
  let w11f975 : Word := shldResult 0xc w11f96f w11f967
  let w11f980h : Word := (mulResult a[2] a[2]).2
  let w11f980 : Word := a[2] * a[2]
  let w11f98ch : Word := (mulResult w11f94f 0x1000003d10).2
  let w11f98c : Word := w11f94f * 0x1000003d10
  let w11f998h : Word := (mulResult a[4] a[0]).2
  #v[w11f967, w11f96f, w11f975, w11f980h, w11f980, w11f98ch, w11f98c, w11f998h]

def squareY11F998 (a : Limbs) (s : Vector Word 8) : Vector Word 7 :=
  let w11f998 : Word := a[4] * a[0]
  let w11f9a4h : Word := (mulResult a[3] a[1]).2
  let w11f9a4 : Word := a[3] * a[1]
  let w11f9a7 : Word := s[1] >>> 0x34
  let w11f9abc : Word := BitVec.ofNat 64 (addSpec w11f9a4 w11f998).2.CF.toNat
  let w11f9ab : Word := w11f9a4 + w11f998
  let w11f9ae : Word := s[7] + w11f9a4h + w11f9abc
  let w11f9b1 : Word := shldResult 0x1 w11f9ae w11f9ab
  let w11f9b6 : Word := w11f9ab + w11f9ab
  let w11f9b9c : Word := BitVec.ofNat 64 (addSpec s[6] s[4]).2.CF.toNat
  let w11f9b9 : Word := s[6] + s[4]
  let w11f9bc : Word := s[5] + s[3] + w11f9b9c
  let w11f9bfc : Word := BitVec.ofNat 64 (addSpec w11f9b9 w11f9b6).2.CF.toNat
  let w11f9bf : Word := w11f9b9 + w11f9b6
  let w11f9c2 : Word := w11f9bc + w11f9b1 + w11f9bfc
  let w11f9c5c : Word := BitVec.ofNat 64 (addSpec w11f9bf s[2]).2.CF.toNat
  let w11f9c5 : Word := w11f9bf + s[2]
  let w11f9cd : Word := w11f9c2 + w11f9a7 + w11f9c5c
  let w11f9d3 : Word := w11f9cd >>> 0x34
  let w11f9d7 : Word := shldResult 0xc w11f9cd w11f9c5
  let w11f9df : Word := w11f9c5 >>> 0x30
  let w11f9e6h : Word := (mulResult a[0] a[0]).2
  let w11f9e6 : Word := a[0] * a[0]
  let w11f9f7 : Word := (BitVec.setWidth 32 w11f9df).setWidth 64 &&& 0xf
  #v[s[0], w11f9c5, w11f9d3, w11f9d7, w11f9e6h, w11f9e6, w11f9f7]

def squareY11F9FEH (a : Limbs) (s : Vector Word 7) : Vector Word 6 :=
  let w11f9feh : Word := (mulResult a[3] a[2]).2
  let w11f9fe : Word := a[3] * a[2]
  let w11fa12h : Word := (mulResult a[4] a[1]).2
  let w11fa12 : Word := a[4] * a[1]
  let w11fa15c : Word := BitVec.ofNat 64 (addSpec w11fa12 w11f9fe).2.CF.toNat
  let w11fa15 : Word := w11fa12 + w11f9fe
  let w11fa18 : Word := w11f9feh + w11fa12h + w11fa15c
  let w11fa1b : Word := shldResult 0x1 w11fa18 w11fa15
  let w11fa20 : Word := w11fa15 + w11fa15
  let w11fa23c : Word := BitVec.ofNat 64 (addSpec w11fa20 s[3]).2.CF.toNat
  let w11fa23 : Word := w11fa20 + s[3]
  let w11fa26 : Word := w11fa1b + s[2] + w11fa23c
  let w11fa2c : Word := w11fa26 >>> 0x34
  let w11fa30 : Word := shldResult 0xc w11fa26 w11fa23
  let w11fa35 : Word := w11fa23 <<< 0x4
  let w11fa43 : Word := w11fa35 &&& 0xfffffffffffff0
  let w11fa46 : Word := w11fa43 ||| s[6]
  let w11fa53h : Word := (mulResult w11fa46 0x1000003d1).2
  let w11fa53 : Word := w11fa46 * 0x1000003d1
  let w11fa59c : Word := BitVec.ofNat 64 (addSpec w11fa53 s[5]).2.CF.toNat
  let w11fa59 : Word := w11fa53 + s[5]
  let w11fa5c : Word := w11fa53h + s[4] + w11fa59c
  let w11fa5f : Word := shldResult 0xc w11fa5c w11fa59
  let w11fa6e : Word := w11fa59 &&& 0xfffffffffffff
  #v[s[0], s[1], w11fa2c, w11fa30, w11fa5f, w11fa6e]

def squareY11FA79 (a : Limbs) (s : Vector Word 6) : Vector Word 9 :=
  let w11fa79 : Word := a[0] + a[0]
  let w11fa81h : Word := (mulResult w11fa79 a[1]).2
  let w11fa81 : Word := w11fa79 * a[1]
  let w11fa8dh : Word := (mulResult a[3] a[3]).2
  let w11fa8d : Word := a[3] * a[3]
  let w11fa9e : Word := a[4] + a[4]
  let w11faadh : Word := (mulResult w11fa9e a[2]).2
  let w11faad : Word := w11fa9e * a[2]
  let w11fab3c : Word := BitVec.ofNat 64 (addSpec w11faad w11fa8d).2.CF.toNat
  let w11fab3 : Word := w11faad + w11fa8d
  let w11fab6 : Word := w11fa8dh + w11faadh + w11fab3c
  let w11fab9c : Word := BitVec.ofNat 64 (addSpec w11fab3 s[3]).2.CF.toNat
  let w11fab9 : Word := w11fab3 + s[3]
  let w11fabc : Word := w11fab6 + s[2] + w11fab9c
  let w11fac5 : Word := w11fab9 &&& 0xfffffffffffff
  let w11fad2h : Word := (mulResult w11fac5 0x1000003d10).2
  let w11fad2 : Word := w11fac5 * 0x1000003d10
  let w11fad8c : Word := BitVec.ofNat 64 (addSpec w11fad2 w11fa81).2.CF.toNat
  let w11fad8 : Word := w11fad2 + w11fa81
  let w11fadb : Word := w11fad2h + w11fa81h + w11fad8c
  let w11fadec : Word := BitVec.ofNat 64 (addSpec w11fad8 s[4]).2.CF.toNat
  let w11fade : Word := w11fad8 + s[4]
  let w11fae1 : Word := w11fadb + 0x0 + w11fadec
  let w11fae8 : Word := shldResult 0xc w11fabc w11fab9
  #v[s[0], s[1], s[5], w11fa79, w11fa9e, w11fabc, w11fade, w11fae1, w11fae8]

def squareY11FAED (a : Limbs) (s : Vector Word 9) : Vector Word 10 :=
  let w11faed : Word := s[5] >>> 0x34
  let w11faf4 : Word := s[7] >>> 0x34
  let w11faf8 : Word := shldResult 0xc s[7] s[6]
  let w11fafd : Word := s[6] &&& 0xfffffffffffff
  let w11fb13h : Word := (mulResult a[1] a[1]).2
  let w11fb13 : Word := a[1] * a[1]
  let w11fb1fh : Word := (mulResult s[4] a[3]).2
  let w11fb1f : Word := s[4] * a[3]
  let w11fb25c : Word := BitVec.ofNat 64 (addSpec w11fb1f s[8]).2.CF.toNat
  let w11fb25 : Word := w11fb1f + s[8]
  let w11fb28 : Word := w11faed + w11fb1fh + w11fb25c
  let w11fb2e : Word := w11fb25 &&& 0xfffffffffffff
  let w11fb34h : Word := (mulResult w11fb2e 0x1000003d10).2
  let w11fb34 : Word := w11fb2e * 0x1000003d10
  let w11fb41h : Word := (mulResult s[3] a[2]).2
  let w11fb41 : Word := s[3] * a[2]
  let w11fb47c : Word := BitVec.ofNat 64 (addSpec w11fb41 w11fb13).2.CF.toNat
  let w11fb47 : Word := w11fb41 + w11fb13
  let w11fb4a : Word := w11fb41h + w11fb13h + w11fb47c
  let w11fb4dc : Word := BitVec.ofNat 64 (addSpec w11fb47 w11fb34).2.CF.toNat
  let w11fb4d : Word := w11fb47 + w11fb34
  let w11fb50 : Word := w11fb4a + w11fb34h + w11fb4dc
  let w11fb53c : Word := BitVec.ofNat 64 (addSpec w11fb4d w11faf8).2.CF.toNat
  let w11fb53 : Word := w11fb4d + w11faf8
  #v[s[0], s[1], s[2], w11faf4, w11fafd, w11fb25, w11fb28, w11fb50, w11fb53c, w11fb53]

def squareY11FB56 (s : Vector Word 10) : Limbs :=
  let w11fb56 : Word := s[7] + s[3] + s[8]
  let w11fb59 : Word := shldResult 0xc s[6] s[5]
  let w11fb61 : Word := w11fb56 >>> 0x34
  let w11fb65 : Word := shldResult 0xc w11fb56 s[9]
  let w11fb6a : Word := s[9] &&& 0xfffffffffffff
  let w11fb78h : Word := (mulResult w11fb59 0x1000003d10).2
  let w11fb78 : Word := w11fb59 * 0x1000003d10
  let w11fb8d : Word := s[0] &&& 0xffffffffffffe
  let w11fb90c : Word := BitVec.ofNat 64 (addSpec w11fb8d w11fb78).2.CF.toNat
  let w11fb90 : Word := w11fb8d + w11fb78
  let w11fb93 : Word := w11fb78h + 0x0 + w11fb90c
  let w11fb97c : Word := BitVec.ofNat 64 (addSpec w11fb90 w11fb65).2.CF.toNat
  let w11fb97 : Word := w11fb90 + w11fb65
  let w11fb9a : Word := w11fb93 + w11fb61 + w11fb97c
  let w11fb9d : Word := shldResult 0xc w11fb9a w11fb97
  let w11fba2 : Word := w11fb97 &&& 0xfffffffffffff
  let w11fbb9 : Word := s[1] &&& 0xffffffffffff
  let w11fbbc : Word := w11fbb9 + w11fb9d
  #v[s[2], s[4], w11fb6a, w11fba2, w11fbbc]

def squareY (a : Limbs) : Limbs :=
  let s := squareY11F919H a
  let s := squareY11F998 a s
  let s := squareY11F9FEH a s
  let s := squareY11FA79 a s
  let s := squareY11FAED a s
  squareY11FB56 s

def squareX11FBD1H (a : Limbs) : Vector Word 8 :=
  let w11fbd1h : Word := (mulResult a[3] a[0]).2
  let w11fbd1 : Word := a[3] * a[0]
  let w11fbe7h : Word := (mulResult a[2] a[1]).2
  let w11fbe7 : Word := a[2] * a[1]
  let w11fbedc : Word := BitVec.ofNat 64 (addSpec w11fbe7 w11fbd1).2.CF.toNat
  let w11fbed : Word := w11fbe7 + w11fbd1
  let w11fbf0 : Word := w11fbd1h + w11fbe7h + w11fbedc
  let w11fbf3 : Word := shldResult 0x1 w11fbf0 w11fbed
  let w11fc00h : Word := (mulResult a[4] a[4]).2
  let w11fc00 : Word := a[4] * a[4]
  let w11fc13 : Word := 0xffffffffffffd &&& w11fc00
  let w11fc16h : Word := (mulResult w11fc13 0x1000003d10).2
  let w11fc16 : Word := w11fc13 * 0x1000003d10
  let w11fc19 : Word := w11fbed + w11fbed
  let w11fc1cc : Word := BitVec.ofNat 64 (addSpec w11fc16 w11fc19).2.CF.toNat
  let w11fc1c : Word := w11fc16 + w11fc19
  let w11fc24 : Word := w11fbf3 + w11fc16h + w11fc1cc
  let w11fc27 : Word := shldResult 0xc w11fc00h w11fc00
  let w11fc2f : Word := shldResult 0xc w11fc24 w11fc1c
  let w11fc37h : Word := (mulResult a[2] a[2]).2
  let w11fc37 : Word := a[2] * a[2]
  let w11fc43h : Word := (mulResult w11fc27 0x1000003d10).2
  let w11fc43 : Word := w11fc27 * 0x1000003d10
  let w11fc4fh : Word := (mulResult a[4] a[0]).2
  #v[w11fc1c, w11fc24, w11fc2f, w11fc37h, w11fc37, w11fc43h, w11fc43, w11fc4fh]

def squareX11FC4F (a : Limbs) (s : Vector Word 8) : Vector Word 8 :=
  let w11fc4f : Word := a[4] * a[0]
  let w11fc5eh : Word := (mulResult a[3] a[1]).2
  let w11fc5e : Word := a[3] * a[1]
  let w11fc61 : Word := s[1] >>> 0x34
  let w11fc65c : Word := BitVec.ofNat 64 (addSpec w11fc5e w11fc4f).2.CF.toNat
  let w11fc65 : Word := w11fc5e + w11fc4f
  let w11fc68 : Word := s[7] + w11fc5eh + w11fc65c
  let w11fc6b : Word := shldResult 0x1 w11fc68 w11fc65
  let w11fc70 : Word := w11fc65 + w11fc65
  let w11fc73c : Word := BitVec.ofNat 64 (addSpec s[6] s[4]).2.CF.toNat
  let w11fc73 : Word := s[6] + s[4]
  let w11fc76 : Word := s[5] + s[3] + w11fc73c
  let w11fc79c : Word := BitVec.ofNat 64 (addSpec w11fc70 w11fc73).2.CF.toNat
  let w11fc79 : Word := w11fc70 + w11fc73
  let w11fc7c : Word := w11fc76 + w11fc6b + w11fc79c
  let w11fc7fc : Word := BitVec.ofNat 64 (addSpec w11fc79 s[2]).2.CF.toNat
  let w11fc7f : Word := w11fc79 + s[2]
  let w11fc86 : Word := w11fc7c + w11fc61 + w11fc7fc
  let w11fc8c : Word := shldResult 0xc w11fc86 w11fc7f
  let w11fc91 : Word := w11fc86 >>> 0x34
  let w11fc98 : Word := w11fc7f >>> 0x30
  let w11fc9fh : Word := (mulResult a[0] a[0]).2
  let w11fc9f : Word := a[0] * a[0]
  let w11fcabh : Word := (mulResult a[3] a[2]).2
  #v[s[0], w11fc7f, w11fc8c, w11fc91, w11fc98, w11fc9fh, w11fc9f, w11fcabh]

def squareX11FCAB (a : Limbs) (s : Vector Word 8) : Vector Word 7 :=
  let w11fcab : Word := a[3] * a[2]
  let w11fcbch : Word := (mulResult a[4] a[1]).2
  let w11fcbc : Word := a[4] * a[1]
  let w11fcbf : Word := (BitVec.setWidth 32 s[4]).setWidth 64 &&& 0xf
  let w11fcc3c : Word := BitVec.ofNat 64 (addSpec w11fcbc w11fcab).2.CF.toNat
  let w11fcc3 : Word := w11fcbc + w11fcab
  let w11fcc6 : Word := s[7] + w11fcbch + w11fcc3c
  let w11fcc9 : Word := shldResult 0x1 w11fcc6 w11fcc3
  let w11fcce : Word := w11fcc3 + w11fcc3
  let w11fcd1c : Word := BitVec.ofNat 64 (addSpec w11fcce s[2]).2.CF.toNat
  let w11fcd1 : Word := w11fcce + s[2]
  let w11fcd4 : Word := w11fcc9 + s[3] + w11fcd1c
  let w11fcda : Word := shldResult 0xc w11fcd4 w11fcd1
  let w11fcdf : Word := w11fcd1 <<< 0x4
  let w11fced : Word := w11fcdf &&& 0xfffffffffffff0
  let w11fcf0 : Word := w11fced ||| w11fcbf
  let w11fcf3 : Word := w11fcd4 >>> 0x34
  let w11fd01h : Word := (mulResult w11fcf0 0x1000003d1).2
  let w11fd01 : Word := w11fcf0 * 0x1000003d1
  let w11fd04c : Word := BitVec.ofNat 64 (addSpec w11fd01 s[6]).2.CF.toNat
  let w11fd04 : Word := w11fd01 + s[6]
  let w11fd0c : Word := s[5] + w11fd01h + w11fd04c
  let w11fd0f : Word := shldResult 0xc w11fd0c w11fd04
  let w11fd14 : Word := a[0] + a[0]
  #v[s[0], s[1], w11fcda, w11fcf3, w11fd04, w11fd0f, w11fd14]

def squareX11FD1DH (a : Limbs) (s : Vector Word 7) : Vector Word 9 :=
  let w11fd1dh : Word := (mulResult s[6] a[1]).2
  let w11fd1d : Word := s[6] * a[1]
  let w11fd2ch : Word := (mulResult a[3] a[3]).2
  let w11fd2c : Word := a[3] * a[3]
  let w11fd35 : Word := a[4] + a[4]
  let w11fd3bh : Word := (mulResult w11fd35 a[2]).2
  let w11fd3b : Word := w11fd35 * a[2]
  let w11fd41c : Word := BitVec.ofNat 64 (addSpec w11fd3b w11fd2c).2.CF.toNat
  let w11fd41 : Word := w11fd3b + w11fd2c
  let w11fd44 : Word := w11fd2ch + w11fd3bh + w11fd41c
  let w11fd47c : Word := BitVec.ofNat 64 (addSpec w11fd41 s[2]).2.CF.toNat
  let w11fd47 : Word := w11fd41 + s[2]
  let w11fd4a : Word := w11fd44 + s[3] + w11fd47c
  let w11fd5a : Word := w11fd47 &&& 0xfffffffffffff
  let w11fd67h : Word := (mulResult w11fd5a 0x1000003d10).2
  let w11fd67 : Word := w11fd5a * 0x1000003d10
  let w11fd6dc : Word := BitVec.ofNat 64 (addSpec w11fd67 w11fd1d).2.CF.toNat
  let w11fd6d : Word := w11fd67 + w11fd1d
  let w11fd70 : Word := w11fd1dh + w11fd67h + w11fd6dc
  let w11fd73c : Word := BitVec.ofNat 64 (addSpec w11fd6d s[5]).2.CF.toNat
  let w11fd73 : Word := w11fd6d + s[5]
  let w11fd76 : Word := w11fd70 + 0x0 + w11fd73c
  let w11fd7d : Word := shldResult 0xc w11fd4a w11fd47
  let w11fd82 : Word := w11fd4a >>> 0x34
  #v[s[0], s[1], s[4], s[6], w11fd35, w11fd73, w11fd76, w11fd7d, w11fd82]

def squareX11FD89 (a : Limbs) (s : Vector Word 9) : Vector Word 7 :=
  let w11fd89 : Word := s[6] >>> 0x34
  let w11fd8d : Word := shldResult 0xc s[6] s[5]
  let w11fd97h : Word := (mulResult a[1] a[1]).2
  let w11fd97 : Word := a[1] * a[1]
  let w11fda3h : Word := (mulResult s[4] a[3]).2
  let w11fda3 : Word := s[4] * a[3]
  let w11fda9c : Word := BitVec.ofNat 64 (addSpec w11fda3 s[7]).2.CF.toNat
  let w11fda9 : Word := w11fda3 + s[7]
  let w11fdac : Word := s[8] + w11fda3h + w11fda9c
  let w11fdb2 : Word := w11fda9 &&& 0xfffffffffffff
  let w11fdb8h : Word := (mulResult w11fdb2 0x1000003d10).2
  let w11fdb8 : Word := w11fdb2 * 0x1000003d10
  let w11fdc6h : Word := (mulResult s[3] a[2]).2
  let w11fdc6 : Word := s[3] * a[2]
  let w11fdc9c : Word := BitVec.ofNat 64 (addSpec w11fdc6 w11fd97).2.CF.toNat
  let w11fdc9 : Word := w11fdc6 + w11fd97
  let w11fdcc : Word := w11fd97h + w11fdc6h + w11fdc9c
  let w11fdcfc : Word := BitVec.ofNat 64 (addSpec w11fdc9 w11fdb8).2.CF.toNat
  let w11fdcf : Word := w11fdc9 + w11fdb8
  let w11fdd2 : Word := w11fdcc + w11fdb8h + w11fdcfc
  let w11fdd5c : Word := BitVec.ofNat 64 (addSpec w11fdcf w11fd8d).2.CF.toNat
  let w11fdd5 : Word := w11fdcf + w11fd8d
  let w11fddb : Word := w11fdd2 + w11fd89 + w11fdd5c
  let w11fdde : Word := shldResult 0xc w11fdac w11fda9
  #v[s[0], s[1], s[2], s[5], w11fdd5, w11fddb, w11fdde]

def squareX11FDF2 (s : Vector Word 7) : Limbs :=
  let w11fdf2 : Word := s[0] &&& 0xffffffffffffe
  let w11fdf8 : Word := s[5] >>> 0x34
  let w11fdfc : Word := shldResult 0xc s[5] s[4]
  let w11fe04h : Word := (mulResult s[6] 0x1000003d10).2
  let w11fe04 : Word := s[6] * 0x1000003d10
  let w11fe0dc : Word := BitVec.ofNat 64 (addSpec w11fe04 w11fdf2).2.CF.toNat
  let w11fe0d : Word := w11fe04 + w11fdf2
  let w11fe10 : Word := w11fe04h + 0x0 + w11fe0dc
  let w11fe14c : Word := BitVec.ofNat 64 (addSpec w11fe0d w11fdfc).2.CF.toNat
  let w11fe14 : Word := w11fe0d + w11fdfc
  let w11fe17 : Word := w11fdf8 + w11fe10 + w11fe14c
  let w11fe1a : Word := shldResult 0xc w11fe17 w11fe14
  let w11fe2d : Word := s[1] &&& 0xffffffffffff
  let w11fe30 : Word := w11fe2d + w11fe1a
  let w11fe3c : Word := s[2] &&& 0xfffffffffffff
  let w11fe47 : Word := s[3] &&& 0xfffffffffffff
  let w11fe4f : Word := s[4] &&& 0xfffffffffffff
  let w11fe57 : Word := w11fe14 &&& 0xfffffffffffff
  #v[w11fe3c, w11fe47, w11fe4f, w11fe57, w11fe30]

def squareX (a : Limbs) : Limbs :=
  let s := squareX11FBD1H a
  let s := squareX11FC4F a s
  let s := squareX11FCAB a s
  let s := squareX11FD1DH a s
  let s := squareX11FD89 a s
  squareX11FDF2 s

end K256.Proofs.Sec1.Affine.Uncompressed
