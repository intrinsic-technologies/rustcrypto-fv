import Sha2.Proofs.Common.SHA256.Instances.Absorb.Compose
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Fit
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TraitFirst

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256.Absorb

def Loop.stagePC (loop : Loop) (v : Wrapper.Variant := .sha256) : Stage → BitVec 64 :=
  match loop with
  | .resetDiscarded => fun
      | .prepare => (if v = .sha224 then 0x100e12 else 0x102a42)
      | .smallBranch => (if v = .sha224 then 0x100e20 else 0x102a50)
      | .emptyTest => (if v = .sha224 then 0x100e22 else 0x102a52)
      | .emptyBranch => (if v = .sha224 then 0x100e25 else 0x102a55)
      | .smallSetup => (if v = .sha224 then 0x100dd0 else 0x102a00)
      | .smallCall => (if v = .sha224 then 0x100dda else 0x102a0a)
      | .smallLength => (if v = .sha224 then 0x100de0 else 0x102a10)
      | .smallStore => (if v = .sha224 then 0x100de3 else 0x102a13)
      | .fillSetup => (if v = .sha224 then 0x100e2b else 0x102a5b)
      | .fillCall => (if v = .sha224 then 0x100e36 else 0x102a66)
      | .increment => (if v = .sha224 then 0x100e3c else 0x102a6c)
      | .fillCompressSetup => (if v = .sha224 then 0x100e41 else 0x102a71)
      | .fillCompressCall => (if v = .sha224 then 0x100e4e else 0x102a7e)
      | .clearTail => (if v = .sha224 then 0x100e53 else 0x102a83)
      | .restoreSource => (if v = .sha224 then 0x100e58 else 0x102a88)
      | .count => (if v = .sha224 then 0x100e5b else 0x102a8b)
      | .countBranch => (if v = .sha224 then 0x100e62 else 0x102a92)
      | .addBlocks => (if v = .sha224 then 0x100e64 else 0x102a94)
      | .bulkSetup => (if v = .sha224 then 0x100e69 else 0x102a99)
      | .bulkCall => (if v = .sha224 then 0x100e71 else 0x102aa1)
      | .bulkRestore => (if v = .sha224 then 0x100e76 else 0x102aa6)
      | .splitTail => (if v = .sha224 then 0x100e76 else 0x102aa6)
      | .tailStore => (if v = .sha224 then 0x100e8c else 0x102abc)
      | .tailSetup => (if v = .sha224 then 0x100e90 else 0x102ac0)
      | .tailCall => (if v = .sha224 then 0x100e99 else 0x102ac9)
      | .emptySetup => (if v = .sha224 then 0x100ead else 0x102add)
  | .resetFirst => fun
      | .prepare => (if v = .sha224 then 0x100f4f else 0x102b7f)
      | .smallBranch => (if v = .sha224 then 0x100f5d else 0x102b8d)
      | .emptyTest => (if v = .sha224 then 0x100f5f else 0x102b8f)
      | .emptyBranch => (if v = .sha224 then 0x100f62 else 0x102b92)
      | .smallSetup => (if v = .sha224 then 0x100f10 else 0x102b40)
      | .smallCall => (if v = .sha224 then 0x100f17 else 0x102b47)
      | .smallLength => (if v = .sha224 then 0x100f1d else 0x102b4d)
      | .smallStore => (if v = .sha224 then 0x100f20 else 0x102b50)
      | .fillSetup => (if v = .sha224 then 0x100f68 else 0x102b98)
      | .fillCall => (if v = .sha224 then 0x100f70 else 0x102ba0)
      | .increment => (if v = .sha224 then 0x100f76 else 0x102ba6)
      | .fillCompressSetup => (if v = .sha224 then 0x100f7b else 0x102bab)
      | .fillCompressCall => (if v = .sha224 then 0x100f88 else 0x102bb8)
      | .clearTail => (if v = .sha224 then 0x100f8d else 0x102bbd)
      | .restoreSource => (if v = .sha224 then 0x100f92 else 0x102bc2)
      | .count => (if v = .sha224 then 0x100f95 else 0x102bc5)
      | .countBranch => (if v = .sha224 then 0x100f9c else 0x102bcc)
      | .addBlocks => (if v = .sha224 then 0x100f9e else 0x102bce)
      | .bulkSetup => (if v = .sha224 then 0x100fa3 else 0x102bd3)
      | .bulkCall => (if v = .sha224 then 0x100fab else 0x102bdb)
      | .bulkRestore => (if v = .sha224 then 0x100fb0 else 0x102be0)
      | .splitTail => (if v = .sha224 then 0x100fb3 else 0x102be3)
      | .tailStore => (if v = .sha224 then 0x100fc9 else 0x102bf9)
      | .tailSetup => (if v = .sha224 then 0x100fce else 0x102bfe)
      | .tailCall => (if v = .sha224 then 0x100fd4 else 0x102c04)
      | .emptySetup => (if v = .sha224 then 0x100fe8 else 0x102c18)
  | .resetLast => fun
      | .prepare => (if v = .sha224 then 0x10125b else 0x102e9b)
      | .smallBranch => (if v = .sha224 then 0x101269 else 0x102ea9)
      | .emptyTest => (if v = .sha224 then 0x10126b else 0x102eab)
      | .emptyBranch => (if v = .sha224 then 0x10126e else 0x102eae)
      | .smallSetup => (if v = .sha224 then 0x101220 else 0x102e60)
      | .smallCall => (if v = .sha224 then 0x101227 else 0x102e67)
      | .smallLength => (if v = .sha224 then 0x101229 else 0x102e69)
      | .smallStore => (if v = .sha224 then 0x10122c else 0x102e6c)
      | .fillSetup => (if v = .sha224 then 0x101270 else 0x102eb0)
      | .fillCall => (if v = .sha224 then 0x101278 else 0x102eb8)
      | .increment => (if v = .sha224 then 0x10127a else 0x102eba)
      | .fillCompressSetup => (if v = .sha224 then 0x10127f else 0x102ebf)
      | .fillCompressCall => (if v = .sha224 then 0x10128c else 0x102ecc)
      | .clearTail => (if v = .sha224 then 0x101291 else 0x102ed1)
      | .restoreSource => (if v = .sha224 then 0x101296 else 0x102ed6)
      | .count => (if v = .sha224 then 0x101299 else 0x102ed9)
      | .countBranch => (if v = .sha224 then 0x1012a0 else 0x102ee0)
      | .addBlocks => (if v = .sha224 then 0x1012a2 else 0x102ee2)
      | .bulkSetup => (if v = .sha224 then 0x1012a7 else 0x102ee7)
      | .bulkCall => (if v = .sha224 then 0x1012af else 0x102eef)
      | .bulkRestore => (if v = .sha224 then 0x1012b4 else 0x102ef4)
      | .splitTail => (if v = .sha224 then 0x1012b7 else 0x102ef7)
      | .tailStore => (if v = .sha224 then 0x1012cd else 0x102f0d)
      | .tailSetup => (if v = .sha224 then 0x1012d2 else 0x102f12)
      | .tailCall => (if v = .sha224 then 0x1012d8 else 0x102f18)
      | .emptySetup => (if v = .sha224 then 0x1012e8 else 0x102f28)
  | .finalizeFirst => fun
      | .prepare => (if v = .sha224 then 0x100726 else 0x102336)
      | .smallBranch => (if v = .sha224 then 0x100734 else 0x102344)
      | .emptyTest => (if v = .sha224 then 0x100736 else 0x102346)
      | .emptyBranch => (if v = .sha224 then 0x100739 else 0x102349)
      | .smallSetup => (if v = .sha224 then 0x1006e0 else 0x1022f0)
      | .smallCall => (if v = .sha224 then 0x1006ee else 0x1022fe)
      | .smallLength => (if v = .sha224 then 0x1006f4 else 0x102304)
      | .smallStore => (if v = .sha224 then 0x1006f7 else 0x102307)
      | .fillSetup => (if v = .sha224 then 0x10073f else 0x10234f)
      | .fillCall => (if v = .sha224 then 0x10074e else 0x10235e)
      | .increment => (if v = .sha224 then 0x100754 else 0x102364)
      | .fillCompressSetup => (if v = .sha224 then 0x100759 else 0x102369)
      | .fillCompressCall => (if v = .sha224 then 0x100768 else 0x102378)
      | .clearTail => (if v = .sha224 then 0x10076d else 0x10237d)
      | .restoreSource => (if v = .sha224 then 0x100772 else 0x102382)
      | .count => (if v = .sha224 then 0x100775 else 0x102385)
      | .countBranch => (if v = .sha224 then 0x10077c else 0x10238c)
      | .addBlocks => (if v = .sha224 then 0x10077e else 0x10238e)
      | .bulkSetup => (if v = .sha224 then 0x100783 else 0x102393)
      | .bulkCall => (if v = .sha224 then 0x10078b else 0x10239b)
      | .bulkRestore => (if v = .sha224 then 0x100790 else 0x1023a0)
      | .splitTail => (if v = .sha224 then 0x100790 else 0x1023a0)
      | .tailStore => (if v = .sha224 then 0x1007a6 else 0x1023b6)
      | .tailSetup => (if v = .sha224 then 0x1007aa else 0x1023ba)
      | .tailCall => (if v = .sha224 then 0x1007b5 else 0x1023c5)
      | .emptySetup => (if v = .sha224 then 0x1007c9 else 0x1023d9)
  | .finalizeLast => fun
      | .prepare => (if v = .sha224 then 0x100a3f else 0x10265f)
      | .smallBranch => (if v = .sha224 then 0x100a4d else 0x10266d)
      | .emptyTest => (if v = .sha224 then 0x100a4f else 0x10266f)
      | .emptyBranch => (if v = .sha224 then 0x100a52 else 0x102672)
      | .smallSetup => (if v = .sha224 then 0x100a00 else 0x102620)
      | .smallCall => (if v = .sha224 then 0x100a0b else 0x10262b)
      | .smallLength => (if v = .sha224 then 0x100a0e else 0x10262e)
      | .smallStore => (if v = .sha224 then 0x100a11 else 0x102631)
      | .fillSetup => (if v = .sha224 then 0x100a58 else 0x102678)
      | .fillCall => (if v = .sha224 then 0x100a64 else 0x102684)
      | .increment => (if v = .sha224 then 0x100a67 else 0x102687)
      | .fillCompressSetup => (if v = .sha224 then 0x100a6c else 0x10268c)
      | .fillCompressCall => (if v = .sha224 then 0x100a7b else 0x10269b)
      | .clearTail => (if v = .sha224 then 0x100a80 else 0x1026a0)
      | .restoreSource => (if v = .sha224 then 0x100a85 else 0x1026a5)
      | .count => (if v = .sha224 then 0x100a88 else 0x1026a8)
      | .countBranch => (if v = .sha224 then 0x100a8f else 0x1026af)
      | .addBlocks => (if v = .sha224 then 0x100a91 else 0x1026b1)
      | .bulkSetup => (if v = .sha224 then 0x100a96 else 0x1026b6)
      | .bulkCall => (if v = .sha224 then 0x100a9e else 0x1026be)
      | .bulkRestore => (if v = .sha224 then 0x100aa3 else 0x1026c3)
      | .splitTail => (if v = .sha224 then 0x100aa6 else 0x1026c6)
      | .tailStore => (if v = .sha224 then 0x100abc else 0x1026dc)
      | .tailSetup => (if v = .sha224 then 0x100ac1 else 0x1026e1)
      | .tailCall => (if v = .sha224 then 0x100ac9 else 0x1026e9)
      | .emptySetup => (if v = .sha224 then 0x100ada else 0x1026fa)
  | .traitFirst => fun
      | .prepare => (if v = .sha224 then 0x1015eb else 0x10323b)
      | .smallBranch => (if v = .sha224 then 0x1015f9 else 0x103249)
      | .emptyTest => (if v = .sha224 then 0x1015fb else 0x10324b)
      | .emptyBranch => (if v = .sha224 then 0x1015fe else 0x10324e)
      | .smallSetup => (if v = .sha224 then 0x101580 else 0x1031d0)
      | .smallCall => (if v = .sha224 then 0x10158a else 0x1031da)
      | .smallLength => (if v = .sha224 then 0x101590 else 0x1031e0)
      | .smallStore => (if v = .sha224 then 0x101593 else 0x1031e3)
      | .fillSetup => (if v = .sha224 then 0x101600 else 0x103250)
      | .fillCall => (if v = .sha224 then 0x10160b else 0x10325b)
      | .increment => (if v = .sha224 then 0x101611 else 0x103261)
      | .fillCompressSetup => (if v = .sha224 then 0x101616 else 0x103266)
      | .fillCompressCall => (if v = .sha224 then 0x101626 else 0x103276)
      | .clearTail => (if v = .sha224 then 0x10162b else 0x10327b)
      | .restoreSource => (if v = .sha224 then 0x101630 else 0x103280)
      | .count => (if v = .sha224 then 0x101633 else 0x103283)
      | .countBranch => (if v = .sha224 then 0x10163a else 0x10328a)
      | .addBlocks => (if v = .sha224 then 0x10163c else 0x10328c)
      | .bulkSetup => (if v = .sha224 then 0x101641 else 0x103291)
      | .bulkCall => (if v = .sha224 then 0x101649 else 0x103299)
      | .bulkRestore => (if v = .sha224 then 0x10164e else 0x10329e)
      | .splitTail => (if v = .sha224 then 0x10164e else 0x10329e)
      | .tailStore => (if v = .sha224 then 0x101665 else 0x1032b5)
      | .tailSetup => (if v = .sha224 then 0x10166a else 0x1032ba)
      | .tailCall => (if v = .sha224 then 0x101673 else 0x1032c3)
      | .emptySetup => (if v = .sha224 then 0x10167e else 0x1032ce)
  | .traitLast => fun
      | .prepare => (if v = .sha224 then 0x10195a else 0x1035ba)
      | .smallBranch => (if v = .sha224 then 0x101968 else 0x1035c8)
      | .emptyTest => (if v = .sha224 then 0x10196a else 0x1035ca)
      | .emptyBranch => (if v = .sha224 then 0x10196d else 0x1035cd)
      | .smallSetup => (if v = .sha224 then 0x1018f0 else 0x103550)
      | .smallCall => (if v = .sha224 then 0x1018fa else 0x10355a)
      | .smallLength => (if v = .sha224 then 0x101900 else 0x103560)
      | .smallStore => (if v = .sha224 then 0x101903 else 0x103563)
      | .fillSetup => (if v = .sha224 then 0x10196f else 0x1035cf)
      | .fillCall => (if v = .sha224 then 0x10197a else 0x1035da)
      | .increment => (if v = .sha224 then 0x101980 else 0x1035e0)
      | .fillCompressSetup => (if v = .sha224 then 0x101985 else 0x1035e5)
      | .fillCompressCall => (if v = .sha224 then 0x101995 else 0x1035f5)
      | .clearTail => (if v = .sha224 then 0x10199a else 0x1035fa)
      | .restoreSource => (if v = .sha224 then 0x10199f else 0x1035ff)
      | .count => (if v = .sha224 then 0x1019a2 else 0x103602)
      | .countBranch => (if v = .sha224 then 0x1019a9 else 0x103609)
      | .addBlocks => (if v = .sha224 then 0x1019ab else 0x10360b)
      | .bulkSetup => (if v = .sha224 then 0x1019b0 else 0x103610)
      | .bulkCall => (if v = .sha224 then 0x1019b8 else 0x103618)
      | .bulkRestore => (if v = .sha224 then 0x1019bd else 0x10361d)
      | .splitTail => (if v = .sha224 then 0x1019bd else 0x10361d)
      | .tailStore => (if v = .sha224 then 0x1019d4 else 0x103634)
      | .tailSetup => (if v = .sha224 then 0x1019d9 else 0x103639)
      | .tailCall => (if v = .sha224 then 0x1019e2 else 0x103642)
      | .emptySetup => (if v = .sha224 then 0x1019ed else 0x10364d)

def Loop.stageSites (loop : Loop) (v : Wrapper.Variant := .sha256) : Stage → List (BitVec 64) :=
  match loop with
  | .resetDiscarded => fun
      | .prepare => [(if v = .sha224 then 0x100e12 else 0x102a42)]
      | .smallBranch => [(if v = .sha224 then 0x100e20 else 0x102a50)]
      | .emptyTest => [(if v = .sha224 then 0x100e22 else 0x102a52)]
      | .emptyBranch => [(if v = .sha224 then 0x100e25 else 0x102a55)]
      | .smallSetup => [(if v = .sha224 then 0x100dd0 else 0x102a00), (if v = .sha224 then 0x100dd4 else 0x102a04), (if v = .sha224 then 0x100dd7 else 0x102a07)]
      | .smallCall => []
      | .smallLength => [(if v = .sha224 then 0x100de0 else 0x102a10)]
      | .smallStore => [(if v = .sha224 then 0x100de3 else 0x102a13)]
      | .fillSetup => [(if v = .sha224 then 0x100e2b else 0x102a5b), (if v = .sha224 then 0x100e2f else 0x102a5f), (if v = .sha224 then 0x100e33 else 0x102a63)]
      | .fillCall => []
      | .increment => [(if v = .sha224 then 0x100e3c else 0x102a6c)]
      | .fillCompressSetup => [(if v = .sha224 then 0x100e41 else 0x102a71), (if v = .sha224 then 0x100e46 else 0x102a76), (if v = .sha224 then 0x100e4b else 0x102a7b)]
      | .fillCompressCall => []
      | .clearTail => [(if v = .sha224 then 0x100e53 else 0x102a83)]
      | .restoreSource => [(if v = .sha224 then 0x100e58 else 0x102a88)]
      | .count => [(if v = .sha224 then 0x100e5b else 0x102a8b)]
      | .countBranch => [(if v = .sha224 then 0x100e62 else 0x102a92)]
      | .addBlocks => [(if v = .sha224 then 0x100e64 else 0x102a94)]
      | .bulkSetup => [(if v = .sha224 then 0x100e69 else 0x102a99), (if v = .sha224 then 0x100e6e else 0x102a9e)]
      | .bulkCall => []
      | .bulkRestore => []
      | .splitTail => [(if v = .sha224 then 0x100e76 else 0x102aa6)]
      | .tailStore => [(if v = .sha224 then 0x100e8c else 0x102abc)]
      | .tailSetup => [(if v = .sha224 then 0x100e90 else 0x102ac0), (if v = .sha224 then 0x100e93 else 0x102ac3), (if v = .sha224 then 0x100e96 else 0x102ac6)]
      | .tailCall => []
      | .emptySetup => [(if v = .sha224 then 0x100ead else 0x102add), (if v = .sha224 then 0x100eb0 else 0x102ae0), (if v = .sha224 then 0x100eb7 else 0x102ae7), (if v = .sha224 then 0x100eb9 else 0x102ae9)]
  | .resetFirst => fun
      | .prepare => [(if v = .sha224 then 0x100f4f else 0x102b7f)]
      | .smallBranch => [(if v = .sha224 then 0x100f5d else 0x102b8d)]
      | .emptyTest => [(if v = .sha224 then 0x100f5f else 0x102b8f)]
      | .emptyBranch => [(if v = .sha224 then 0x100f62 else 0x102b92)]
      | .smallSetup => [(if v = .sha224 then 0x100f10 else 0x102b40), (if v = .sha224 then 0x100f14 else 0x102b44)]
      | .smallCall => []
      | .smallLength => [(if v = .sha224 then 0x100f1d else 0x102b4d)]
      | .smallStore => [(if v = .sha224 then 0x100f20 else 0x102b50)]
      | .fillSetup => [(if v = .sha224 then 0x100f68 else 0x102b98), (if v = .sha224 then 0x100f6c else 0x102b9c)]
      | .fillCall => []
      | .increment => [(if v = .sha224 then 0x100f76 else 0x102ba6)]
      | .fillCompressSetup => [(if v = .sha224 then 0x100f7b else 0x102bab), (if v = .sha224 then 0x100f80 else 0x102bb0), (if v = .sha224 then 0x100f85 else 0x102bb5)]
      | .fillCompressCall => []
      | .clearTail => [(if v = .sha224 then 0x100f8d else 0x102bbd)]
      | .restoreSource => [(if v = .sha224 then 0x100f92 else 0x102bc2)]
      | .count => [(if v = .sha224 then 0x100f95 else 0x102bc5)]
      | .countBranch => [(if v = .sha224 then 0x100f9c else 0x102bcc)]
      | .addBlocks => [(if v = .sha224 then 0x100f9e else 0x102bce)]
      | .bulkSetup => [(if v = .sha224 then 0x100fa3 else 0x102bd3), (if v = .sha224 then 0x100fa8 else 0x102bd8)]
      | .bulkCall => []
      | .bulkRestore => [(if v = .sha224 then 0x100fb0 else 0x102be0)]
      | .splitTail => [(if v = .sha224 then 0x100fb3 else 0x102be3)]
      | .tailStore => [(if v = .sha224 then 0x100fc9 else 0x102bf9)]
      | .tailSetup => [(if v = .sha224 then 0x100fce else 0x102bfe), (if v = .sha224 then 0x100fd1 else 0x102c01)]
      | .tailCall => []
      | .emptySetup => [(if v = .sha224 then 0x100fe8 else 0x102c18), (if v = .sha224 then 0x100feb else 0x102c1b), (if v = .sha224 then 0x100ff2 else 0x102c22), (if v = .sha224 then 0x100ff4 else 0x102c24)]
  | .resetLast => fun
      | .prepare => [(if v = .sha224 then 0x10125b else 0x102e9b)]
      | .smallBranch => [(if v = .sha224 then 0x101269 else 0x102ea9)]
      | .emptyTest => [(if v = .sha224 then 0x10126b else 0x102eab)]
      | .emptyBranch => [(if v = .sha224 then 0x10126e else 0x102eae)]
      | .smallSetup => [(if v = .sha224 then 0x101220 else 0x102e60), (if v = .sha224 then 0x101224 else 0x102e64)]
      | .smallCall => []
      | .smallLength => [(if v = .sha224 then 0x101229 else 0x102e69)]
      | .smallStore => [(if v = .sha224 then 0x10122c else 0x102e6c)]
      | .fillSetup => [(if v = .sha224 then 0x101270 else 0x102eb0), (if v = .sha224 then 0x101274 else 0x102eb4)]
      | .fillCall => []
      | .increment => [(if v = .sha224 then 0x10127a else 0x102eba)]
      | .fillCompressSetup => [(if v = .sha224 then 0x10127f else 0x102ebf), (if v = .sha224 then 0x101284 else 0x102ec4), (if v = .sha224 then 0x101289 else 0x102ec9)]
      | .fillCompressCall => []
      | .clearTail => [(if v = .sha224 then 0x101291 else 0x102ed1)]
      | .restoreSource => [(if v = .sha224 then 0x101296 else 0x102ed6)]
      | .count => [(if v = .sha224 then 0x101299 else 0x102ed9)]
      | .countBranch => [(if v = .sha224 then 0x1012a0 else 0x102ee0)]
      | .addBlocks => [(if v = .sha224 then 0x1012a2 else 0x102ee2)]
      | .bulkSetup => [(if v = .sha224 then 0x1012a7 else 0x102ee7), (if v = .sha224 then 0x1012ac else 0x102eec)]
      | .bulkCall => []
      | .bulkRestore => [(if v = .sha224 then 0x1012b4 else 0x102ef4)]
      | .splitTail => [(if v = .sha224 then 0x1012b7 else 0x102ef7)]
      | .tailStore => [(if v = .sha224 then 0x1012cd else 0x102f0d)]
      | .tailSetup => [(if v = .sha224 then 0x1012d2 else 0x102f12), (if v = .sha224 then 0x1012d5 else 0x102f15)]
      | .tailCall => []
      | .emptySetup => [(if v = .sha224 then 0x1012e8 else 0x102f28), (if v = .sha224 then 0x1012eb else 0x102f2b), (if v = .sha224 then 0x1012f2 else 0x102f32), (if v = .sha224 then 0x1012f4 else 0x102f34)]
  | .finalizeFirst => fun
      | .prepare => [(if v = .sha224 then 0x100726 else 0x102336)]
      | .smallBranch => [(if v = .sha224 then 0x100734 else 0x102344)]
      | .emptyTest => [(if v = .sha224 then 0x100736 else 0x102346)]
      | .emptyBranch => [(if v = .sha224 then 0x100739 else 0x102349)]
      | .smallSetup => [(if v = .sha224 then 0x1006e0 else 0x1022f0), (if v = .sha224 then 0x1006e4 else 0x1022f4), (if v = .sha224 then 0x1006e8 else 0x1022f8), (if v = .sha224 then 0x1006eb else 0x1022fb)]
      | .smallCall => []
      | .smallLength => [(if v = .sha224 then 0x1006f4 else 0x102304)]
      | .smallStore => [(if v = .sha224 then 0x1006f7 else 0x102307)]
      | .fillSetup => [(if v = .sha224 then 0x10073f else 0x10234f), (if v = .sha224 then 0x100743 else 0x102353), (if v = .sha224 then 0x100747 else 0x102357), (if v = .sha224 then 0x10074b else 0x10235b)]
      | .fillCall => []
      | .increment => [(if v = .sha224 then 0x100754 else 0x102364)]
      | .fillCompressSetup => [(if v = .sha224 then 0x100759 else 0x102369), (if v = .sha224 then 0x10075e else 0x10236e), (if v = .sha224 then 0x100763 else 0x102373)]
      | .fillCompressCall => []
      | .clearTail => [(if v = .sha224 then 0x10076d else 0x10237d)]
      | .restoreSource => [(if v = .sha224 then 0x100772 else 0x102382)]
      | .count => [(if v = .sha224 then 0x100775 else 0x102385)]
      | .countBranch => [(if v = .sha224 then 0x10077c else 0x10238c)]
      | .addBlocks => [(if v = .sha224 then 0x10077e else 0x10238e)]
      | .bulkSetup => [(if v = .sha224 then 0x100783 else 0x102393), (if v = .sha224 then 0x100788 else 0x102398)]
      | .bulkCall => []
      | .bulkRestore => []
      | .splitTail => [(if v = .sha224 then 0x100790 else 0x1023a0)]
      | .tailStore => [(if v = .sha224 then 0x1007a6 else 0x1023b6)]
      | .tailSetup => [(if v = .sha224 then 0x1007aa else 0x1023ba), (if v = .sha224 then 0x1007af else 0x1023bf), (if v = .sha224 then 0x1007b2 else 0x1023c2)]
      | .tailCall => []
      | .emptySetup => [(if v = .sha224 then 0x1007c9 else 0x1023d9), (if v = .sha224 then 0x1007cc else 0x1023dc), (if v = .sha224 then 0x1007d3 else 0x1023e3), (if v = .sha224 then 0x1007d5 else 0x1023e5)]
  | .finalizeLast => fun
      | .prepare => [(if v = .sha224 then 0x100a3f else 0x10265f)]
      | .smallBranch => [(if v = .sha224 then 0x100a4d else 0x10266d)]
      | .emptyTest => [(if v = .sha224 then 0x100a4f else 0x10266f)]
      | .emptyBranch => [(if v = .sha224 then 0x100a52 else 0x102672)]
      | .smallSetup => [(if v = .sha224 then 0x100a00 else 0x102620), (if v = .sha224 then 0x100a04 else 0x102624), (if v = .sha224 then 0x100a08 else 0x102628)]
      | .smallCall => []
      | .smallLength => [(if v = .sha224 then 0x100a0e else 0x10262e)]
      | .smallStore => [(if v = .sha224 then 0x100a11 else 0x102631)]
      | .fillSetup => [(if v = .sha224 then 0x100a58 else 0x102678), (if v = .sha224 then 0x100a5c else 0x10267c), (if v = .sha224 then 0x100a60 else 0x102680)]
      | .fillCall => []
      | .increment => [(if v = .sha224 then 0x100a67 else 0x102687)]
      | .fillCompressSetup => [(if v = .sha224 then 0x100a6c else 0x10268c), (if v = .sha224 then 0x100a71 else 0x102691), (if v = .sha224 then 0x100a76 else 0x102696)]
      | .fillCompressCall => []
      | .clearTail => [(if v = .sha224 then 0x100a80 else 0x1026a0)]
      | .restoreSource => [(if v = .sha224 then 0x100a85 else 0x1026a5)]
      | .count => [(if v = .sha224 then 0x100a88 else 0x1026a8)]
      | .countBranch => [(if v = .sha224 then 0x100a8f else 0x1026af)]
      | .addBlocks => [(if v = .sha224 then 0x100a91 else 0x1026b1)]
      | .bulkSetup => [(if v = .sha224 then 0x100a96 else 0x1026b6), (if v = .sha224 then 0x100a9b else 0x1026bb)]
      | .bulkCall => []
      | .bulkRestore => [(if v = .sha224 then 0x100aa3 else 0x1026c3)]
      | .splitTail => [(if v = .sha224 then 0x100aa6 else 0x1026c6)]
      | .tailStore => [(if v = .sha224 then 0x100abc else 0x1026dc)]
      | .tailSetup => [(if v = .sha224 then 0x100ac1 else 0x1026e1), (if v = .sha224 then 0x100ac6 else 0x1026e6)]
      | .tailCall => []
      | .emptySetup => [(if v = .sha224 then 0x100ada else 0x1026fa), (if v = .sha224 then 0x100add else 0x1026fd), (if v = .sha224 then 0x100ae4 else 0x102704), (if v = .sha224 then 0x100ae6 else 0x102706)]
  | .traitFirst => fun
      | .prepare => [(if v = .sha224 then 0x1015eb else 0x10323b)]
      | .smallBranch => [(if v = .sha224 then 0x1015f9 else 0x103249)]
      | .emptyTest => [(if v = .sha224 then 0x1015fb else 0x10324b)]
      | .emptyBranch => [(if v = .sha224 then 0x1015fe else 0x10324e)]
      | .smallSetup => [(if v = .sha224 then 0x101580 else 0x1031d0), (if v = .sha224 then 0x101584 else 0x1031d4), (if v = .sha224 then 0x101587 else 0x1031d7)]
      | .smallCall => []
      | .smallLength => [(if v = .sha224 then 0x101590 else 0x1031e0)]
      | .smallStore => [(if v = .sha224 then 0x101593 else 0x1031e3)]
      | .fillSetup => [(if v = .sha224 then 0x101600 else 0x103250), (if v = .sha224 then 0x101604 else 0x103254), (if v = .sha224 then 0x101608 else 0x103258)]
      | .fillCall => []
      | .increment => [(if v = .sha224 then 0x101611 else 0x103261)]
      | .fillCompressSetup => [(if v = .sha224 then 0x101616 else 0x103266), (if v = .sha224 then 0x10161b else 0x10326b), (if v = .sha224 then 0x101620 else 0x103270), (if v = .sha224 then 0x101623 else 0x103273)]
      | .fillCompressCall => []
      | .clearTail => [(if v = .sha224 then 0x10162b else 0x10327b)]
      | .restoreSource => [(if v = .sha224 then 0x101630 else 0x103280)]
      | .count => [(if v = .sha224 then 0x101633 else 0x103283)]
      | .countBranch => [(if v = .sha224 then 0x10163a else 0x10328a)]
      | .addBlocks => [(if v = .sha224 then 0x10163c else 0x10328c)]
      | .bulkSetup => [(if v = .sha224 then 0x101641 else 0x103291), (if v = .sha224 then 0x101646 else 0x103296)]
      | .bulkCall => []
      | .bulkRestore => []
      | .splitTail => [(if v = .sha224 then 0x10164e else 0x10329e)]
      | .tailStore => [(if v = .sha224 then 0x101665 else 0x1032b5)]
      | .tailSetup => [(if v = .sha224 then 0x10166a else 0x1032ba), (if v = .sha224 then 0x10166d else 0x1032bd), (if v = .sha224 then 0x101670 else 0x1032c0)]
      | .tailCall => []
      | .emptySetup => [(if v = .sha224 then 0x10167e else 0x1032ce), (if v = .sha224 then 0x101681 else 0x1032d1), (if v = .sha224 then 0x101684 else 0x1032d4), (if v = .sha224 then 0x10168b else 0x1032db), (if v = .sha224 then 0x10168d else 0x1032dd)]
  | .traitLast => fun
      | .prepare => [(if v = .sha224 then 0x10195a else 0x1035ba)]
      | .smallBranch => [(if v = .sha224 then 0x101968 else 0x1035c8)]
      | .emptyTest => [(if v = .sha224 then 0x10196a else 0x1035ca)]
      | .emptyBranch => [(if v = .sha224 then 0x10196d else 0x1035cd)]
      | .smallSetup => [(if v = .sha224 then 0x1018f0 else 0x103550), (if v = .sha224 then 0x1018f4 else 0x103554), (if v = .sha224 then 0x1018f7 else 0x103557)]
      | .smallCall => []
      | .smallLength => [(if v = .sha224 then 0x101900 else 0x103560)]
      | .smallStore => [(if v = .sha224 then 0x101903 else 0x103563)]
      | .fillSetup => [(if v = .sha224 then 0x10196f else 0x1035cf), (if v = .sha224 then 0x101973 else 0x1035d3), (if v = .sha224 then 0x101977 else 0x1035d7)]
      | .fillCall => []
      | .increment => [(if v = .sha224 then 0x101980 else 0x1035e0)]
      | .fillCompressSetup => [(if v = .sha224 then 0x101985 else 0x1035e5), (if v = .sha224 then 0x10198a else 0x1035ea), (if v = .sha224 then 0x10198f else 0x1035ef), (if v = .sha224 then 0x101992 else 0x1035f2)]
      | .fillCompressCall => []
      | .clearTail => [(if v = .sha224 then 0x10199a else 0x1035fa)]
      | .restoreSource => [(if v = .sha224 then 0x10199f else 0x1035ff)]
      | .count => [(if v = .sha224 then 0x1019a2 else 0x103602)]
      | .countBranch => [(if v = .sha224 then 0x1019a9 else 0x103609)]
      | .addBlocks => [(if v = .sha224 then 0x1019ab else 0x10360b)]
      | .bulkSetup => [(if v = .sha224 then 0x1019b0 else 0x103610), (if v = .sha224 then 0x1019b5 else 0x103615)]
      | .bulkCall => []
      | .bulkRestore => []
      | .splitTail => [(if v = .sha224 then 0x1019bd else 0x10361d)]
      | .tailStore => [(if v = .sha224 then 0x1019d4 else 0x103634)]
      | .tailSetup => [(if v = .sha224 then 0x1019d9 else 0x103639), (if v = .sha224 then 0x1019dc else 0x10363c), (if v = .sha224 then 0x1019df else 0x10363f)]
      | .tailCall => []
      | .emptySetup => [(if v = .sha224 then 0x1019ed else 0x10364d), (if v = .sha224 then 0x1019f0 else 0x103650), (if v = .sha224 then 0x1019f3 else 0x103653), (if v = .sha224 then 0x1019fa else 0x10365a), (if v = .sha224 then 0x1019fc else 0x10365c)]

def Loop.chunk (loop : Loop) (v : Wrapper.Variant := .sha256) : Layout :=
  match loop with
  | .resetDiscarded =>
    { initialHash := v.initialHash
      frameBytes := 248
      bufferOffset := 0x0
      registers := ⟨14, 5, 13, 3⟩
      alignedSource := 14
      savedSource := 5
      bulkSave := none
      bufferRestore := none
      bufferSource := none
      clobbered := [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 13, 14]
      entry := (if v = .sha224 then 0x100e12 else 0x102a42)
      smallExit := (if v = .sha224 then 0x100de8 else 0x102a18)
      largeExit := (if v = .sha224 then 0x100e9f else 0x102acf)
      pc := (Loop.resetDiscarded.stagePC v)
      blocks := fun stage => (Loop.resetDiscarded.sites v).filter (fun site => site.pc ∈ (Loop.resetDiscarded.stageSites v) stage)
      smallCall := ⟨(if v = .sha224 then 0x100dda else 0x102a0a), .memory (.rip (if v = .sha224 then 0xff4a0 else 0xfd870))⟩
      fillCall := ⟨(if v = .sha224 then 0x100e36 else 0x102a66), .memory (.rip (if v = .sha224 then 0xff444 else 0xfd814))⟩
      fillCompressCall := ⟨(if v = .sha224 then 0x100e4e else 0x102a7e), .relative (if v = .sha224 then 0xa68d else 0x8a5d)⟩
      bulkCall := ⟨(if v = .sha224 then 0x100e71 else 0x102aa1), .relative (if v = .sha224 then 0xa66a else 0x8a3a)⟩
      tailCall := ⟨(if v = .sha224 then 0x100e99 else 0x102ac9), .memory (.rip (if v = .sha224 then 0xff3e1 else 0xfd7b1))⟩ }
  | .resetFirst =>
    { initialHash := v.initialHash
      frameBytes := 248
      bufferOffset := 0x0
      registers := ⟨6, 14, 13, 5⟩
      alignedSource := 6
      savedSource := 14
      bulkSave := (some 14)
      bufferRestore := none
      bufferSource := (some 3)
      clobbered := [0, 1, 2, 5, 6, 7, 8, 9, 10, 11, 13, 14]
      entry := (if v = .sha224 then 0x100f4f else 0x102b7f)
      smallExit := (if v = .sha224 then 0x100f25 else 0x102b55)
      largeExit := (if v = .sha224 then 0x100fda else 0x102c0a)
      pc := (Loop.resetFirst.stagePC v)
      blocks := fun stage => (Loop.resetFirst.sites v).filter (fun site => site.pc ∈ (Loop.resetFirst.stageSites v) stage)
      smallCall := ⟨(if v = .sha224 then 0x100f17 else 0x102b47), .memory (.rip (if v = .sha224 then 0xff363 else 0xfd733))⟩
      fillCall := ⟨(if v = .sha224 then 0x100f70 else 0x102ba0), .memory (.rip (if v = .sha224 then 0xff30a else 0xfd6da))⟩
      fillCompressCall := ⟨(if v = .sha224 then 0x100f88 else 0x102bb8), .relative (if v = .sha224 then 0xa553 else 0x8923)⟩
      bulkCall := ⟨(if v = .sha224 then 0x100fab else 0x102bdb), .relative (if v = .sha224 then 0xa530 else 0x8900)⟩
      tailCall := ⟨(if v = .sha224 then 0x100fd4 else 0x102c04), .memory (.rip (if v = .sha224 then 0xff2a6 else 0xfd676))⟩ }
  | .resetLast =>
    { initialHash := v.initialHash
      frameBytes := 248
      bufferOffset := 0x0
      registers := ⟨6, 14, 13, 5⟩
      alignedSource := 6
      savedSource := 14
      bulkSave := (some 14)
      bufferRestore := none
      bufferSource := none
      clobbered := [0, 1, 2, 5, 6, 7, 8, 9, 10, 11, 13, 14]
      entry := (if v = .sha224 then 0x10125b else 0x102e9b)
      smallExit := (if v = .sha224 then 0x101231 else 0x102e71)
      largeExit := (if v = .sha224 then 0x1012da else 0x102f1a)
      pc := (Loop.resetLast.stagePC v)
      blocks := fun stage => (Loop.resetLast.sites v).filter (fun site => site.pc ∈ (Loop.resetLast.stageSites v) stage)
      smallCall := ⟨(if v = .sha224 then 0x101227 else 0x102e67), .register 3⟩
      fillCall := ⟨(if v = .sha224 then 0x101278 else 0x102eb8), .register 3⟩
      fillCompressCall := ⟨(if v = .sha224 then 0x10128c else 0x102ecc), .relative (if v = .sha224 then 0xa24f else 0x860f)⟩
      bulkCall := ⟨(if v = .sha224 then 0x1012af else 0x102eef), .relative (if v = .sha224 then 0xa22c else 0x85ec)⟩
      tailCall := ⟨(if v = .sha224 then 0x1012d8 else 0x102f18), .register 3⟩ }
  | .finalizeFirst =>
    { initialHash := v.initialHash
      frameBytes := 360
      bufferOffset := 0x8
      registers := ⟨13, 5, 12, 3⟩
      alignedSource := 13
      savedSource := 5
      bulkSave := none
      bufferRestore := none
      bufferSource := none
      clobbered := [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13]
      entry := (if v = .sha224 then 0x100726 else 0x102336)
      smallExit := (if v = .sha224 then 0x1006fc else 0x10230c)
      largeExit := (if v = .sha224 then 0x1007bb else 0x1023cb)
      pc := (Loop.finalizeFirst.stagePC v)
      blocks := fun stage => (Loop.finalizeFirst.sites v).filter (fun site => site.pc ∈ (Loop.finalizeFirst.stageSites v) stage)
      smallCall := ⟨(if v = .sha224 then 0x1006ee else 0x1022fe), .memory (.rip (if v = .sha224 then 0xffb8c else 0xfdf7c))⟩
      fillCall := ⟨(if v = .sha224 then 0x10074e else 0x10235e), .memory (.rip (if v = .sha224 then 0xffb2c else 0xfdf1c))⟩
      fillCompressCall := ⟨(if v = .sha224 then 0x100768 else 0x102378), .relative (if v = .sha224 then 0xad73 else 0x9163)⟩
      bulkCall := ⟨(if v = .sha224 then 0x10078b else 0x10239b), .relative (if v = .sha224 then 0xad50 else 0x9140)⟩
      tailCall := ⟨(if v = .sha224 then 0x1007b5 else 0x1023c5), .memory (.rip (if v = .sha224 then 0xffac5 else 0xfdeb5))⟩ }
  | .finalizeLast =>
    { initialHash := v.initialHash
      frameBytes := 360
      bufferOffset := 0x8
      registers := ⟨6, 13, 3, 5⟩
      alignedSource := 6
      savedSource := 13
      bulkSave := (some 13)
      bufferRestore := none
      bufferSource := none
      clobbered := [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 13]
      entry := (if v = .sha224 then 0x100a3f else 0x10265f)
      smallExit := (if v = .sha224 then 0x100a16 else 0x102636)
      largeExit := (if v = .sha224 then 0x100acc else 0x1026ec)
      pc := (Loop.finalizeLast.stagePC v)
      blocks := fun stage => (Loop.finalizeLast.sites v).filter (fun site => site.pc ∈ (Loop.finalizeLast.stageSites v) stage)
      smallCall := ⟨(if v = .sha224 then 0x100a0b else 0x10262b), .register 12⟩
      fillCall := ⟨(if v = .sha224 then 0x100a64 else 0x102684), .register 12⟩
      fillCompressCall := ⟨(if v = .sha224 then 0x100a7b else 0x10269b), .relative (if v = .sha224 then 0xaa60 else 0x8e40)⟩
      bulkCall := ⟨(if v = .sha224 then 0x100a9e else 0x1026be), .relative (if v = .sha224 then 0xaa3d else 0x8e1d)⟩
      tailCall := ⟨(if v = .sha224 then 0x100ac9 else 0x1026e9), .register 12⟩ }
  | .traitFirst =>
    { initialHash := v.initialHash
      frameBytes := 360
      bufferOffset := 0x0
      registers := ⟨5, 14, 13, 12⟩
      alignedSource := 5
      savedSource := 14
      bulkSave := none
      bufferRestore := (some 13)
      bufferSource := (some 3)
      clobbered := [0, 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
      entry := (if v = .sha224 then 0x1015eb else 0x10323b)
      smallExit := (if v = .sha224 then 0x101598 else 0x1031e8)
      largeExit := (if v = .sha224 then 0x101679 else 0x1032c9)
      pc := (Loop.traitFirst.stagePC v)
      blocks := fun stage => (Loop.traitFirst.sites v).filter (fun site => site.pc ∈ (Loop.traitFirst.stageSites v) stage)
      smallCall := ⟨(if v = .sha224 then 0x10158a else 0x1031da), .memory (.rip (if v = .sha224 then 0xfecf0 else 0xfd0a0))⟩
      fillCall := ⟨(if v = .sha224 then 0x10160b else 0x10325b), .memory (.rip (if v = .sha224 then 0xfec6f else 0xfd01f))⟩
      fillCompressCall := ⟨(if v = .sha224 then 0x101626 else 0x103276), .relative (if v = .sha224 then 0x9eb5 else 0x8265)⟩
      bulkCall := ⟨(if v = .sha224 then 0x101649 else 0x103299), .relative (if v = .sha224 then 0x9e92 else 0x8242)⟩
      tailCall := ⟨(if v = .sha224 then 0x101673 else 0x1032c3), .memory (.rip (if v = .sha224 then 0xfec07 else 0xfcfb7))⟩ }
  | .traitLast =>
    { initialHash := v.initialHash
      frameBytes := 360
      bufferOffset := 0x0
      registers := ⟨13, 12, 5, 14⟩
      alignedSource := 13
      savedSource := 12
      bulkSave := none
      bufferRestore := (some 5)
      bufferSource := (some 3)
      clobbered := [0, 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
      entry := (if v = .sha224 then 0x10195a else 0x1035ba)
      smallExit := (if v = .sha224 then 0x101908 else 0x103568)
      largeExit := (if v = .sha224 then 0x1019e8 else 0x103648)
      pc := (Loop.traitLast.stagePC v)
      blocks := fun stage => (Loop.traitLast.sites v).filter (fun site => site.pc ∈ (Loop.traitLast.stageSites v) stage)
      smallCall := ⟨(if v = .sha224 then 0x1018fa else 0x10355a), .memory (.rip (if v = .sha224 then 0xfe980 else 0xfcd20))⟩
      fillCall := ⟨(if v = .sha224 then 0x10197a else 0x1035da), .memory (.rip (if v = .sha224 then 0xfe900 else 0xfcca0))⟩
      fillCompressCall := ⟨(if v = .sha224 then 0x101995 else 0x1035f5), .relative (if v = .sha224 then 0x9b46 else 0x7ee6)⟩
      bulkCall := ⟨(if v = .sha224 then 0x1019b8 else 0x103618), .relative (if v = .sha224 then 0x9b23 else 0x7ec3)⟩
      tailCall := ⟨(if v = .sha224 then 0x1019e2 else 0x103642), .memory (.rip (if v = .sha224 then 0xfe898 else 0xfcc38))⟩ }

theorem Loop.chunk_sites (loop : Loop) (stage : Stage) (v : Wrapper.Variant := .sha256) :
    ∀ site ∈ (loop.chunk v).blocks stage, site ∈ (loop.sites v) := by
  cases v <;> cases loop <;> exact fun site member => (List.mem_filter.mp member).1

theorem Loop.chunk_inside (loop : Loop) (stage : Stage) (v : Wrapper.Variant := .sha256) :
    ∀ site ∈ (loop.chunk v).blocks stage, BlockInProgram site.pc (Blocks.bytes site.block).length :=
  fun site member => loop.sites_inside v site (loop.chunk_sites stage v site member)

theorem Loop.basic_sites (loop : Loop) (stage : Stage)
    (notStore : stage ∉ [Stage.smallStore, .increment, .clearTail, .addBlocks, .tailStore]) (v : Wrapper.Variant := .sha256) :
    ∀ site ∈ (loop.chunk v).blocks stage, Blocks.Basic site.block := by
  cases v <;> cases loop <;> cases stage <;> first | contradiction | decide +kernel

theorem traitFirst_chunk (v : Wrapper.Variant := .sha256) : (Loop.traitFirst.chunk v) = (traitFirst v).chunk := by
  cases v <;> simp only [Loop.chunk, traitFirst]
  all_goals
  congr 1 <;> funext stage <;> cases stage <;> simp [Loop.sites, Loop.stageSites]

end Sha2.Proofs.Common.SHA256.Instances.Absorption
