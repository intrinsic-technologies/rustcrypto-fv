import Md5.Proofs.Buffered.Update.Contracts

namespace Md5.Proofs.Buffered.ResetSecond

open X86 X86.Machine X86.UserProcess X86Proofs

def pc (kind : UpdateKind) (oldPC : BitVec 64) : BitVec 64 :=
  match kind with
  | .finalizeResetSecond => oldPC + 0x690
  | .resetDiscardSecond =>
    match oldPC.toNat with
    | 0x1009a0 => 0x101510
    | 0x1009a4 => 0x101514
    | 0x1009a8 => 0x10151b
    | 0x1009ab => 0x10151e
    | 0x1009ae => 0x101521
    | 0x1009b1 => 0x101524
    | 0x1009b6 => 0x101529
    | 0x1009df => 0x101549
    | 0x1009e5 => 0x10154e
    | 0x1009ea => 0x101553
    | 0x1009ed => 0x101556
    | 0x1009f0 => 0x101559
    | 0x1009f3 => 0x10155c
    | 0x1009f5 => 0x10155e
    | 0x1009f8 => 0x101561
    | 0x1009fe => 0x101567
    | 0x100a02 => 0x10156b
    | 0x100a06 => 0x10156f
    | 0x100a0a => 0x101576
    | 0x100a0d => 0x101579
    | 0x100a12 => 0x10157e
    | 0x100a17 => 0x101583
    | 0x100a1c => 0x101588
    | 0x100a1f => 0x10158d
    | 0x100a24 => 0x101592
    | 0x100a29 => 0x101597
    | 0x100a2c => 0x10159a
    | 0x100a2f => 0x10159d
    | 0x100a33 => 0x1015a1
    | 0x100a35 => 0x1015a3
    | 0x100a3a => 0x1015a8
    | 0x100a3f => 0x1015ad
    | 0x100a42 => 0x1015b0
    | 0x100a47 => 0x1015b5
    | 0x100a4a => 0x1015b5
    | 0x100a4d => 0x1015b8
    | 0x100a57 => 0x1015c2
    | 0x100a5a => 0x1015c5
    | 0x100a5e => 0x1015c9
    | 0x100a61 => 0x1015cc
    | 0x100a66 => 0x1015d1
    | 0x100a69 => 0x1015d9
    | 0x100a6c => 0x1015dc
    | 0x100a6f => 0x1015df
    | 0x100a82 => 0x1015ef
    | 0x100a85 => 0x1015f2
    | 0x100a88 => 0x1015f5
    | 0x100a8c => 0x1015f9
    | 0x100a8e => 0x1015fb
    | 0x100a90 => 0x1015fd
    | _ => oldPC
  | _ => oldPC

def positionRegister (kind : UpdateKind) : BitVec 5 :=
  if kind = .resetDiscardSecond then 5 else 13

def savedInputRegister (kind : UpdateKind) : BitVec 5 :=
  if kind = .resetDiscardSecond then 13 else 12

def batchSavedInputRegister (kind : UpdateKind) : BitVec 5 :=
  if kind = .resetDiscardSecond then 3 else 12

def remainingRegister (_kind : UpdateKind) : BitVec 5 := 14

def position (kind : UpdateKind) (s : RamState) : BitVec 64 :=
  ((Operand.mem (kind.context s + 63) : Operand 8).read s).setWidth 64

end Md5.Proofs.Buffered.ResetSecond
