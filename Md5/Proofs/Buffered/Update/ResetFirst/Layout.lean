import Md5.Proofs.Buffered.Update.Contracts

namespace Md5.Proofs.Buffered.ResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs

def KindSupported (kind : UpdateKind) : Prop :=
  kind = .resetFirst ∨ kind = .finalizeResetFirst ∨ kind = .resetDiscardFirst

def pc (kind : UpdateKind) (offset : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (0x100000 + match kind with
    | .finalizeResetFirst => offset + 0x6b0
    | .resetDiscardFirst => match offset with
      | 0x690 => 0x13d0
      | 0x69e => 0x13de
      | 0x6a4 => 0x13e4
      | 0x6ac => 0x13ec
      | 0x6d0 => 0x140a
      | 0x6e4 => 0x141d
      | 0x6e6 => 0x141f
      | 0x6ef => 0x1428
      | 0x6fe => 0x1437
      | 0x704 => 0x143d
      | 0x709 => 0x1442
      | 0x718 => 0x1451
      | 0x71d => 0x1456
      | 0x722 => 0x145b
      | 0x72c => 0x1465
      | 0x72e => 0x1467
      | 0x733 => 0x146c
      | 0x73b => 0x1474
      | 0x740 => 0x1479
      | 0x756 => 0x1490
      | 0x75a => 0x1495
      | 0x765 => 0x14a0
      | 0x76b => 0x14a6
      | 0x779 => 0x14b4
      | 0x783 => 0x14be
      | n => n
    | _ => offset)

def reg (kind : UpdateKind) (r : BitVec 5) : BitVec 5 :=
  if kind = .resetDiscardFirst then
    if r = 13 then 5 else if r = 3 then 13 else if r = 12 then 3 else r
  else r

def stackOffset (kind : UpdateKind) (offset : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (kind.contextOffset + offset - 8)

end Md5.Proofs.Buffered.ResetFirst
