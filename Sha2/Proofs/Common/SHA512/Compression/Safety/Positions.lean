import Sha2.Proofs.Common.SHA512.Compression.Safety.Basic
import Sha2.Proofs.Common.SHA512.Compression.Decoded

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Safety

open X86 X86.Machine X86.UserProcess X86Proofs

 def positionOf (entry : BitVec 64 × Nat) : Position :=
  ⟨entry.1 + BitVec.ofNat 64 entry.2, false, [6]⟩

def positionsOf (layout : List (BitVec 64 × Nat)) : List Position := layout.map positionOf

def positionOfNoRsi (entry : BitVec 64 × Nat) : Position :=
  ⟨entry.1 + BitVec.ofNat 64 entry.2, false, []⟩

def positionsOfNoRsi (layout : List (BitVec 64 × Nat)) : List Position :=
  layout.map positionOfNoRsi

def before00 : Position := ⟨0x10ddf0, false, [6]⟩
def after00 : Position := ⟨0x10de17, false, [6]⟩
def positions00 := positionsOf Decoded.part00Layout

def before01 : Position := after00
def after01 : Position := ⟨0x10de50, false, [6]⟩
def positions01 := positionsOf Decoded.part01Layout

def before02 : Position := after01
def after02 : Position := ⟨0x10df22, false, [6]⟩
def positions02 := positionsOf Decoded.part02Layout

def before03 : Position := after02
def after03 : Position := ⟨0x10df2f, false, [6]⟩
def positions03 := positionsOf Decoded.part03Layout

def before04 : Position := after03
def after04 : Position := ⟨0x10df5b, false, []⟩
def positions04 := positionsOfNoRsi Decoded.part04Layout

def before05 : Position := after04
def after05 : Position := ⟨0x10dfba, false, []⟩
def positions05 := positionsOfNoRsi Decoded.part05Layout

def before06 : Position := after05
def after06 : Position := ⟨0x10dffc, false, []⟩
def positions06 := positionsOfNoRsi Decoded.part06Layout

def before06And : Position := after06
def after06And : Position := ⟨0x10e004, false, []⟩
def positions06And := positionsOfNoRsi Decoded.part06AndLayout

def before07 : Position := after06And
def after07 : Position := ⟨0x10e074, false, []⟩
def positions07 := positionsOfNoRsi Decoded.part07Layout

def before08 : Position := after07
def after08 : Position := ⟨0x10e0f7, false, []⟩
def positions08 := positionsOfNoRsi Decoded.part08Layout

def before09 : Position := after08
def after09 : Position := ⟨0x10e184, false, []⟩
def positions09 := positionsOfNoRsi Decoded.part09Layout

def before10 : Position := after09
def after10 : Position := ⟨0x10e1fa, false, []⟩
def positions10 := positionsOfNoRsi Decoded.part10Layout

def before11 : Position := after10
def after11 : Position := ⟨0x10e27d, false, []⟩
def positions11 := positionsOfNoRsi Decoded.part11Layout

def before12 : Position := after11
def after12 : Position := ⟨0x10e300, false, []⟩
def positions12 := positionsOfNoRsi Decoded.part12Layout

def before13 : Position := after12
def after13 : Position := ⟨0x10e383, false, []⟩
def positions13 := positionsOfNoRsi Decoded.part13Layout

def before14 : Position := after13
def after14 : Position := ⟨0x10e406, false, []⟩
def positions14 := positionsOfNoRsi Decoded.part14Layout

def before15 : Position := after14
def after15 : Position := ⟨0x10e489, false, []⟩
def positions15 := positionsOfNoRsi Decoded.part15Layout

def before16 : Position := after15
def after16 : Position := ⟨0x10e50c, false, []⟩
def positions16 := positionsOfNoRsi Decoded.part16Layout

def before17 : Position := after16
def after17 : Position := ⟨0x10e592, false, []⟩
def positions17 := positionsOfNoRsi Decoded.part17Layout

def before18 : Position := after17
def after18 : Position := ⟨0x10e608, false, []⟩
def positions18 := positionsOfNoRsi Decoded.part18Layout

def before19 : Position := after18
def after19 : Position := ⟨0x10e6fc, false, []⟩
def positions19 := positionsOfNoRsi Decoded.part19Layout

def before20 : Position := after19
def after20 : Position := ⟨0x10e862, false, []⟩
def positions20 := positionsOfNoRsi Decoded.part20Layout

def before21 : Position := after20
def after21 : Position := ⟨0x10e9e5, false, []⟩
def positions21 := positionsOfNoRsi Decoded.part21Layout

def before22 : Position := after21
def after22 : Position := ⟨0x10eba6, false, []⟩
def positions22 := positionsOfNoRsi Decoded.part22Layout

def before23 : Position := after22
def after23 : Position := ⟨0x10ed1b, false, []⟩
def positions23 := positionsOfNoRsi Decoded.part23Layout

def before24 : Position := after23
def after24 : Position := ⟨0x10ee8c, false, []⟩
def positions24 := positionsOfNoRsi Decoded.part24Layout

def before25 : Position := after24
def after25 : Position := ⟨0x10efe3, false, []⟩
def positions25 := positionsOfNoRsi Decoded.part25Layout

def before26 : Position := after25
def after26 : Position := ⟨0x10f134, false, []⟩
def positions26 := positionsOfNoRsi Decoded.part26Layout

def before27 : Position := after26
def after27 : Position := ⟨0x10f294, false, []⟩
def positions27 := positionsOfNoRsi Decoded.part27Layout

def before28 : Position := after27
def after28 : Position := ⟨0x10f3ec, false, []⟩
def positions28 := positionsOfNoRsi Decoded.part28Layout

def before29 : Position := after28
def after29 : Position := ⟨0x10f542, false, []⟩
def positions29 := positionsOfNoRsi Decoded.part29Layout

def before30 : Position := after29
def after30 : Position := ⟨0x10f695, false, []⟩
def positions30 := positionsOfNoRsi Decoded.part30Layout

def before31 : Position := after30
def after31 : Position := ⟨0x10f7e3, false, []⟩
def positions31 := positionsOfNoRsi Decoded.part31Layout

def before32 : Position := after31
def after32 : Position := ⟨0x10f938, false, []⟩
def positions32 := positionsOfNoRsi Decoded.part32Layout

def before33 : Position := after32
def after33 : Position := ⟨0x10fa8d, false, []⟩
def positions33 := positionsOfNoRsi Decoded.part33Layout

def before34 : Position := after33
def after34 : Position := ⟨0x10fbe8, false, []⟩
def positions34 := positionsOfNoRsi Decoded.part34Layout

def before35 : Position := after34
def after35 : Position := ⟨0x10fd36, false, []⟩
def positions35 := positionsOfNoRsi Decoded.part35Layout

def before36 : Position := after35
def after36 : Position := ⟨0x10fe84, false, []⟩
def positions36 := positionsOfNoRsi Decoded.part36Layout

def before37 : Position := after36
def after37 : Position := ⟨0x10ffda, false, []⟩
def positions37 := positionsOfNoRsi Decoded.part37Layout

def before38 : Position := after37
def after38 : Position := ⟨0x110130, false, []⟩
def positions38 := positionsOfNoRsi Decoded.part38Layout

def before39 : Position := after38
def after39 : Position := ⟨0x11028c, false, []⟩
def positions39 := positionsOfNoRsi Decoded.part39Layout

def before40 : Position := after39
def after40 : Position := ⟨0x1103d9, false, []⟩
def positions40 := positionsOfNoRsi Decoded.part40Layout

def before41 : Position := after40
def after41 : Position := ⟨0x11052c, false, []⟩
def positions41 := positionsOfNoRsi Decoded.part41Layout

def before42 : Position := after41
def after42 : Position := ⟨0x110681, false, []⟩
def positions42 := positionsOfNoRsi Decoded.part42Layout

def before43 : Position := after42
def after43 : Position := ⟨0x1107d4, false, []⟩
def positions43 := positionsOfNoRsi Decoded.part43Layout

def before44 : Position := after43
def after44 : Position := ⟨0x11092a, false, []⟩
def positions44 := positionsOfNoRsi Decoded.part44Layout

def before45 : Position := after44
def after45 : Position := ⟨0x110a7b, false, []⟩
def positions45 := positionsOfNoRsi Decoded.part45Layout

def before46 : Position := after45
def after46 : Position := ⟨0x110bce, false, []⟩
def positions46 := positionsOfNoRsi Decoded.part46Layout

def before47 : Position := after46
def after47 : Position := ⟨0x110d1e, false, []⟩
def positions47 := positionsOfNoRsi Decoded.part47Layout

def before48 : Position := after47
def after48 : Position := ⟨0x110e72, false, []⟩
def positions48 := positionsOfNoRsi Decoded.part48Layout

def before49 : Position := after48
def after49 : Position := ⟨0x110fc8, false, []⟩
def positions49 := positionsOfNoRsi Decoded.part49Layout

def before50 : Position := after49
def after50 : Position := ⟨0x11111c, false, []⟩
def positions50 := positionsOfNoRsi Decoded.part50Layout

def before51 : Position := after50
def after51 : Position := ⟨0x111273, false, []⟩
def positions51 := positionsOfNoRsi Decoded.part51Layout

def before52 : Position := after51
def after52 : Position := ⟨0x1113e1, false, []⟩
def positions52 := positionsOfNoRsi Decoded.part52Layout

def before53 : Position := after52
def after53 : Position := ⟨0x111534, false, []⟩
def positions53 := positionsOfNoRsi Decoded.part53Layout

def before54 : Position := after53
def after54 : Position := ⟨0x11167c, false, []⟩
def positions54 := positionsOfNoRsi Decoded.part54Layout

def before55 : Position := after54
def after55 : Position := ⟨0x1117e4, false, []⟩
def positions55 := positionsOfNoRsi Decoded.part55Layout

def before56 : Position := after55
def after56 : Position := ⟨0x111802, false, []⟩
def positions56 := positionsOfNoRsi Decoded.part56Layout


def positions : List Position :=
  before00 :: (positions00 ++ positions01 ++ positions02 ++ positions03 ++ positions04 ++ positions05 ++ positions06 ++ positions06And ++ positions07 ++ positions08 ++ positions09 ++ positions10 ++ positions11 ++ positions12 ++ positions13 ++ positions14 ++ positions15 ++ positions16 ++ positions17 ++ positions18 ++ positions19 ++ positions20 ++ positions21 ++ positions22 ++ positions23 ++ positions24 ++ positions25 ++ positions26 ++ positions27 ++ positions28 ++ positions29 ++ positions30 ++ positions31 ++ positions32 ++ positions33 ++ positions34 ++ positions35 ++ positions36 ++ positions37 ++ positions38 ++ positions39 ++ positions40 ++ positions41 ++ positions42 ++ positions43 ++ positions44 ++ positions45 ++ positions46 ++ positions47 ++ positions48 ++ positions49 ++ positions50 ++ positions51 ++ positions52 ++ positions53 ++ positions54 ++ positions55 ++ positions56)

end Sha2.Proofs.Common.SHA512.Compression.Safety
