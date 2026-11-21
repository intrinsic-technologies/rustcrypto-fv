import P256.Proofs.Program.Compare.Mismatch.Wide
import P256.Proofs.Program.Compare.Mismatch.WordComparisons
import P256.Proofs.Program.Compare.Mismatch.ShiftedHalves

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def mainStage16 [Bindings] : NarrowingStage 16 0 7 0x11c8f1 0x11c900 where
  shiftEntry := 0x11c8f6
  shiftedEntry := 0x11c8fc
  equalExit := 0x11c916
  lowCompare := main_low16
  shift := main_shift16
  highCompare := main_shifted16

def tailStage16 [Bindings] : NarrowingStage 16 0 7 0x11ce1f 0x11ce2e where
  shiftEntry := 0x11ce24
  shiftedEntry := 0x11ce2a
  equalExit := 0x11ce91
  lowCompare := tail_low16
  shift := tail_shift16
  highCompare := tail_shifted16

def fourStage16 [Bindings] : NarrowingStage 16 6 7 0x11ce4d 0x11ce5c where
  shiftEntry := 0x11ce52
  shiftedEntry := 0x11ce58
  equalExit := 0x11ce91
  lowCompare := four_low16
  shift := four_shift16
  highCompare := four_shifted16

def mainStage8 [Bindings] : NarrowingStage 8 0 7 0x11c900 0x11c91a where
  shiftEntry := 0x11c905
  shiftedEntry := 0x11c911
  equalExit := 0x11c916
  lowCompare := main_low8
  shift := main_shift8
  highCompare := main_shifted8

def tailStage8 [Bindings] : NarrowingStage 8 0 7 0x11ce2e 0x11ce44 where
  shiftEntry := 0x11ce33
  shiftedEntry := 0x11ce3f
  equalExit := 0x11ce91
  lowCompare := tail_low8
  shift := tail_shift8
  highCompare := tail_shifted8

def fourStage8 [Bindings] : NarrowingStage 8 6 7 0x11ce5c 0x11ce72 where
  shiftEntry := 0x11ce61
  shiftedEntry := 0x11ce6d
  equalExit := 0x11ce91
  lowCompare := four_low8
  shift := four_shift8
  highCompare := four_shifted8

def twoStage8 [Bindings] : NarrowingStage 8 8 7 0x11ce78 0x11ce94 where
  shiftEntry := 0x11ce7d
  shiftedEntry := 0x11ce8b
  equalExit := 0x11ce91
  lowCompare := two_low8
  shift := two_shift8
  highCompare := two_shifted8

end P256.Proofs.Program.Compare.Mismatch
