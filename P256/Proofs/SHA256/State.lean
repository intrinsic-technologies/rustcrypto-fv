import P256.Proofs.SHA256.Interface

set_option autoImplicit false

namespace P256.Proofs.SHA256

open X86 X86.Machine

structure RegistersAt (s : RamState) (hash : Array UInt32) : Prop where
  size : hash.size = 8
  a : (s.regValue .rbx).setWidth 32 = hash[0]!.toBitVec
  b : (s.regValue .r14).setWidth 32 = hash[1]!.toBitVec
  c : (s.regValue .rax).setWidth 32 = hash[2]!.toBitVec
  d : (s.regValue .r9).setWidth 32 = hash[3]!.toBitVec
  e : (s.regValue .r8).setWidth 32 = hash[4]!.toBitVec
  f : (s.regValue .r10).setWidth 32 = hash[5]!.toBitVec
  g : (s.regValue .rdx).setWidth 32 = hash[6]!.toBitVec
  h : (s.regValue .rcx).setWidth 32 = hash[7]!.toBitVec


end P256.Proofs.SHA256
