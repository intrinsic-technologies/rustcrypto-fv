import ChaCha20Poly1305.Proofs.Decrypt.StreamControl
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part3

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 9000
set_option maxHeartbeats 7000000
set_option pp.maxSteps 120
@[refine_layout] def writeAt (d : BitVec 64) (x : Input) (j : BitVec 64) (fr : Activation) (v : Vector (BitVec 64) 8)
    (last : Bool) : Micro.Step where
  entry := .l101036
  exit := if last then .l1010b3 else .l100c70
  pre := fixedRegs x j fr ++ [.mem (fr.rsp+96) 64 x.buf,.mem (fr.rsp+80) 64 (x.n >>> 6),
    .readable fr.rsp 368,.writable d 64,
    .fact (fr.rsp.toNat + 368 ≤ d.toNat ∨ d.toNat+64 ≤ fr.rsp.toNat),
    .fact (d.toNat+64 ≤ 0x101036 ∨ 0x1010b3 ≤ d.toNat)] ++ [.mem (fr.rsp+176) 64 v[0],
    .mem (fr.rsp+184) 64 v[1],
    .mem (fr.rsp+192) 64 v[2],
    .mem (fr.rsp+200) 64 v[3],
    .mem (fr.rsp+208) 64 v[4],
    .mem (fr.rsp+216) 64 v[5],
    .mem (fr.rsp+224) 64 v[6],
    .mem (fr.rsp+232) 64 v[7]]
  post := Full.registers fr ++ [.gpr 7 (j+1),.low 12 32 (x.w[12].toBitVec+1),
    .low 10 32 x.w[4].toBitVec,.low 11 32 x.w[8].toBitVec,.low 8 32 x.w[13].toBitVec] ++ qwords d v
  writes := [⟨d.toNat,64⟩]

private theorem writeFrom (d : BitVec 64) (x : Input) (j : BitVec 64) (fr : Activation) (v : Vector (BitVec 64) 8) (last : Bool) (addr : x.buf + (j <<< 6) = d) (h : j+1 = x.n >>> 6 ↔ last = true) : Micro.Valid (writeAt d x j fr v last) := by
  unfold Micro.Valid
  cases last <;> simp at h
  all_goals refine_one [Micro.program,writeAt,addr,h]
  all_goals first | assumption | exact False.elim (h hc.symm) | exact False.elim (hc h.symm) | contradiction


theorem writeValid (x : Input) (j : BitVec 64) (fr : Activation) (v : Vector (BitVec 64) 8) (last : Bool) (h : j+1 = x.n >>> 6 ↔ last = true) : Micro.Valid (writeStep x j fr v last)  := by
  have e : writeStep x j fr v last = writeAt (blockPtr x j) x j fr v last := by
    unfold writeStep writeAt
    congr 2
    simp [qwords,BitVec.add_assoc]
  exact e ▸ writeFrom _ x j fr v last rfl h

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
