import ChaCha20Poly1305.Proofs.Decrypt.StreamABI
import ChaCha20Poly1305.Proofs.Decrypt.Bytes

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Control

@[refine_layout] def extra (x : Input) (fr : Activation) : List MemoryRegion :=
  [⟨fr.rdi.toNat+48,4⟩,⟨fr.rdi.toNat+64,64⟩,⟨x.buf.toNat,x.n.toNat⟩]

@[refine_layout] def fn (x : Input) (src dst : BitVec (8*x.n.toNat)) : Callee where
  entry := .l100a80
  abi := Fn100a80.active .l100a80
  pre fr := (core x).atoms .entry () fr () ++ [.mem x.buf (8*x.n.toNat) src]
  post _ := [.gpr 0 0,.mem x.buf (8*x.n.toNat) dst]
  writes := extra x

theorem sliceByte {m : Ram} {buf : BitVec 64} {n i : Nat} (h : i<n) :
    Xor.readAt m buf i = (memLoad m buf (8*n)).extractLsb' (8*i) 8 := by
  rw [extractLsb'_memLoad _ _ _ _ (by omega) (by decide) (by omega)]
  simp [Xor.readAt]

theorem loadFromBytes {m : Ram} {buf : BitVec 64} {n : Nat} {val : BitVec (8*n)}
    (h : ∀ i, i<n → Xor.readAt m buf i = val.extractLsb' (8*i) 8) : memLoad m buf (8*n) = val := by
  apply memLoad_eq_of_memByte (by omega)
  intro i hi
  have e := h i (by omega)
  simp only [Xor.readAt,memLoad_8] at e
  change _ = UInt8.ofBitVec (val.extractLsb' (8*i) 8)
  exact UInt8.toBitVec_inj.mp e

set_option maxHeartbeats 550000
set_option maxRecDepth 6000
set_option pp.maxSteps 140

theorem correct (x : Input) (src dst : BitVec (8*x.n.toNat)) (small : x.w[12].toBitVec.toNat ≤ 1)
    (bytesEq : ∀ i, i<x.n.toNat → dst.extractLsb' (8*i) 8 = streamByte x i ^^^ src.extractLsb' (8*i) 8) :
    (fn x src dst).Correct := by
  intro fr a hl hat hf
  change Atom.All fnCode a.arguments a.store (Fn100a80.active .l100a80 fr ++
    ((core x).atoms .entry () fr () ++ [.mem x.buf (8*x.n.toNat) src])) at hat
  rw [Atom.all_append,Atom.all_append] at hat
  obtain ⟨abi,ax,srcV,_⟩ := hat
  let sf := snap fr a.store
  have sp : 416 ≤ fr.rsp.toNat := by unpack_atoms abi []; omega
  have low : fr.low.toNat+416 ≤ fr.rsp.toNat := by unpack_atoms abi []; assumption
  have sfLow : sf.low.toNat = fr.rsp.toNat-416 := by dsimp [sf,snap]; bv_omega
  have start : (front x).Rel fnCode (sf,()) (unitLoc .entry) a := by
    refine ⟨hl,⟨(),rfl,rfl,(Atom.all_append _ _).2 ⟨?_,ax⟩⟩,.refl _ _⟩
    unpack_atoms abi []
    join_atoms [sf]
    all_goals first | assumption | bv_omega
  obtain ⟨b,ab,bl,⟨_,_,_,base⟩,bf⟩ := prologue x small start
  change Base x sf b at base
  obtain ⟨s,ready,words⟩ := baseInputs x sf b base
  obtain ⟨c,bc,cl,regs,cf,vals⟩ := body x (work sf) b s bl ready words
  have lastAbi := baseOut x sf b c base regs cf
  let ef := {sf with original := c.store}
  obtain ⟨o,er,tag,done,ofr⟩ := execEnd ef c cl lastAbi rfl
  refine ⟨o,execJump (jumpTrans ab bc) er,tag,?_,?_⟩
  · change Atom.All fnCode _ _ (abiOut fr ++ [.gpr 0 0,.mem x.buf (8*x.n.toNat) dst])
    rw [Atom.all_append] at done ⊢
    refine ⟨done.1,done.2.1,?_,trivial⟩
    apply loadFromBytes
    have g := ax
    unpack_atoms g []
    change RamWriteFrame a.store b.store (sf.region :: [⟨fr.rdi.toNat+64,1⟩]) at bf
    intro i hi
    have bufLow := s.buf.readable.low
    have p : (x.buf+BitVec.ofNat 64 i).toNat = x.buf.toNat+i := Xor.ptrNat (by omega)
    have out : Xor.readAt o.store x.buf i = Xor.readAt c.store x.buf i := by
      apply ofr.memLoad_eq
      simp [Outside,ef,sf,snap,Activation.region,p]; bv_omega
    have inp : Xor.readAt b.store x.buf i = Xor.readAt a.store x.buf i := by
      apply bf.memLoad_eq
      simp [Outside,Activation.region,p,sf,snap]; bv_omega
    rw [out,vals i hi,inp,bytesEq i hi,sliceByte hi,srcV]
  · change RamWriteFrame fr.original o.store (fr.region :: extra x fr)
    change RamWriteFrame fr.original a.store (fr.region :: extra x fr) at hf
    apply ((hf.trans bf _).trans cf _) |>.trans ofr
    all_goals simp [RegionsWithin,Activation.region,extra,bodyFrame,front,Layout.withFrame,core,work,snap,sf,ef] <;> bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Stream
