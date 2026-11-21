import ChaCha20Poly1305.Proofs.Decrypt.FullBlock
import ChaCha20Poly1305.Proofs.Decrypt.BlockMath

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

structure Scope (x : Input) (fr : Activation) (m : Ram) : Prop where
  stack : Writable fnCode m fr.rsp 368
  ctx : Writable fnCode m fr.rdi 128
  buf : Writable fnCode m x.buf x.n.toNat
  stackCode : fr.rsp.toNat+368 ≤ 0x100a80 ∨ 0x1014bc ≤ fr.rsp.toNat
  ctxCode : fr.rdi.toNat+128 ≤ 0x100a80 ∨ 0x1014bc ≤ fr.rdi.toNat
  bufCode : x.buf.toNat+x.n.toNat ≤ 0x100a80 ∨ 0x1014bc ≤ x.buf.toNat
  stackCtx : fr.rsp.toNat+368 ≤ fr.rdi.toNat ∨ fr.rdi.toNat+128 ≤ fr.rsp.toNat
  stackBuf : fr.rsp.toNat+368 ≤ x.buf.toNat ∨ x.buf.toNat+x.n.toNat ≤ fr.rsp.toNat
  ctxBuf : fr.rdi.toNat+128 ≤ x.buf.toNat ∨ x.buf.toNat+x.n.toNat ≤ fr.rdi.toNat

theorem Scope.after {x fr a b rs} (s : Scope x fr a) (f : RamWriteFrame a b rs) : Scope x fr b :=
  { s with stack := s.stack.of_frame f, ctx := s.ctx.of_frame f, buf := s.buf.of_frame f }

theorem Scope.block {x fr m} (s : Scope x fr m) {i : Nat} (hi : i < x.n.toNat/64) :
    BlockGeo fr.rsp (blockPtr x (BitVec.ofNat 64 i)) m := by
  have low := s.buf.readable.low
  have addr := blockAddress x i (by omega) low
  have apart := s.stackBuf
  have code := s.bufCode
  exact ⟨s.stack,s.buf.sub (by omega) (by omega),by omega,s.stackCode,by omega⟩

def prefixFrame (x : Input) (fr : Activation) (i : Nat) : List MemoryRegion :=
  ⟨x.buf.toNat,64*i⟩ :: blockScratch fr

@[refine_layout] def live (x : Input) (i : Nat) (fr : Activation) : List Atom :=
  Full.registers fr ++ [.gpr 7 (BitVec.ofNat 64 i),.low 10 32 x.w[4].toBitVec,
   .low 11 32 x.w[8].toBitVec,.low 8 32 x.w[13].toBitVec,.low 12 32 (x.w[12].toBitVec+BitVec.ofNat 32 i)]

theorem pinsKept {x fr m m' i} (s : Scope x fr m) (hi : 64*i ≤ x.n.toNat)
    (f : RamWriteFrame m m' (prefixFrame x fr i)) {rs rs'}
    (h : Atom.All fnCode rs m (pointers x fr ++ fixedSlots x fr)) :
    Atom.All fnCode rs' m' (pointers x fr ++ fixedSlots x fr) := by
  apply ChaChaRound.keepFrame _ f h
  have low := s.stack.readable.low
  have apart := s.stackBuf
  intro t ht
  simp only [pointers,fixedSlots,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ChaChaRound.pass,Outside,prefixFrame,blockScratch] <;> bv_omega

theorem setupAt {x fr m i rs} (s : Scope x fr m)
    (h : Atom.All fnCode rs m (live x i fr))
    (hs : Atom.All fnCode rs m (fixedSlots x fr)) :
    Atom.All fnCode rs m ((Full.layout (atBlock x i) (BitVec.ofNat 64 i)).atoms .setup fr ()) := by
  have stack := s.stack
  have code := s.stackCode
  unpack_atoms h []
  unpack_atoms hs []
  join_atoms [atBlock,Vector.getElem_set,UInt32.toBitVec_add]
  all_goals first | assumption | omega | rfl

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
