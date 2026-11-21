import ChaCha20Poly1305.Proofs.Decrypt.InstallStep
import ChaCha20Poly1305.Proofs.Decrypt.InitCall
import ChaCha20Poly1305.Proofs.Decrypt.KeyCall

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Poly1305 Standards.RFC.ChaCha20Poly1305

structure Packet where
  key : Vector UInt8 32
  nonce : Vector UInt8 12
  aad : ByteArray
  ct : ByteArray
  tag : BitVec 128
  pa : BitVec 64
  buf : BitVec 64
  n : BitVec 64
  length : n.toNat=ct.size
  small : n.toNat<2^32

def Packet.one (p : Packet) := poly1305KeyGen p.key p.nonce
def Packet.computed (p : Packet) := tagBits (poly1305Mac (aeadMacData p.aad p.ct) p.one)
def Packet.good (p : Packet) := decide (p.computed=p.tag)
def Packet.plain (p : Packet) := chacha20Encrypt p.key 1 p.nonce p.ct
def Packet.stream (p : Packet) : Stream.Input := ⟨Stream.words p.key p.nonce 1,p.buf,p.n,p.small⟩
def Packet.src (p : Packet) := Stream.encode p.ct p.n.toNat
def Packet.dst (p : Packet) := Stream.encode p.plain p.n.toNat
def Packet.x (p : Packet) := raw p.key p.nonce

@[refine_layout] def physical (fr : Activation) :=
  {fr with rsp:=fr.rsp-440,rbx:=fr.r8,rbp:=fr.rcx,r13:=fr.rdx,r14:=fr.r9}

@[refine_layout] def extraIn (p : Packet) (fr : Activation) : List Atom :=
  [.readable fr.r8 24,.readable (fr.rsp+8) 8,.readable p.pa p.aad.size,.writable p.buf p.n.toNat,
   .fact (fr.rsp.toNat≤0x1001f0 ∨ 0x102e00+864≤fr.rsp.toNat),
   .fact (fr.rsp.toNat+8≤fr.r8.toNat),
   .fact (p.pa.toNat+p.aad.size≤fr.rsp.toNat-864 ∨ fr.rsp.toNat+8≤p.pa.toNat),
   .fact (p.buf.toNat+p.n.toNat≤fr.rsp.toNat-864 ∨ fr.rsp.toNat+8≤p.buf.toNat),
   .fact (p.buf.toNat+p.n.toNat≤fr.r8.toNat ∨ fr.r8.toNat+24≤p.buf.toNat),
   .fact (p.buf.toNat+p.n.toNat≤0x100a80 ∨ 0x1014bc≤p.buf.toNat),
   .fact (fr.rcx.toNat=p.aad.size),.fact (fr.rcx.toNat<2^32),.fact (0<p.aad.size → fr.rdx=p.pa),
   .fact (fr.r9=p.tag.extractLsb' 0 64),
   .mem (fr.rsp+8) 64 (p.tag.extractLsb' 64 64),.mem p.pa (8*p.aad.size) (Bytes.packed p.aad),
   .mem p.buf (8*p.n.toNat) p.src] ++ vec fr.r8 p.buf p.n

@[refine_layout] def detachedFn (p : Packet) : Callee where
  entry := .l1001f0
  abi := Fn1001f0.frameAt .l1001f0
  pre fr := srcGeo fr ++ inputs p.x fr ++ extraIn p fr
  post _ := [.low 0 8 (if p.good then 0 else 1)] ++ (if p.good then [.mem p.buf (8*p.n.toNat) p.dst] else [])
  writes _ := if p.good then [⟨p.buf.toNat,p.n.toNat⟩] else []

def innerZone (fr : Activation) : List MemoryRegion := [⟨fr.rsp.toNat-864,816⟩]
def atEntry (fr : Activation) (m : Ram) := {fr with original:=m,low:=fr.rsp-864}

@[refine_layout] def preserved (fr : Activation) : List Atom :=
  [.mem (fr.rsp-48) 64 fr.rbx,.mem (fr.rsp-40) 64 fr.r12,.mem (fr.rsp-32) 64 fr.r13,
    .mem (fr.rsp-24) 64 fr.r14,.mem (fr.rsp-16) 64 fr.r15,.mem (fr.rsp-8) 64 fr.rbp,
    .readable fr.rsp 8,.mem fr.rsp 64 fr.ret,.fact (fr.ret.toNat<2^32),
    .writable (fr.rsp-864) 864,.fact (fr.low.toNat+864≤fr.rsp.toNat),.fact (fr.rsp.toNat%16=8)]

theorem keepExt {p : Packet} {fr rs rs' m m' regs} (h : Atom.All fnCode rs m (extraIn p fr))
    (f : RamWriteFrame m m' regs) (le : RegionsWithin regs [⟨fr.rsp.toNat-864,864⟩])
    (sp : 864≤fr.rsp.toNat) (low : fr.rsp.toNat+16≤2^32) : Atom.All fnCode rs' m' (extraIn p fr) := by
  have z := widen f le
  have ctx := h
  unpack_atoms ctx []
  apply ChaChaRound.keepFrame _ z h
  intro t ht
  simp only [extraIn,vec,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ChaChaRound.pass,Outside] <;> bv_omega

theorem innerOuter (fr : Activation) (h : 864≤fr.rsp.toNat) :
    RegionsWithin (innerZone fr) [⟨fr.rsp.toNat-864,864⟩] := by simp [innerZone,RegionsWithin]; omega

theorem keepSaved {fr rs rs' m m' regs} (h : Atom.All fnCode rs m (preserved fr))
    (f : RamWriteFrame m m' regs) (sp : 864≤fr.rsp.toNat)
    (le : RegionsWithin regs (innerZone fr)) : Atom.All fnCode rs' m' (preserved fr) := by
  have z := widen f le
  have low := (show Readable m fr.rsp 8 by unpack_atoms h []; assumption).low
  apply ChaChaRound.keepFrame _ z h
  intro t ht
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ChaChaRound.pass,Outside,innerZone] <;> bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Detached
