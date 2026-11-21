import ChaCha20Poly1305.Proofs.Callee100a80.Defs
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Rounds
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Xor
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Tail

namespace ChaCha20Poly1305.Proofs.Callee100a80.Run


open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 ChaCha20Poly1305.Proofs.ChaCha20

                                                                                 
def sp (s : RamState) : BitVec 64 := stackPtr s - BitVec.ofNat 64 frameBytes

                                                
def st (s : RamState) : BitVec 64 := rdi.read s

                                        
def msg (message : ByteArray) : Nat → UInt8 := fun i => message[i]!

                                         
def nblocks (size : Nat) : Nat := size / 64

                                                                                        
def words (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12) (j : Nat) :
    Vector UInt32 16 :=
  initialState key (counter + j.toUInt32) nonce

                                           
def block (message : ByteArray) (j : Nat) : Vector UInt8 64 :=
  Vector.ofFn fun i => message[64 * j + i.val]!

                                             
def mixed (x : Vector UInt32 16) : Vector UInt32 16 := Nat.repeat doubleRound 10 x

                                                           
def Prefix (output : BitVec 64) (cipher : ByteArray) (upto : Nat) (t : RamState) : Prop :=
  ∀ i < upto, t.external[output + BitVec.ofNat 64 i]? = some cipher[i]!

                                                                                           
                                                                                                
                                                                                                
                      
structure Head [Bindings] (s : RamState) (key : Vector UInt8 32) (counter : UInt32)
    (nonce : Vector UInt8 12) (input output : BitVec 64) (message : ByteArray) (j : Nat)
    (t : RamState) : Prop where
  frame : Frame s t output message.size
  rip : t.RIP = 0x100c70
  lt : j < nblocks message.size
  rdi : Cuts.Xor.reg64 t 7 = BitVec.ofNat 64 j
  r12 : Cuts.Xor.reg64 t 12 = (words key counter nonce j)[12].toBitVec.setWidth 64
  r10 : Cuts.Xor.reg64 t 10 = (words key counter nonce j)[4].toBitVec.setWidth 64
  r11 : Cuts.Xor.reg64 t 11 = (words key counter nonce j)[8].toBitVec.setWidth 64
  r8 : Cuts.Xor.reg64 t 8 = (words key counter nonce j)[13].toBitVec.setWidth 64
  inits : ∀ e ∈ Cuts.Xor.initSlot, e.1 ≠ 12 →
    Cuts.Xor.slot32 t e.2 = (words key counter nonce j)[e.1].toBitVec
  inSlot : Cuts.Xor.slot64 t 0x68 = input
  outSlot : Cuts.Xor.slot64 t 0x60 = output
  count : Cuts.Xor.slot64 t 0x50 = BitVec.ofNat 64 (nblocks message.size)
  slots : Cuts.Tail.Slots (sp s) (st s) input output message.size t
  state : (wordsRegion s).HasBytes t.external (stateBytes key counter nonce)
  rest : Cuts.Tail.Rest input message.size (msg message) (64 * j) t
  wrote : Prefix output (chacha20Encrypt key counter nonce message) (64 * j) t

                                                                                           
                                                                                           
structure Kept [Bindings] (s : RamState) (key : Vector UInt8 32) (counter : UInt32)
    (nonce : Vector UInt8 12) (input output : BitVec 64) (message : ByteArray) (j : Nat)
    (t : RamState) : Prop where
  frame : Frame s t output message.size
  lt : j < nblocks message.size
  index : Cuts.Xor.slot64 t 0x70 = BitVec.ofNat 64 j
  inits : ∀ e ∈ Cuts.Xor.initSlot,
    Cuts.Xor.slot32 t e.2 = (words key counter nonce j)[e.1].toBitVec
  inSlot : Cuts.Xor.slot64 t 0x68 = input
  outSlot : Cuts.Xor.slot64 t 0x60 = output
  count : Cuts.Xor.slot64 t 0x50 = BitVec.ofNat 64 (nblocks message.size)
  slots : Cuts.Tail.Slots (sp s) (st s) input output message.size t
  state : (wordsRegion s).HasBytes t.external (stateBytes key counter nonce)
  rest : Cuts.Tail.Rest input message.size (msg message) (64 * j) t
  wrote : Prefix output (chacha20Encrypt key counter nonce message) (64 * j) t

                                                                                      
                                                 
structure Mixing [Bindings] (s : RamState) (key : Vector UInt8 32) (counter : UInt32)
    (nonce : Vector UInt8 12) (input output : BitVec 64) (message : ByteArray) (j : Nat)
    (t : RamState) : Prop where
  kept : Kept s key counter nonce input output message j t
  rip : t.RIP = 0x100cd0
  rframe : Cuts.Rounds.RFrame (sp s) t
  words : Write.AllHold t (Cuts.Rounds.cut (sp s) Cuts.Rounds.mainBase (words key counter nonce j))
  rounds : (Operand.mem (sp s + 0x78) : Operand 64).read t = BitVec.ofNat 64 (9 + 1)

                                                                                      
structure AtTail [Bindings] (s : RamState) (key : Vector UInt8 32) (counter : UInt32)
    (nonce : Vector UInt8 12) (input output : BitVec 64) (message : ByteArray)
    (t : RamState) : Prop where
  frame : Frame s t output message.size
  cut : Cuts.Tail.TailCut (sp s) (st s) input output message.size (msg message)
    (words key counter nonce (nblocks message.size)) t
  wrote : Prefix output (chacha20Encrypt key counter nonce message)
    (64 * nblocks message.size) t

theorem hb_cut {boundary : ReturnBoundary}
    (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat) :
    boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat := by
  have he : entry.toNat = 0x100a80 := rfl
  have hc : codeEnd = 0x1014bc := rfl
  rw [he, hc] at hb
  exact hb

end ChaCha20Poly1305.Proofs.Callee100a80.Run
