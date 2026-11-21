import Sha2.Proofs.Common.SHA256.Initialize.Blocks

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Initialize

variable {v : Sha2.Proofs.Wrapper.Variant}

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

structure Layout (v : Sha2.Proofs.Wrapper.Variant := .sha256) where
  start : BitVec 64
  words : Vector (WordStore v) 4
  clear : Clear

def Layout.wordPC (l : Layout v) (i : Nat) : BitVec 64 :=
  l.start + BitVec.ofNat 64
    ((l.words.toArray.toList.take i).map WordStore.bytes |>.map List.length |>.sum)

def Layout.bytes (l : Layout v) : List UInt8 :=
  l.words.toArray.toList.flatMap WordStore.bytes ++ l.clear.bytes

def Layout.finish (l : Layout v) : BitVec 64 := l.start + BitVec.ofNat 64 l.bytes.length

structure Layout.Valid (l : Layout v) : Prop where
  order : ∀ i : Fin 4, (l.words[i]).index.val = 3 - i.val
  addressing : ∀ i : Fin 4, (l.words[i]).destination.mode.Valid
  independentWords : ∀ i j : Fin 4, (l.words[i]).loadConstant = true →
    (l.words[i]).register ≠ (l.words[j]).destination.base
  independentCounter : ∀ i : Fin 4, (l.words[i]).loadConstant = true →
    (l.words[i]).register ≠ l.clear.counter.base
  independentTail : ∀ i : Fin 4, (l.words[i]).loadConstant = true →
    (l.words[i]).register ≠ l.clear.tail.base
  independentStack : ∀ i : Fin 4, (l.words[i]).loadConstant = true →
    (l.words[i]).register ≠ 4
  preservedValues : ∀ i j : Fin 4, i.val < j.val →
    (l.words[i]).loadConstant = true → (l.words[j]).loadConstant = false →
    (l.words[i]).register ≠ (l.words[j]).register

structure Pre (l : Layout v) (base : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = l.start
  valid : l.Valid
  baseReadable : MemReadable s base 104
  words : ∀ i : Fin 4, (l.words[i]).Pre (l.wordPC i.val)
    { s with RIP := l.wordPC i.val }
  addresses : ∀ i : Fin 4, (l.words[i]).destination.read s =
    base + 64 + BitVec.ofNat 64 (8 * (l.words[i]).index.val)
  counter : l.clear.counter.read s = base + 96
  tail : l.clear.tail.read s = base + 63
  clear : l.clear.Pre (l.wordPC 4) { s with RIP := l.wordPC 4 }
  codeApart : RangeApart base 104 l.start l.bytes.length

def Layout.components (l : Layout v) (base : BitVec 64) : List Component :=
  (l.words.toArray.toList.filter WordStore.loadConstant).map
      (fun b => Component.reg (b.register.setWidth 5)) ++
    [.mem (base + 64) 32, .mem (base + 96) 8, .mem (base + 63) 1, .rip]

structure Post (l : Layout v) (base : BitVec 64) (s t : RamState) : Prop where
  rip : t.RIP = l.finish
  hasher : HasherAt t base ByteArray.empty v.initialHash
  rsp : stackPtr t = stackPtr s
  frame : AgreesExcept (l.components base) s t
  finalConstant : ∀ i : Fin 4, (l.words[i]).loadConstant = true →
    (∀ j : Fin 4, i.val < j.val → (l.words[j]).loadConstant = true →
      (l.words[j]).register ≠ (l.words[i]).register) →
    (.reg ((l.words[i]).register.setWidth 5) : Operand 64).read t =
      packedWord (l.words[i]).index v

def Contract [Bindings] (boundary : ReturnBoundary) (l : Layout v) : Prop :=
  ∀ base, AdvanceTriple boundary (Pre l base) (codeRange l.start l.bytes) (Post l base)

end Sha2.Proofs.Common.SHA256.Initialize
