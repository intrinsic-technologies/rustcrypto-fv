import P256.Proofs.Sec1.Decode.Prepare.Copy.Memory

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Buffer

open P256.Proofs.Sec1.Decode.Prepare.Copy

def copiedWindow {α : Type} (f : Nat → α) : Nat → α :=
  let f2 := update f (fun j ↦ f (168+j)) 240 2
  let f4 := update f2 (fun j ↦ f2 (170+j)) 242 1
  let f8 := update f4 (fun j ↦ f4 (179+j)) 48 8
  let f10 := update f8 (fun j ↦ f8 (187+j)) 56 8
  let f12 := update f10 (fun j ↦ f10 (195+j)) 64 8
  let f14 := update f12 (fun j ↦ f12 (203+j)) 72 8
  let f16 := update f14 (fun j ↦ f14 (211+j)) 80 8
  let f18 := update f16 (fun j ↦ f16 (219+j)) 88 8
  let f20 := update f18 (fun j ↦ f18 (225+j)) 94 8
  let f22 := update f20 (fun j ↦ f20 (94+j)) 158 8
  let f24 := update f22 (fun j ↦ f22 (88+j)) 152 8
  let f27 := update f24 (fun j ↦ f24 (48+j)) 112 8
  let f28 := update f27 (fun j ↦ f24 (56+j)) 120 8
  let f30 := update f28 (fun j ↦ f28 (64+j)) 128 8
  let f32 := update f30 (fun j ↦ f30 (72+j)) 136 8
  let f34 := update f32 (fun j ↦ f32 (80+j)) 144 8
  let f35 := update f34 (fun j ↦ f4 (175+j)) 247 4
  let f36 := update f35 (fun j ↦ f24 (48+j)) 251 8
  let f37 := update f36 (fun j ↦ f24 (56+j)) 259 8
  let f38 := update f37 (fun j ↦ f28 (64+j)) 267 8
  let f39 := update f38 (fun j ↦ f30 (72+j)) 275 8
  let f40 := update f39 (fun j ↦ f32 (80+j)) 283 8
  let f43 := update f40 (fun j ↦ f40 (152+j)) 291 8
  let f44 := update f43 (fun j ↦ f40 (158+j)) 297 8
  let f45 := update f44 (fun j ↦ f4 (171+j)) 243 4
  f45

theorem copiedWindow_map {α β : Type} (g : α → β) (f : Nat → α) :
    copiedWindow (fun i ↦ g (f i)) = fun i ↦ g (copiedWindow f i) := by
  simp only [copiedWindow,update_map]

theorem copiedWindow_eq (f : Nat → UInt8) {i : Nat} (hi : i<65) :
    copiedWindow f (240+i)=f (168+i) := by
  have index : ∀ j : Fin 65, copiedWindow (fun k ↦ k) (240+j.val)=168+j.val := by
    decide +kernel
  have mapped := congrFun (copiedWindow_map f (fun k ↦ k)) (240+i)
  change copiedWindow f (240+i)=f (copiedWindow (fun k ↦ k) (240+i)) at mapped
  rw [mapped,index ⟨i,hi⟩]

end P256.Proofs.EcdhWrapper.Peer.Buffer
