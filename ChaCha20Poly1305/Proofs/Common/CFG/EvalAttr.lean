import Lean

register_simp_attr cfg_eval

namespace ChaCha20Poly1305.Proofs.CFG

initialize cfgBlockAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `cfg_block "a definition cfg_eval unfolds to look up and run a block"

end ChaCha20Poly1305.Proofs.CFG
