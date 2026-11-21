import Lean.Elab.Command

namespace K256.Proofs.Generate.Generator.Multiply

open Lean Elab Command in
elab "open_generator_loop " path:ident " (" decls:ident+ ")" : command => do
  let ns := `K256.Proofs.Generate.Generator.Multiply
  let mod := ns ++ `Loop ++ path.getId
  for decl in decls do
    let name := mkPrivateNameCore mod (ns ++ decl.getId)
    modifyScope fun scope => { scope with openDecls := .explicit decl.getId name :: scope.openDecls }

end K256.Proofs.Generate.Generator.Multiply
