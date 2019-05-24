/-
Define notation which is localized to a namespace
Usage:
* Declare notation using:
```
localized_notation "local infix ` ⊹ ` := my_add" in my.add
```
* it will be available in the same section/namespace/file
* open it in other sections/files:
```
open_notation my.add --
```
The code is based on code from Gabriel Ebner from the hott3 repository
-/
import tactic.core
open lean lean.parser interactive tactic

@[user_attribute]
meta def localized_notation_attr : user_attribute unit name := {
    name := `_localized_notation,
    descr := "(interal) attribute that flags localized notation",
    parser := ident
}

-- TODO: speed up
meta def get_localized_notation (ns : list name) : tactic (list string) :=
do decls ← attribute.get_instances localized_notation_attr.name,
   decls ← decls.mfilter $ λ nm,
   (do par ← user_attribute.get_param localized_notation_attr nm, return $ ns.mem par),
   decls.mmap $ λ d, mk_const d >>= eval_expr string

@[user_command] meta def open_notation_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "open_notation") : parser unit :=
do ns ← many ident,
   cmds ← get_localized_notation ns,
   cmds.mmap' emit_code_here

def string_hash (s : string) : ℕ :=
s.fold 1 (λ h c, (33*h + c.val) % unsigned_sz)

@[user_command] meta def localized_notation_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "localized_notation") : parser unit :=
do cmd ← parser.pexpr, cmd ← i_to_expr cmd, cmd ← eval_expr string cmd,
   emit_code_here cmd,
   tk "in",
   nm ← ident,
   let dummy_decl_name := mk_num_name `_localized_notation_decl (string_hash cmd),
   add_decl (declaration.defn dummy_decl_name [] `(string) (reflect cmd)
    (reducibility_hints.regular 1 tt) ff),
   localized_notation_attr.set dummy_decl_name nm tt

meta def print_localized_notations (ns : list name) : tactic unit :=
do cmds ← get_localized_notation ns, cmds.mmap' trace
