/-
Copyright (c) 2021 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import tactic.core
/-!
# Canonical declarations

This consists of two user-commands that allow you to define and use
canonical declarations for certain concepts (for example, all of the
`variables` to introduce algebraic objects such as a vector space).

It like a parameterized version of `tactic.localized_cmd` (and the code
is heavily inspired by it).

See the tactic doc entry below for more information.
-/

open lean lean.parser interactive tactic native

/-- Descriptor for a `def_declare`, constructed when building
the attribute cache.
It contains the number of parameters it expects, names for the
metavariables given in the `def_declare` (for debugging), and
a function that takes a list of that many parameters and produces
the code to evaluate. -/
meta structure canon_decl_def :=
(nparams : ℕ)
(default : list string)
(mk_cmd : list string → tactic string)

/-- The user attribute for canonical declarations. -/
@[user_attribute]
meta def canon_decl_attr : user_attribute (rb_lmap name canon_decl_def) unit := {
  name := "_canon_decl_attr",
  descr := "(interal) attribute for canonical declarations",
  parser := failed,
  cache_cfg := ⟨λ ns, (do dcls ← ns.mmap (λ n, mk_const n >>= eval_expr (name × canon_decl_def)),
                          return $ rb_lmap.of_list dcls), []⟩ }

/-- Get all commands for a given declaration and return them as a list -/
meta def get_canon_decls (n : name) (nparams : ℕ) : tactic (list canon_decl_def) :=
do m ← canon_decl_attr.get_cache,
   match m.find n with
   | [] := fail format!"canonical declaration {n} does not exist"
   | decls := return $ decls.filter (λ decl, decl.nparams = nparams)
   end

/-- Get all commands for a given declaration and return them as a list -/
meta def get_all_canon_decls (n : name) : tactic (list canon_decl_def) :=
do m ← canon_decl_attr.get_cache,
   match m.find n with
   | [] := fail format!"canonical declaration {n} does not exist"
   | decls := return $ decls
   end

/-- Execute all commands for the given type of canonical declaration. -/
@[user_command] meta def declare_cmd (_ : parse $ tk "declare") : parser unit :=
do do_print ← optional (tk "?"),
   n ← ident,
   args ← many ident,
   let args' := args.map name.to_string,
   decls ← get_canon_decls n args.length,
   when (decls.length = 0) $
     fail format!"no canonical declaration for {n} with {args.length} arguments",
   decls.mmap' $ λ d, do
     code ← d.mk_cmd args',
     when do_print.is_some $ trace ("Try this: " ++ code),
     emit_code_here code -- is it possible to print the code if this fails?

private meta def parse_declare_string (args : list name) (lst : pexpr) :
  string → list char → parser pexpr
| acc [] := pure $ pexpr.of_expr (reflect acc)
| acc ('%'::'%'::s) := parse_declare_string (acc ++ "%") s
| acc ('%'::'('::s) :=
do (e, s) ← with_input ident s.as_string,
   ')'::s ← return s.to_list | fail "')' expected",
   f ← parse_declare_string "" s,
   when (¬ e ∈ args) $ fail format!"no argument {e}",
   let i := args.index_of e,
   pure ``(%%(reflect acc) ++ to_string (option.get_or_else (list.nth %%lst %%i) "#error") ++ %%f)
| acc (c::s) := parse_declare_string (acc.str c) s

/-- Add a new command to a canonical declaration.
  The new command is added as a declaration to the environment with name `_canon_decl.<number>`.
  This declaration has attribute `_canon_decl_attr` and as value a `name × canon_decl_def`. -/
@[user_command] meta def def_declare_cmd (_ : parse $ tk "def_declare") : parser unit :=
do do_print ← optional (tk "?"),
   n ← ident,
   args ← many ident,
   tk ":=",
   cmd ← parser.pexpr,
   cmd ← i_to_expr cmd,
   cmd ← eval_expr string cmd,

   let v : pexpr := expr.var 0,
   cmd' ← parse_declare_string args v "" cmd.to_list,
   let f : pexpr := expr.lam "lst" binder_info.default ``(list string)
     ``(if list.length %%v = %%(list.length args)
        then pure %%cmd'
        else fail "(internal error) incorrect number of arguments"),
   let args' : list string := args.map name.to_string,
   let decl : pexpr := ``(prod.mk %%n (canon_decl_def.mk %%(list.length args) %%args' %%f)),
   decl ← i_to_expr decl,
   when do_print.is_some $ trace decl,

   env ← get_env,
   let dummy_decl_name := mk_num_name `_canon_decl
     ((string.hash (cmd ++ n.to_string) + env.fingerprint) % unsigned_sz),

   add_decl (declaration.defn dummy_decl_name [] `(name × canon_decl_def)
     decl (reducibility_hints.regular 1 tt) ff),
   canon_decl_attr.set dummy_decl_name unit.star tt

/--
This consists of two user-commands that allow you to define give
canonical declarations for certain concepts (for example, all of the
`variables` to introduce algebraic objects such as a vector space).

* Declare notation which is localized to a locale using:
```lean
def_declare algebra R A := "variables [semiring %(A)] [algebra %(R) %(A)]"
def_declare vector_space K V := "variables [add_comm_group %(V)] [module %(K) %(V)]"
```

* The following command will evaluate this code in a given section/namespace/file,
substituting `α` for `K` and `β` for `V`:
```lean
declare vector_space α β
```

* You can also use other declarations recursively:
```lean
class foo (α : Type*)
class bar (α : Type*) [foo α]

def_declare foo x :=
"variables [foo %(x)]"

def_declare bar x :=
"declare foo %(x)
variables [bar %(x)]"
```

* The same name can get multiple declarations, and they are selected by
the number of arguments.  If multiple match, they are evaluated in some
undetermined order. (TODO: can they be done in definition order?)

* To see all declaration definitions for a given name, run:
```lean
run_cmd print_canon_decl_commands `vector_space
run_cmd print_canon_decl_commands `vector_space ["α", "β"]
```
When given arguments, it shows only those declarations that apply.

* To see what a `def_declare` is defining, use `def_declare?`:
```lean
def_declare? vector_space K V := "variables [add_comm_group %(V)] [module %(K) %(V)]"
```

* To see what a `declare` is evaluating, use `declare?`:
```lean
declare? vector_space α β
```

* To see a list of all names with declarations, run:
```lean
run_cmd do
  m ← canon_decl_attr.get_cache,
  tactic.trace m.keys
```

* Warning: You have to give full names of all declarations used in declarations
  so that they also work when the appropriate namespaces are not opened.
-/
add_tactic_doc
{ name                     := "canonical declarations",
  category                 := doc_category.cmd,
  decl_names               := [`def_declare_cmd, `declare_cmd],
  tags                     := ["notation", "type classes"] }

/-- Print all commands in a given locale -/
meta def print_canon_decl_commands (n : name) : opt_param (option (list string)) none → tactic unit
| none :=
  do cmds ← get_all_canon_decls n,
     cmds.mmap' $ λ d, do
       trace format!"declaration {n} {string.intercalate \" \" d.default}: ",
       d.mk_cmd d.default >>= trace
| (some args) :=
  do cmds ← get_canon_decls n args.length,
     cmds.mmap' $ λ d, do
       trace format!"declaration {n} {string.intercalate \" \" args}: ",
       d.mk_cmd args >>= trace
