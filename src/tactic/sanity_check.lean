import tactic.core

open expr tactic

setup_tactic_parser

namespace string

meta def iterator.is_prefix : iterator → iterator → bool | n m :=
if ¬ n.has_next then tt
else if ¬ m.has_next then ff
else if n.curr ≠ m.curr then ff
else iterator.is_prefix n.next m.next

meta def is_prefix (s s' : string) : bool :=
s.mk_iterator.is_prefix s'.mk_iterator

end string

/-- A hackish way to get the `src` directory of mathlib. Requires the import of `tactic.cache`.
  The string probably ends with
    \mathlib\src\
  -/
meta def get_mathlib_dir : tactic string :=
do e ← get_env,
  s ← e.decl_olean `tactic.reset_instance_cache,
  return $ s.popn_back 17

/-- Checks whether a declaration with the given name is declared in mathlib -/
meta def is_in_mathlib (n : name) : tactic bool :=
do e ← get_env,
   ml ← get_mathlib_dir,
   let olean := e.decl_olean n,
   return $ ml.is_prefix $ olean.get_or_else ""

meta def check_unused_arguments_aux : list ℕ → ℕ → expr → list ℕ
:= λ l n e,
if ¬is_lambda e then
  if e = const `true.intro [] ∨ e = const `trivial [] then [] else l -- don't return if the target is true
else
  let b := e.binding_body in
  let l' := if b.has_var_idx 0 then l else n :: l in check_unused_arguments_aux l' (n+1) b

/- Check which arguments of expr are not used. We return [] if the body of `e` is `true.intro` or
  `trivial`, to filter many automatically generated declarations. -/
meta def check_unused_arguments (e : expr) : list ℕ :=
(check_unused_arguments_aux [] 1 e).reverse

meta def environment.mfold {α : Type} {m : Type → Type} [monad m] (e : environment) (x : α) (fn : declaration → α → m α) : m α :=
e.fold (return x) (λ d t, t >>= fn d)

/- Print all declarations where `tac` returns true and which has unused arguments.
  Automatically removes all internal declarations, and most declarations which prove `true`
  Returns a string of the form
    #print <name> -- <list of unused arguments>
-/
meta def get_all_unused_args_tac (tac : declaration → tactic bool) :
  tactic (list (declaration × list nat)) :=
do e ← get_env,
   e.mfold [] $ λ d ds, if name.is_internal d.to_name then return ds else
    do b ← tac d, if ¬ b then return ds else
    let l := check_unused_arguments d.value in
    if l = [] then return ds else
    return $ (d,l)::ds

namespace string
def popn (s : string) (n : nat) : string :=
(s.mk_iterator.nextn n).next_to_string
end string


open native

meta def get_all_unused_args_tac_sorted (tac : declaration → tactic bool) :
  tactic (list (string × list (declaration × list nat))) :=
do e ← get_env,
   ds ← get_all_unused_args_tac tac,
   let ds₂ := rb_lmap.of_list (ds.map (λ x, ((e.decl_olean x.1.to_name).get_or_else "", x))),
   return $ ds₂.to_list

meta def print_decls (ds : list (declaration × list nat)) : tactic unit :=
ds.mmap' $ λ x, trace (to_fmt "#print " ++ to_fmt x.1.to_name ++ " -- " ++ to_fmt x.2)

meta def print_all_decls (ds : list (string × list (declaration × list nat))) : tactic unit :=
ds.mmap' $ λ x, trace (to_fmt "-- " ++ to_fmt x.1) >> print_decls x.2

meta def print_all_decls_remove_prefix (ds : list (string × list (declaration × list nat))) :
  tactic unit :=
do n ← string.length <$> get_mathlib_dir,
   ds.mmap' $ λ x, trace (to_fmt "-- " ++ to_fmt (x.1.popn n)) >> print_decls x.2

/-- Get all declarations with unused arguments -/
meta def get_all_unused_args : tactic unit :=
get_all_unused_args_tac_sorted (λ d, return tt) >>= print_all_decls

/-- Get all declarations in mathlib with unused arguments -/
meta def get_all_unused_args_mathlib : tactic unit :=
-- get_all_unused_args_tac (λ d, is_in_mathlib d.to_name) >>= print_decls
get_all_unused_args_tac_sorted (λ d, is_in_mathlib d.to_name) >>= print_all_decls_remove_prefix

/-- Get all declarations in current file with unused arguments -/
meta def get_all_unused_args_current_file : tactic unit :=
get_all_unused_args_tac_sorted (λ d, do e ← get_env, return $ e.in_current_file d.to_name) >>=
  print_all_decls
