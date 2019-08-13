import tactic.core

universe variable u
open expr tactic native

setup_tactic_parser

reserve notation `#sanity_check`
reserve notation `#sanity_check_mathlib`

-- to other files
namespace string

/-- Tests whether the first string is a prefix of the second string -/
def is_prefix : string → string → bool | ⟨s⟩ ⟨t⟩ := s.is_prefix_of t

/-- Removes the first `n` elements from the string `s` -/
def popn (s : string) (n : nat) : string :=
(s.mk_iterator.nextn n).next_to_string

end string

meta def environment.mfold {α : Type} {m : Type → Type} [monad m] (e : environment) (x : α)
  (fn : declaration → α → m α) : m α :=
e.fold (return x) (λ d t, t >>= fn d)

namespace declaration
/-- Checks whether the declaration is declared in the current file. A simple wrapper around
  `environment.in_current_file` -/
meta def in_current_file (d : declaration) : tactic bool :=
do e ← get_env, return $ e.in_current_file' d.to_name

meta def is_constant : declaration → bool
| (cnst _ _ _ _) := tt
| _              := ff

meta def is_axiom : declaration → bool
| (ax _ _ _) := tt
| _          := ff

end declaration

namespace name
/-- Get the postfix of a name, assuming it is a string. -/
def get_postfix : name → string
| anonymous        := ""
| (mk_string s p)  := s
| (mk_numeral s p) := ""
end name

/-- A hackish way to get the `src` directory of mathlib. -/
meta def get_mathlib_dir : tactic string :=
do e ← get_env,
  s ← e.decl_olean `tactic.reset_instance_cache,
  return $ s.popn_back 17

/-- Checks whether `ml` is a prefix of the file where `n` is declared.
  If you want to run `is_in_mathlib` many times, you should use this tactic instead,
  since it is expensive to execute get_mathlib_dir many times. -/
meta def is_in_mathlib_aux (ml : string) (n : name) : tactic bool :=
do e ← get_env, return $ ml.is_prefix $ (e.decl_olean n).get_or_else ""

/-- Checks whether a declaration with the given name is declared in mathlib -/
meta def is_in_mathlib (n : name) : tactic bool :=
do ml ← get_mathlib_dir, is_in_mathlib_aux ml n

/-- Auxilliary definition for `expr.pi_arity` -/
meta def expr.pi_arity_aux : ℕ → expr → ℕ
| n (pi _ _ _ b) := expr.pi_arity_aux (n + 1) b
| n e            := n

/-- The arity of a pi-type. Does not perform any reduction.
  In one application this was ~30 times quicker than tactic.get_pi_arity -/
meta def expr.pi_arity : expr → ℕ :=
expr.pi_arity_aux 0


/-- Find all (non-internal) declarations where tac returns `some x` and list them. -/
meta def fold_over_with_cond {α} (tac : declaration → tactic (option α)) :
  tactic (list (declaration × α)) :=
do e ← get_env,
   e.mfold [] $ λ d ds,
     if name.is_internal d.to_name then return ds else
     do o ← tac d,
     if h : o.is_some then return $ (d, option.get h)::ds else return ds

/-- Find all declarations where tac returns `some x` and sort the resulting list by file name. -/
meta def fold_over_with_cond_sorted {α} (tac : declaration → tactic (option α)) :
  tactic (list (string × list (declaration × α))) :=
do e ← get_env,
   ds ← fold_over_with_cond tac,
   let ds₂ := rb_lmap.of_list (ds.map (λ x, ((e.decl_olean x.1.to_name).get_or_else "", x))),
   return $ ds₂.to_list

/-- Make the output of `fold_over_with_cond` printable, in the following form:
      #print <name> -- <elt of α> -/
meta def print_decls {α} [has_to_format α] (ds : list (declaration × α)) : format :=
ds.foldl
  (λ f x, f ++ format.line ++ to_fmt "#print " ++ to_fmt x.1.to_name ++ " -- " ++ to_fmt x.2)
  format.nil

/-- Make the output of `fold_over_with_cond_sorted` printable, with the file path + name inserted.-/
meta def print_decls_sorted {α} [has_to_format α] (ds : list (string × list (declaration × α))) :
  format :=
ds.foldl
  (λ f x, f ++ format.line ++ format.line ++ to_fmt "-- " ++ to_fmt x.1 ++ print_decls x.2)
  format.nil

/- Print all (non-internal) declarations where tac return `some x`-/
meta def print_all_decls {α} [has_to_format α] (tac : declaration → tactic (option α)) :
  tactic format :=
print_decls_sorted <$> fold_over_with_cond_sorted tac

/- Print (non-internal) declarations in the current file where tac return `some x`-/
meta def print_decls_current_file {α} [has_to_format α] (tac : declaration → tactic (option α)) :
  tactic format :=
print_decls <$> fold_over_with_cond
  (λ d, if name.is_internal d.to_name then return none else
    d.in_current_file >>= λ b,
      if b then tac d else return none)

/- Print (non-internal) declarations in mathlib where tac return `some x` -/
meta def print_decls_mathlib {α} [has_to_format α] (tac : declaration → tactic (option α)) :
  tactic format :=
do ml ← get_mathlib_dir,
   f ← fold_over_with_cond_sorted
   (λ d, is_in_mathlib_aux ml d.to_name >>= λ b,
      if b then tac d else return none),
   return $ print_decls_sorted $ f.map (λ x, ⟨x.1.popn ml.length, x.2⟩)

/-- Auxilliary definition for `check_unused_arguments_aux` -/
meta def check_unused_arguments_aux : list ℕ → ℕ → ℕ → expr → list ℕ
:= λ l n n_max e,
if n > n_max then l else
if ¬is_lambda e then
  if e = const `true.intro [] ∨ e = const `trivial [] then [] else l -- don't return if the target is true
else
  let b := e.binding_body in
  let l' := if b.has_var_idx 0 then l else n :: l in check_unused_arguments_aux l' (n+1) n_max b

/-- Check which arguments of a declaration are not used.
  Prints a list of natural numbers corresponding to which arguments are not used (e.g.
    this outputs [1, 4] if the first and fourth arguments are unused).
  We return [] if the body of `e` is `true.intro` or `trivial`,
    to filter many automatically generated declarations.
  We don't print arguments that are larger than the arity of the type of the declaration. -/
meta def check_unused_arguments (d : declaration) : option (list ℕ) :=
let l := check_unused_arguments_aux [] 1 (d.type.pi_arity) d.value in
if l = [] then none else l.reverse

/-- Get all declarations with unused arguments -/
meta def get_all_unused_args : tactic unit :=
print_all_decls (return ∘ check_unused_arguments) >>= trace

/-- Get all declarations in mathlib with unused arguments -/
meta def get_all_unused_args_mathlib : tactic unit :=
print_decls_mathlib (return ∘ check_unused_arguments) >>= trace

/-- Get all declarations in current file with unused arguments. -/
meta def get_all_unused_args_current_file : tactic unit :=
print_decls_current_file (return ∘ check_unused_arguments) >>= trace

/-- Checks whether the correct declaration constructor (definition of theorem) by comparing it
  to its sort. This will automatically remove all instances and automatically generated
  definitions -/
meta def correct_decl_constr (d : declaration) : tactic (option string) :=
do
  e ← get_env,
  expr.sort n ← infer_type d.type,
  if d.is_constant ∨ d.is_axiom ∨ (e.is_projection d.to_name).is_some ∨
    (d.is_definition : bool) = (n ≠ level.zero : bool) ∨
    (d.to_name.get_postfix ∈ ["inj","inj_eq","sizeof_spec"] ∧
      e.is_constructor d.to_name.get_prefix) ∨
    (d.to_name.get_postfix ∈ ["dcases_on","drec_on","drec","cases_on","rec_on","binduction_on"] ∧
      e.is_inductive d.to_name.get_prefix)
    then return none
    else (option.is_some <$> try_core (has_attribute `instance d.to_name)) >>=
    λ b, return $ if b then none
    else if (d.is_definition : bool) then "is a def, should be a lemma/theorem"
    else "is a lemma/theorem, should be a def"

/-- Get all declarations in mathlib incorrectly marked as def/lemma -/
meta def get_all_decl_const_mathlib : tactic unit :=
print_decls_mathlib (return ∘ check_unused_arguments) >>= trace

/-- The command `#sanity_check` at the bottom of a file will warn you about some common mistakes
  in that file. -/
@[user_command] meta def sanity_check_cmd (_ : parse $ tk "#sanity_check") : parser unit :=
do
  trace "/- Note: This command is still in development. -/\n",
  f ← print_decls_current_file (return ∘ check_unused_arguments),
  if f.is_nil then trace "/- OK: No unused arguments in the current file. -/"
  else trace (to_fmt "/- Unused arguments in the current file: -/" ++ f ++ format.line),
  f ← print_decls_current_file correct_decl_constr,
  if f.is_nil then trace "/-OK: All declarations correctly marked as def/lemma -/"
  else trace (to_fmt "/- Declarations incorrectly marked as def/lemma: -/" ++ f ++ format.line),
  skip

/-- The command `#sanity_check` at the bottom of a file will warn you about some common mistakes
  in that file. -/
@[user_command] meta def sanity_check_mathlib_cmd (_ : parse $ tk "#sanity_check_mathlib") :
  parser unit :=
do
  trace "/- Note: This command is still in development. -/\n",
  f ← print_decls_mathlib (return ∘ check_unused_arguments),
  trace (to_fmt "/- UNUSED ARGUMENTS: -/" ++ f ++ format.line),
  f ← print_decls_mathlib correct_decl_constr,
  trace (to_fmt "/- INCORRECT DEF/LEMMA: -/" ++ f ++ format.line),
  skip

-- #sanity_check
-- #sanity_check_mathlib
