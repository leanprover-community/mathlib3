/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis
-/
import data.string.defs
/-!
# Additional operations on expr and related types

 This file defines basic operations on the types expr, name, declaration, level, environment.

 This file is mostly for non-tactics. Tactics should generally be placed in `tactic.core`.

 ## Tags
 expr, name, declaration, level, environment, meta, metaprogramming, tactic
-/

namespace binder_info

instance : inhabited binder_info := ⟨ binder_info.default ⟩

/-- The brackets corresponding to a given binder_info. -/
def brackets : binder_info → string × string
| binder_info.implicit        := ("{", "}")
| binder_info.strict_implicit := ("{{", "}}")
| binder_info.inst_implicit   := ("[", "]")
| _                           := ("(", ")")

end binder_info

namespace name

/-- Find the largest prefix `n` of a `name` such that `f n ≠ none`, then replace this prefix
with the value of `f n`. -/
def map_prefix (f : name → option name) : name → name
| anonymous := anonymous
| (mk_string s n') := (f (mk_string s n')).get_or_else (mk_string s $ map_prefix n')
| (mk_numeral d n') := (f (mk_numeral d n')).get_or_else (mk_numeral d $ map_prefix n')

/-- If `nm` is a simple name (having only one string component) starting with `_`, then `deinternalize_field nm` removes the underscore. Otherwise, it does nothing. -/
meta def deinternalize_field : name → name
| (mk_string s name.anonymous) :=
  let i := s.mk_iterator in
  if i.curr = '_' then i.next.next_to_string else s
| n := n

/-- `get_nth_prefix nm n` removes the last `n` components from `nm` -/
meta def get_nth_prefix : name → ℕ → name
| nm 0 := nm
| nm (n + 1) := get_nth_prefix nm.get_prefix n

/-- Auxilliary definition for `pop_nth_prefix` -/
private meta def pop_nth_prefix_aux : name → ℕ → name × ℕ
| anonymous n := (anonymous, 1)
| nm n := let (pfx, height) := pop_nth_prefix_aux nm.get_prefix n in
          if height ≤ n then (anonymous, height + 1)
          else (nm.update_prefix pfx, height + 1)

/-- Pops the top `n` prefixes from the given name. -/
meta def pop_nth_prefix (nm : name) (n : ℕ) : name :=
prod.fst $ pop_nth_prefix_aux nm n

/-- Pop the prefix of a name -/
meta def pop_prefix (n : name) : name :=
pop_nth_prefix n 1

/-- Auxilliary definition for `from_components` -/
private def from_components_aux : name → list string → name
| n [] := n
| n (s :: rest) := from_components_aux (name.mk_string s n) rest

/-- Build a name from components. For example `from_components ["foo","bar"]` becomes
  ``` `foo.bar``` -/
def from_components : list string → name :=
from_components_aux name.anonymous

/-- `name`s can contain numeral pieces, which are not legal names
  when typed/passed directly to the parser. We turn an arbitrary
  name into a legal identifier name by turning the numbers to strings. -/
meta def sanitize_name : name → name
| name.anonymous := name.anonymous
| (name.mk_string s p) := name.mk_string s $ sanitize_name p
| (name.mk_numeral s p) := name.mk_string sformat!"n{s}" $ sanitize_name p

/-- Append a string to the last component of a name -/
def append_suffix : name → string → name
| (mk_string s n) s' := mk_string (s ++ s') n
| n _ := n

/-- The first component of a name, turning a number to a string -/
meta def head : name → string
| (mk_string s anonymous) := s
| (mk_string s p)         := head p
| (mk_numeral n p)        := head p
| anonymous               := "[anonymous]"

/-- Tests whether the first component of a name is `"_private"` -/
meta def is_private (n : name) : bool :=
n.head = "_private"

/-- Get the last component of a name, and convert it to a string. -/
meta def last : name → string
| (mk_string s _)  := s
| (mk_numeral n _) := repr n
| anonymous        := "[anonymous]"

/-- Returns the number of characters used to print all the string components of a name,
  including periods between name segments. Ignores numerical parts of a name. -/
meta def length : name → ℕ
| (mk_string s anonymous) := s.length
| (mk_string s p)         := s.length + 1 + p.length
| (mk_numeral n p)        := p.length
| anonymous               := "[anonymous]".length

end name

namespace level

/-- Tests whether a universe level is non-zero for all assignments of its variables -/
meta def nonzero : level → bool
| (succ _) := tt
| (max l₁ l₂) := l₁.nonzero || l₂.nonzero
| (imax _ l₂) := l₂.nonzero
| _ := ff

end level

namespace expr
open tactic

/-- Apply a function to each constant (inductive type, defined function etc) in an expression. -/
protected meta def apply_replacement_fun (f : name → name) (e : expr) : expr :=
e.replace $ λ e d,
  match e with
  | expr.const n ls := some $ expr.const (f n) ls
  | _ := none
  end

/-- Turns an expression into a positive natural number, assuming it is only built up from
  `has_one.one`, `bit0` and `bit1`. -/
protected meta def to_pos_nat : expr → option ℕ
| `(has_one.one _) := some 1
| `(bit0 %%e) := bit0 <$> e.to_pos_nat
| `(bit1 %%e) := bit1 <$> e.to_pos_nat
| _           := none

/-- Turns an expression into a natural number, assuming it is only built up from
  `has_one.one`, `bit0`, `bit1` and `has_zero.zero`. -/
protected meta def to_nat : expr → option ℕ
| `(has_zero.zero _) := some 0
| e                  := e.to_pos_nat

/-- Turns an expression into a integer, assuming it is only built up from
  `has_one.one`, `bit0`, `bit1`, `has_zero.zero` and a optionally a single `has_neg.neg` as head. -/
protected meta def to_int : expr → option ℤ
| `(has_neg.neg %%e) := do n ← e.to_nat, some (-n)
| e                  := coe <$> e.to_nat

/-- Tests whether an expression is a meta-variable. -/
meta def is_mvar : expr → bool
| (mvar _ _ _) := tt
| _            := ff

/-- Tests whether an expression is a sort. -/
meta def is_sort : expr → bool
| (sort _) := tt
| e         := ff

/-- Returns a list of all local constants in an expression (without duplicates). -/
meta def list_local_consts (e : expr) : list expr :=
e.fold [] (λ e' _ es, if e'.is_local_constant then insert e' es else es)

/-- Returns a name_set of all constants in an expression. -/
meta def list_constant (e : expr) : name_set :=
e.fold mk_name_set (λ e' _ es, if e'.is_constant then es.insert e'.const_name else es)

/-- Returns a list of all meta-variables in an expression (without duplicates). -/
meta def list_meta_vars (e : expr) : list expr :=
e.fold [] (λ e' _ es, if e'.is_mvar then insert e' es else es)

/-- Returns a name_set of all constants in an expression starting with a certain prefix. -/
meta def list_names_with_prefix (pre : name) (e : expr) : name_set :=
e.fold mk_name_set $ λ e' _ l,
  match e' with
  | expr.const n _ := if n.get_prefix = pre then l.insert n else l
  | _ := l
  end

/-- Returns a name_set of all constants in an expression.
  Returns `true` if `n` is `name.anonymous` -/
meta def contains_constant (e : expr) (n : name) : bool :=
e.fold ff (λ e' _ b, if e'.const_name = n then tt else b)

/--
 is_num_eq n1 n2 returns true if n1 and n2 are both numerals with the same numeral structure,
 ignoring differences in type and type class arguments.
-/
meta def is_num_eq : expr → expr → bool
| `(@has_zero.zero _ _) `(@has_zero.zero _ _) := tt
| `(@has_one.one _ _) `(@has_one.one _ _) := tt
| `(bit0 %%a) `(bit0 %%b) := a.is_num_eq b
| `(bit1 %%a) `(bit1 %%b) := a.is_num_eq b
| `(-%%a) `(-%%b) := a.is_num_eq b
| `(%%a/%%a') `(%%b/%%b') :=  a.is_num_eq b
| _ _ := ff

/-- Simplifies the expression `t` with the specified options.
  The result is `(new_e, pr)` with the new expression `new_e` and a proof
  `pr : e = new_e`. -/
meta def simp (t : expr)
  (cfg : simp_config := {}) (discharger : tactic unit := failed)
  (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) :
  tactic (expr × expr) :=
do (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
   simplify s to_unfold t cfg `eq discharger

/-- Definitionally simplifies the expression `t` with the specified options.
  The result is the simplified expression. -/
meta def dsimp (t : expr)
  (cfg : dsimp_config := {})
  (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) :
  tactic expr :=
do (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
   s.dsimplify to_unfold t cfg

/-- Auxilliary definition for `expr.pi_arity` -/
meta def pi_arity_aux : ℕ → expr → ℕ
| n (pi _ _ _ b) := pi_arity_aux (n + 1) b
| n e            := n

/-- The arity of a pi-type. Does not perform any reduction of the expression.
  In one application this was ~30 times quicker than `tactic.get_pi_arity`. -/
meta def pi_arity : expr → ℕ :=
pi_arity_aux 0

end expr

namespace environment

/-- Tests whether a name is declared in the current file. Fixes an error in `in_current_file`
  which returns `tt` for the four names `quot, quot.mk, quot.lift, quot.ind` -/
meta def in_current_file' (env : environment) (n : name) : bool :=
env.in_current_file n && (n ∉ [``quot, ``quot.mk, ``quot.lift, ``quot.ind])

/-- Tests whether `n` is an inductive type with one constructor without indices.
  If so, returns the number of paramaters and the name of the constructor.
  Otherwise, returns `none`. -/
meta def is_structure_like (env : environment) (n : name) : option (nat × name) :=
do guardb (env.is_inductive n),
  d ← (env.get n).to_option,
  [intro] ← pure (env.constructors_of n) | none,
  guard (env.inductive_num_indices n = 0),
  some (env.inductive_num_params n, intro)

/-- Tests whether `n` is a structure.
  It will first test whether `n` is structure-like and then test that the first projection is
  defined in the environment and is a projection. -/
meta def is_structure (env : environment) (n : name) : bool :=
option.is_some $ do
  (nparams, intro) ← env.is_structure_like n,
  di ← (env.get intro).to_option,
  expr.pi x _ _ _ ← nparams.iterate
    (λ e : option expr, do expr.pi _ _ _ body ← e | none, some body)
    (some di.type) | none,
  env.is_projection (n ++ x.deinternalize_field)

/-- For all declarations `d` where `f d = some x` this adds `x` to the returned list.  -/
meta def decl_filter_map {α : Type} (e : environment) (f : declaration → option α) : list α :=
  e.fold [] $ λ d l, match f d with
                     | some r := r :: l
                     | none := l
                     end

/-- Maps `f` to all declarations in the environment. -/
meta def decl_map {α : Type} (e : environment) (f : declaration → α) : list α :=
  e.decl_filter_map $ λ d, some (f d)

/-- Lists all declarations in the environment -/
meta def get_decls (e : environment) : list declaration :=
  e.decl_map id

/-- Lists all trusted (non-meta) declarations in the environment -/
meta def get_trusted_decls (e : environment) : list declaration :=
  e.decl_filter_map (λ d, if d.is_trusted then some d else none)

/-- Lists the name of all declarations in the environment -/
meta def get_decl_names (e : environment) : list name :=
  e.decl_map declaration.to_name

/-- Fold a monad over all declarations in the environment. -/
meta def mfold {α : Type} {m : Type → Type} [monad m] (e : environment) (x : α)
  (fn : declaration → α → m α) : m α :=
e.fold (return x) (λ d t, t >>= fn d)

/-- Filters all declarations in the environment. -/
meta def mfilter (e : environment) (test : declaration → tactic bool) : tactic (list declaration) :=
e.mfold [] $ λ d ds, do b ← test d, return $ if b then d::ds else ds

/-- Checks whether `ml` is a prefix of the file where `n` is declared.
  This is used to check whether `n` is declared in mathlib, where `s` is the mathlib directory. -/
meta def is_prefix_of_file (e : environment) (s : string) (n : name) : bool :=
s.is_prefix_of $ (e.decl_olean n).get_or_else ""

end environment

namespace declaration
open tactic

protected meta def update_with_fun (f : name → name) (tgt : name) (decl : declaration) :
  declaration :=
let decl := decl.update_name $ tgt in
let decl := decl.update_type $ decl.type.apply_replacement_fun f in
decl.update_value $ decl.value.apply_replacement_fun f

/-- Checks whether the declaration is declared in the current file.
  This is a simple wrapper around `environment.in_current_file'`
  Use `environment.in_current_file'` instead if performance matters. -/
meta def in_current_file (d : declaration) : tactic bool :=
do e ← get_env, return $ e.in_current_file' d.to_name

/-- Checks whether a declaration is a theorem -/
meta def is_theorem : declaration → bool
| (thm _ _ _ _) := tt
| _             := ff

/-- Checks whether a declaration is a constant -/
meta def is_constant : declaration → bool
| (cnst _ _ _ _) := tt
| _              := ff

/-- Checks whether a declaration is a axiom -/
meta def is_axiom : declaration → bool
| (ax _ _ _) := tt
| _          := ff

/-- Checks whether a declaration is automatically generated in the environment -/
meta def is_auto_generated (e : environment) (d : declaration) : bool :=
e.is_constructor d.to_name ∨
(e.is_projection d.to_name).is_some ∨
(e.is_constructor d.to_name.get_prefix ∧
  d.to_name.last ∈ ["inj", "inj_eq", "sizeof_spec", "inj_arrow"]) ∨
(e.is_inductive d.to_name.get_prefix ∧
  d.to_name.last ∈ ["below", "binduction_on", "brec_on", "cases_on", "dcases_on", "drec_on", "drec",
  "rec", "rec_on", "no_confusion", "no_confusion_type", "sizeof", "ibelow", "has_sizeof_inst"])

end declaration

/-- The type of binders containing a name, the binding info and the binding type -/
@[derive decidable_eq]
meta structure binder :=
  (name : name)
  (info : binder_info)
  (type : expr)

namespace binder
/-- Turn a binder into a string. Uses expr.to_string for the type. -/
protected meta def to_string (b : binder) : string :=
let (l, r) := b.info.brackets in
l ++ b.name.to_string ++ " : " ++ b.type.to_string ++ r

open tactic
meta instance : inhabited binder := ⟨⟨default _, default _, default _⟩⟩
meta instance : has_to_string binder := ⟨ binder.to_string ⟩
meta instance : has_to_format binder := ⟨ λ b, b.to_string ⟩
meta instance : has_to_tactic_format binder :=
⟨ λ b, let (l, r) := b.info.brackets in
  (λ e, l ++ b.name.to_string ++ " : " ++ e ++ r) <$> pp b.type ⟩

end binder
