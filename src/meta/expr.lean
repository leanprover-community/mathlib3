/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis

Additional non-tactic operations on expr and related types
-/

namespace name

meta def deinternalize_field : name → name
| (name.mk_string s name.anonymous) :=
  let i := s.mk_iterator in
  if i.curr = '_' then i.next.next_to_string else s
| n := n

meta def get_nth_prefix : name → ℕ → name
| nm 0 := nm
| nm (n + 1) := get_nth_prefix nm.get_prefix n

private meta def pop_nth_prefix_aux : name → ℕ → name × ℕ
| anonymous n := (anonymous, 1)
| nm n := let (pfx, height) := pop_nth_prefix_aux nm.get_prefix n in
          if height ≤ n then (anonymous, height + 1)
          else (nm.update_prefix pfx, height + 1)

-- Pops the top `n` prefixes from the given name.
meta def pop_nth_prefix (nm : name) (n : ℕ) : name :=
prod.fst $ pop_nth_prefix_aux nm n

meta def pop_prefix (n : name) : name :=
pop_nth_prefix n 1

private def from_components_aux : name → list string → name
| n [] := n
| n (s :: rest) := from_components_aux (name.mk_string s n) rest

def from_components : list string → name :=
from_components_aux name.anonymous

-- `name`s can contain numeral pieces, which are not legal names
-- when typed/passed directly to the parser. We turn an arbitrary
-- name into a legal identifier name.
meta def sanitize_name : name → name
| name.anonymous := name.anonymous
| (name.mk_string s p) := name.mk_string s $ sanitize_name p
| (name.mk_numeral s p) := name.mk_string sformat!"n{s}" $ sanitize_name p

def append_suffix : name → string → name
| (mk_string s n) s' := mk_string (s ++ s') n
| n _ := n

meta def head : name → string
| (mk_string s anonymous) := s
| (mk_string s p)         := head p
| (mk_numeral n p)        := head p
| anonymous               := "[anonymous]"

meta def is_private (n : name) : bool :=
n.head = "_private"

/-- Get the last component of a name, assuming it is a string. -/
meta def last : name → string
| (mk_string s _)  := s
| (mk_numeral n _) := repr n
| anonymous        := "[anonymous]"

meta def length : name → ℕ
| (mk_string s anonymous) := s.length
| (mk_string s p)         := s.length + 1 + p.length
| (mk_numeral n p)        := p.length
| anonymous               := "[anonymous]".length

end name

namespace level

meta def nonzero : level → bool
| (succ _) := tt
| (max l₁ l₂) := l₁.nonzero || l₂.nonzero
| (imax _ l₂) := l₂.nonzero
| _ := ff

end level

namespace expr
open tactic

protected meta def to_pos_nat : expr → option ℕ
| `(has_one.one _) := some 1
| `(bit0 %%e) := bit0 <$> e.to_pos_nat
| `(bit1 %%e) := bit1 <$> e.to_pos_nat
| _           := none

protected meta def to_nat : expr → option ℕ
| `(has_zero.zero _) := some 0
| e                  := e.to_pos_nat

protected meta def to_int : expr → option ℤ
| `(has_neg.neg %%e) := do n ← e.to_nat, some (-n)
| e                  := coe <$> e.to_nat

meta def is_meta_var : expr → bool
| (mvar _ _ _) := tt
| e            := ff

meta def is_sort : expr → bool
| (sort _) := tt
| e         := ff

meta def list_local_consts (e : expr) : list expr :=
e.fold [] (λ e' _ es, if e'.is_local_constant then insert e' es else es)

meta def list_constant (e : expr) : name_set :=
e.fold mk_name_set (λ e' _ es, if e'.is_constant then es.insert e'.const_name else es)

meta def list_meta_vars (e : expr) : list expr :=
e.fold [] (λ e' _ es, if e'.is_meta_var then insert e' es else es)

meta def list_names_with_prefix (pre : name) (e : expr) : name_set :=
e.fold mk_name_set $ λ e' _ l,
  match e' with
  | expr.const n _ := if n.get_prefix = pre then l.insert n else l
  | _ := l
  end

meta def is_mvar : expr → bool
| (mvar _ _ _) := tt
| _            := ff

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

meta def simp (t : expr)
  (cfg : simp_config := {}) (discharger : tactic unit := failed)
  (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) :
  tactic (expr × expr) :=
do (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
   simplify s to_unfold t cfg `eq discharger

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

meta def in_current_file' (env : environment) (n : name) : bool :=
env.in_current_file n && (n ∉ [``quot, ``quot.mk, ``quot.lift, ``quot.ind])

meta def is_structure_like (env : environment) (n : name) : option (nat × name) :=
do guardb (env.is_inductive n),
  d ← (env.get n).to_option,
  [intro] ← pure (env.constructors_of n) | none,
  guard (env.inductive_num_indices n = 0),
  some (env.inductive_num_params n, intro)

meta def is_structure (env : environment) (n : name) : bool :=
option.is_some $ do
  (nparams, intro) ← env.is_structure_like n,
  di ← (env.get intro).to_option,
  expr.pi x _ _ _ ← nparams.iterate
    (λ e : option expr, do expr.pi _ _ _ body ← e | none, some body)
    (some di.type) | none,
  env.is_projection (n ++ x.deinternalize_field)

meta def decl_filter_map {α : Type} (e : environment) (f : declaration → option α) : list α :=
  e.fold [] $ λ d l, match f d with
                     | some r := r :: l
                     | none := l
                     end

meta def decl_map {α : Type} (e : environment) (f : declaration → α) : list α :=
  e.decl_filter_map $ λ d, some (f d)

meta def get_decls (e : environment) : list declaration :=
  e.decl_map id

meta def get_trusted_decls (e : environment) : list declaration :=
  e.decl_filter_map (λ d, if d.is_trusted then some d else none)

meta def get_decl_names (e : environment) : list name :=
  e.decl_map declaration.to_name

meta def mfold {α : Type} {m : Type → Type} [monad m] (e : environment) (x : α)
  (fn : declaration → α → m α) : m α :=
e.fold (return x) (λ d t, t >>= fn d)

end environment

namespace declaration

open tactic
/-- Checks whether the declaration is declared in the current file.
  This is a simple wrapper around `environment.in_current_file'` -/
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

end declaration
