/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

-- TODO remove
import tactic.clear tactic.rename


universes u v w


namespace list

variables {α : Type u} {β : Type v}

/-- Auxiliary definition for `foldl_with_index`. -/
def foldl_with_index_aux (f : ℕ → α → β → α) : ℕ → α → list β → α
| _ a [] := a
| i a (b :: l) := foldl_with_index_aux (i + 1) (f i a b) l

/-- Fold a list from left to right as with `foldl`, but the combining function
also receives each element's index. -/
def foldl_with_index (f : ℕ → α → β → α) (a : α) (l : list β) : α :=
foldl_with_index_aux f 0 a l

/-- Auxiliary definition for `foldr_with_index`. -/
def foldr_with_index_aux (f : ℕ → α → β → β) : ℕ → β → list α → β
| _ b [] := b
| i b (a :: l) := f i a (foldr_with_index_aux (i + 1) b l)

/-- Fold a list from right to left as with `foldr`, but the combining function
also receives each element's index. -/
def foldr_with_index (f : ℕ → α → β → β) (b : β) (l : list α) : β :=
foldr_with_index_aux f 0 b l

/-- The list of indexes of a list. `index_list l = [0, ..., length l - 1]`. -/
def index_list : list α → list nat := map_with_index (λ i _, i)

end list


@[reducible] def rbmultimap (α : Type*) (β : Type*)
  (ltα : α → α → Prop . rbtree.default_lt)
  (ltβ : β → β → Prop . rbtree.default_lt)
  : Type* :=
rbmap α (rbtree β ltβ) ltα

def mk_rbmultimap (α : Type*) (β : Type*)
  (ltα : α → α → Prop . rbtree.default_lt)
  (ltβ : β → β → Prop . rbtree.default_lt)
  : rbmultimap α β ltα ltβ :=
mk_rbmap α (rbtree β ltβ) ltα


namespace rbmultimap

variables
  {α : Type u} {β : Type v}
  {ltα : α → α → Prop} [decidable_rel ltα]
  {ltβ : β → β → Prop} [decidable_rel ltβ]

def insert (m : rbmultimap α β ltα ltβ) (a : α) (b : β) : rbmultimap α β ltα ltβ :=
let bs := m.find a in
m.insert a
  (match bs with
   | none := @rbtree_of _ [b] ltβ _
   | (some bs) := bs.insert b
   end)

def find (m : rbmultimap α β ltα ltβ) (a : α) : option (rbtree β ltβ) :=
m.find a

def contains (m : rbmultimap α β ltα ltβ) (a : α) (b : β) : bool :=
match m.find a with
| none := false
| (some bs) := bs.contains b
end

def to_list (m : rbmultimap α β ltα ltβ) : list (α × rbtree β ltβ) :=
m.to_list

def to_multilist (m : rbmultimap α β ltα ltβ) : list (α × list β) :=
m.to_list.map (λ ⟨a, bs⟩, ⟨a, bs.to_list⟩)

end rbmultimap


namespace tactic

open expr

/-- Given a type of the form `∀ (x : T) ... (z : U), V`, this function returns
information about each of the binders `x ... z` (binder name, binder info and
type) and the return type `V`.

Given any other expression `e`, it returns an empty list and `e`.
-/
meta def decompose_pi : expr → list (name × binder_info × expr) × expr
| (pi n binfo T rest) :=
  let (args , ret) := decompose_pi rest in
  ((n, binfo, T) :: args, ret)
| e := ([] , e)

/-- Given a type of the form `∀ (x : T) ... (z : U), V`, this function returns
information about each of the binders `x ... z` (binder name, binder info and
type) and the return type `V`.

Given any other expression `e`, it returns an empty list and `e`.

The input expression is normalised lazily. This means that the returned
expressions are not necessarily in normal form.
-/
meta def decompose_pi_normalising
  : expr → tactic (list (name × binder_info × expr) × expr) := λ e, do
e ← whnf e,
match e with
| (pi n binfo T rest) := do
  (args, ret) ← decompose_pi_normalising rest,
  pure ((n , binfo, T) :: args, ret)
| _ := pure ([] , e)
end

/-- Auxiliary function for `decompose_app`. -/
meta def decompose_app_aux : expr → expr × list expr
| (app t u) :=
  let (f , args) := decompose_app_aux t in
  (f , u :: args)
| e := (e , [])

/-- Decomposes a function application. If `e` is of the form `f x ... z`, the
result is `(f, [x, ..., z])`. If `e` is not of this form, the result is
`(e, [])`.
-/
meta def decompose_app (e : expr) : expr × list expr :=
let (f , args) := decompose_app_aux e in
(f , args.reverse)

/-- Auxiliary function for `decompose_app_normalising`. -/
meta def decompose_app_normalising_aux : expr → tactic (expr × list expr) := λ e, do
e ← whnf e,
match e with
| (app t u) := do
  (f , args) ← decompose_app_normalising_aux e,
  pure (f , u :: args)
| _ := pure (e , [])
end

/-- Decomposes a function application. If `e` is of the form `f x ... z`, the
result is `(f, [x, ..., z])`. If `e` is not of this form, the result is
`(e, [])`.

`e` is normalised lazily. This means that the returned expressions are not
necessarily in normal form.
-/
meta def decompose_app_normalising (e : expr) : tactic (expr × list expr) := do
(f , args) ← decompose_app_normalising_aux e,
pure (f , args.reverse)

/-- Matches any expression of the form `C x .. z` where `C` is a constant.
Returns the name of `C`.
-/
meta def match_const_application : expr → option name
| (app e₁ e₂) := match_const_application e₁
| (const n _) := pure n
| _ := none

/-- Matches any expression of the form `C x .. z` where `C` is a constant.
Returns the name of `C`.

The input expression is normalised lazily. This means that the returned
expressions are not necessarily in normal form.
-/
meta def match_const_application_normalising : expr → tactic name := λ e, do
e ← whnf e,
match e with
| (app e₁ e₂) := match_const_application_normalising e₁
| (const n _) := pure n
| _ := fail $ format!
    "Expected {e} to be a constant (possibly applied to some arguments)."
end

/-- Returns true iff `arg_type` is the local constant named `type_name`
(possibly applied to some arguments). If `arg_type` is the type of an argument
of one of `type_name`'s constructors and this function returns true, then the
constructor argument is a recursive occurrence. -/
meta def is_recursive_constructor_argument (type_name : name) (arg_type : expr)
  : bool :=
let base_type_name := match_const_application arg_type in
base_type_name = type_name

/-- `match_variable e` returns `some n` if `e` is the `n`-th de Bruijn variable,
and `none` otherwise. -/
meta def match_variable : expr → option nat
| (var n) := some n
| _ := none

/-- Returns the set of variables occurring in `e`. -/
meta def variable_occurrences (e : expr) : rbtree nat :=
e.fold (mk_rbtree nat)
  (λ e _ occs,
    match match_variable e with
    | some n := occs.insert n
    | none := occs
    end)

/-- Given an application `e = f x ... z`, this function returns a map
associating each de Bruijn index that occurs in `e` with the parts of `e` that it
occurs in. For instance, if `e = #3 (#2 + 1) 0 #3` then the returned map is

    3 -> 0, 3
    2 -> 1
-/
meta def application_variable_occurrences (e : expr) : rbmultimap nat nat :=
let (f, args) := decompose_app e in
let occs := (f :: args).map variable_occurrences in
occs.foldl_with_index
  (λ i occ_map occs, occs.fold (λ var occ_map , occ_map.insert var i) occ_map)
  (mk_rbmap nat (rbtree nat))

@[derive has_reflect]
meta structure constructor_argument_info :=
(aname : name)
(type : expr)

@[derive has_reflect]
meta structure constructor_info :=
(cname : name)
(args : list constructor_argument_info)
(return_type : expr)

@[derive has_reflect]
meta structure inductive_info :=
(iname : name)
(constructors : list constructor_info)
(num_constructors : ℕ)
(type : expr)
(num_params : ℕ)
(num_indices : ℕ)

/-- Gathers information about a constructor from the environment. Fails if `c`
does not refer to a constructor. -/
meta def get_constructor_info (env : environment) (c : name)
  : exceptional constructor_info := do
when (¬ env.is_constructor c) $ exceptional.fail format!
  "Expected {c} to be a constructor.",
decl ← env.get c,
let (args , return_type) := decompose_pi decl.type,
pure
  { cname := decl.to_name,
    args := args.map (λ ⟨name, _, type⟩, ⟨name, type⟩),
    return_type := return_type }

/-- Gathers information about an inductive type from the environment. Fails if
`T` does not refer to an inductive type. -/
meta def get_inductive_info (env : environment) (T : name)
  : exceptional inductive_info := do
when (¬ env.is_inductive T) $ exceptional.fail format!
  "Expected {T} to be an inductive type.",
decl ← env.get T,
let type := decl.type,
let num_params := env.inductive_num_params T,
let num_indices := env.inductive_num_indices T,
let constructor_names := env.constructors_of T,
constructors ← constructor_names.mmap (get_constructor_info env),
pure
  { iname := T,
    constructors := constructors,
    num_constructors := constructors.length,
    type := type,
    num_params := num_params,
    num_indices := num_indices }

@[derive has_reflect]
meta structure eliminee_info :=
(ename : name)
(type : expr)
(index_instantiations : list expr)

meta def local_pp_name_option : expr → option name
| (local_const _ n _ _) := some n
| _ := none

meta def get_eliminee_info (e : expr) : tactic eliminee_info := do
ename ← local_pp_name_option e <|> fail format!
  "Expected {e} to be a local constant.",
type ← infer_type e,
pure
  { ename := ename,
    type := type,
    index_instantiations := [] } -- TODO

@[derive has_reflect]
meta structure constructor_argument_naming_info : Type :=
(einfo : eliminee_info)
(iinfo : inductive_info)
(cinfo : constructor_info)
(ainfo : constructor_argument_info)

@[reducible] meta def constructor_argument_naming_rule : Type :=
constructor_argument_naming_info → option name

meta def constructor_argument_naming_rule_rec : constructor_argument_naming_rule := λ i,
if is_recursive_constructor_argument i.iinfo.iname i.ainfo.type
  then some i.einfo.ename
  else none

meta def default_constructor_argument_name : name := `x

meta def apply_constructor_argument_naming_rules
  (info : constructor_argument_naming_info)
  (rules : list constructor_argument_naming_rule)
  : name :=
let go : option name → constructor_argument_naming_rule → option name :=
  λ n rule,
    match n with
    | some n := some n
    | none := rule info
    end
in
(rules.foldl go none).get_or_else default_constructor_argument_name

meta def constructor_argument_name (info : constructor_argument_naming_info)
  : name :=
apply_constructor_argument_naming_rules info
  [ constructor_argument_naming_rule_rec ]

meta def ih_name (arg_name : name) : name :=
mk_simple_name ("ih_" ++ arg_name.to_string)

meta def intro_fresh (n : name) : tactic unit := do
n ← get_unused_name n,
intro n,
pure ()

meta def constructor_argument_intros (einfo : eliminee_info)
  (iinfo : inductive_info) (cinfo : constructor_info)
  : tactic unit :=
(cinfo.args.drop iinfo.num_params).mmap' $ λ ainfo,
  intro_fresh (constructor_argument_name ⟨einfo, iinfo, cinfo, ainfo⟩)

meta def ih_intros (einfo : eliminee_info) (iinfo : inductive_info)
  (cinfo : constructor_info)
  : tactic unit :=
let rec_args :=
  cinfo.args.filter
    (λ ainfo, is_recursive_constructor_argument iinfo.iname ainfo.type) in
let ih_names :=
  rec_args.map
    (λ ainfo, ih_name $ constructor_argument_name ⟨einfo, iinfo, cinfo, ainfo⟩) in
match ih_names with
| [] := pure ()
| [_] := intro_fresh "ih"
| ns := ns.mmap' intro_fresh
end

meta def constructor_intros (einfo : eliminee_info) (iinfo : inductive_info)
  (cinfo : constructor_info) : tactic unit := do
constructor_argument_intros einfo iinfo cinfo,
ih_intros einfo iinfo cinfo

meta def interactive.stuff : tactic unit := do
env ← get_env,
cinfo ← get_constructor_info env `nat.less_than_or_equal.step,
trace cinfo.return_type,
trace (application_variable_occurrences cinfo.return_type).to_multilist,
pure ()

set_option pp.all true

example : unit :=
begin
  stuff,
  exact ()
end

-- TODO debug
meta def trace_constructor_arg (type_name : name) (arg : constructor_argument_info)
  : tactic unit := do
let ⟨n , ty⟩ := arg,
trace format!"Name: {n}",
trace format!"Type: {ty}",
let is_rec := is_recursive_constructor_argument type_name ty,
trace format!"Recursive?: {is_rec}"

-- TODO debug
meta def trace_constructor (type_name : name) (constructor_name : name)
  : tactic unit := do
env ← get_env,
info ← get_constructor_info env constructor_name,
trace "Arguments:",
info.args.mmap (trace_constructor_arg type_name),
trace "Return type:",
trace info.return_type

meta def induction'' (eliminee_name : name) : tactic unit := do
eliminee ← get_local eliminee_name,
einfo ← get_eliminee_info eliminee,
let eliminee_type := einfo.type,
env ← get_env,

-- Find the recursor and other info about the inductive type
(rec_const, iinfo) ← (do
  type_name ← match_const_application_normalising eliminee_type,
  guard (env.is_inductive type_name),
  let rec_name := type_name ++ "rec_on",
  rec_const ← mk_const rec_name,
  iinfo ← get_inductive_info env type_name,
  pure (rec_const, iinfo)
) <|> fail format!
  "The type of {eliminee_name} should be an inductive type, but it is {eliminee_type}.",
-- TODO disallow generalised inductives; we don't want to support them

-- Apply the recursor
let rec := ``(%%rec_const %%eliminee),
rec ← i_to_expr_for_apply rec,
apply rec,

-- Clear the eliminated hypothesis
focus $ list.repeat (clear eliminee) iinfo.num_constructors,

-- Introduce all constructor arguments
focus $ iinfo.constructors.map $ constructor_intros einfo iinfo,
pure ()

end tactic


namespace tactic.interactive

open interactive lean.parser

meta def induction' (hyp : parse ident) : tactic unit :=
  tactic.induction'' hyp

end tactic.interactive


--------------------------------------------------------------------------------
-- TODO remove everything below this
--------------------------------------------------------------------------------

set_option trace.app_builder true
-- set_option pp.all true

inductive le : ℕ → ℕ → Type
| zero {n} : le 0 n
| succ {n m} : le n m → le (n + 1) (m + 1)

inductive lt : ℕ → ℕ → Type
| zero {n} : lt 0 (n + 1)
| succ {n m} : lt n m → lt (n + 1) (m + 1)

inductive unit_param (a : unit) : Type
| intro : unit_param

inductive unit_index : unit → Type
| intro : unit_index ()

inductive Fin : ℕ → Type
| zero {n} : Fin (n + 1)
| succ {n} : Fin n → Fin (n + 1)

inductive List (α : Sort*) : Sort*
| nil {} : List
| cons {} (x : α) (xs : List) : List

namespace List

def append {α} : List α → List α → List α
| nil ys := ys
| (cons x xs) ys := cons x (append xs ys)

end List

inductive Vec (α : Sort*) : ℕ → Sort*
| nil : Vec 0
| cons {n} : α → Vec n → Vec (n + 1)

example (k) : 0 + k = k :=
begin
  induction' k,
  { refl
  },
  { simp [ih]
  }
end

example {k} (fk : Fin k) : Fin (k + 1) :=
begin
  induction' fk,
  { clear' k,
    rename x k,
    exact Fin.zero
  },
  { clear' k fk,
    rename x k,
    exact Fin.succ ih
  }
end

example {α} (l : List α) : l.append List.nil = l :=
begin
  induction' l,
  { refl
  },
  { simp [ih, List.append]
  }
end

example {k l} (h : lt k l) : le k l :=
begin
  induction' h,
  { clear' k l,
    rename x l,
    constructor
  },
  { clear' k l,
    rename' [x k, x_1 l],
    constructor,
    assumption
  }
end

-- The type of the induction premise can be a complex expression so long as it
-- normalises to an inductive (possibly applied to params/indexes).
example (n) : 0 + n = n :=
begin
  let T := ℕ,
  change T at n,
  induction' n; simp
end

-- Fail if the type of the induction premise is not an inductive type
example {α} (x : α) (f : α → α) : unit :=
begin
  success_if_fail { induction' x },
  success_if_fail { induction' f },
  exact ()
end


namespace tactic

meta def test : tactic unit := do
  get_unused_name `y none >>= trace,
  get_unused_name `x none >>= trace,
  get_unused_name `x (some 0) >>= trace,
  get_unused_name `x (some 1) >>= trace,
  get_unused_name `x (some 2) >>= trace,
  get_unused_name `x (some 3) >>= trace,
  get_unused_name `y (some 0) >>= trace,
  get_unused_name >>= trace,
  pure ()

end tactic

example {x x_1 : Type} : unit :=
begin
  tactic.test,
  exact ()
end

example : unit :=
begin
  tactic.trace_constructor `le `le.succ,
  exact ()
end
