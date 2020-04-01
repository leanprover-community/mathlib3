/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import category.basic data.sum data.list.defs tactic.basic


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

/-- The list of indices of a list. `index_list l = [0, ..., length l - 1]`. -/
def index_list : list α → list ℕ := map_with_index (λ i _, i)

def to_rbmap : list α → rbmap ℕ α :=
foldl_with_index (λ i mapp a, mapp.insert i a) (mk_rbmap ℕ α)

def all_some : list (option α) → option (list α)
| [] := some []
| (some x :: xs) := (λ z, x :: z) <$> all_some xs
| (none :: xs) := none

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
  {ltα : α → α → Prop} {ltβ : β → β → Prop}

def insert [decidable_rel ltα] [decidable_rel ltβ] (m : rbmultimap α β ltα ltβ)
  (a : α) (b : β)
  : rbmultimap α β ltα ltβ :=
let bs := m.find a in
m.insert a
  (match bs with
   | none := @rbtree_of _ [b] ltβ _
   | (some bs) := bs.insert b
   end)

def find [decidable_rel ltα] (m : rbmultimap α β ltα ltβ) (a : α)
  : option (rbtree β ltβ) :=
m.find a

def contains [decidable_rel ltα] [decidable_rel ltβ] (m : rbmultimap α β ltα ltβ)
  (a : α) (b : β)
  : bool :=
match m.find a with
| none := false
| (some bs) := bs.contains b
end

def to_list (m : rbmultimap α β ltα ltβ) : list (α × rbtree β ltβ) :=
m.to_list

def to_multilist (m : rbmultimap α β ltα ltβ) : list (α × list β) :=
m.to_list.map (λ ⟨a, bs⟩, ⟨a, bs.to_list⟩)

end rbmultimap


namespace rbtree

def merge {α} {lt : α → α → Prop} [decidable_rel lt] (xs ys : rbtree α lt)
  : rbtree α lt :=
ys.fold (λ a xs, xs.insert a) xs

end rbtree


namespace expr

meta def local_pp_name_option : expr → option name
| (local_const _ n _ _) := some n
| _ := none

meta def local_unique_name_option : expr → option name
| (local_const n _ _ _) := some n
| _ := none

meta def local_names_option : expr → option (name × name)
| (local_const n₁ n₂ _ _) := some (n₁, n₂)
| _ := none

meta def is_local (e : expr) : bool := e.local_unique_name_option.is_some

end expr


namespace sum

def get_left {α β} : α ⊕ β → option α
| (inl a) := some a
| _ := none

def get_right {α β} : α ⊕ β → option β
| (inr b) := some b
| _ := none

def is_left {α β} (s : α ⊕ β) : bool :=
s.get_left.is_some

def is_right {α β} (s : α ⊕ β) : bool :=
s.get_right.is_some

end sum


namespace parser

def char : parser char :=
sat (λ _, true)

def digit : parser nat := do
c ← char,
let c' := c.to_nat - '0'.to_nat,
if 0 ≤ c' ∧ c' ≤ 9
  then pure c'
  else parser.fail $ "expected a digit, got: " ++ c.to_string

def nat : parser nat := do
digits ← many1 digit,
pure $ prod.fst $
  digits.foldr
    (λ digit ⟨sum, magnitude⟩, ⟨sum + digit * magnitude, magnitude * 10⟩)
    ⟨0, 1⟩

end parser


namespace name

open parser

meta def likely_generated_name_p : parser unit := do
str "a",
optional (ch '_' *> parser.nat),
pure ()

meta def is_likely_generated_name (n : name) : bool :=
match n with
| anonymous := ff
| mk_numeral _ _ := ff
| mk_string s anonymous := (likely_generated_name_p.run_string s).is_right
| mk_string _ _ := ff
end

end name


namespace tactic

open expr

meta def free_vars (binder_depth : ℕ) (e : expr) : rbtree ℕ :=
e.fold (mk_rbtree ℕ) $ λ e depth vars,
  match e with
  | var n := if n ≥ binder_depth + depth then vars.insert n else vars
  | _ := vars
  end

meta def decompose_pi_aux
  : ℕ → expr → list (name × binder_info × expr × bool) × ℕ × expr × rbtree ℕ
| binder_depth (pi name binfo T rest) :=
  let (args, n_args, ret, vars) := decompose_pi_aux (binder_depth + 1) rest in
  let dep := vars.contains binder_depth in
  let vars' := vars.merge (free_vars binder_depth T) in
  ((name, binfo, T, dep) :: args, n_args + 1, ret, vars')
| binder_depth e := ([], 0, e, free_vars binder_depth e)

/-- Given a type of the form `∀ (x : T) ... (z : U), V`, this function returns a
tuple `(args, n, V)` where

- `args` is a list containing information about the arguments `x ... z`:
  argument name, binder info, argument type and whether the argument is
  dependent (i.e. whether the rest of the input `expr` depends on it).
- `n` is the length of `args`.
- `V` is the return type.

Given any other expression `e`, this function returns an empty list and `e`.
-/
meta def decompose_pi (e : expr)
  : list (name × binder_info × expr × bool) × ℕ × expr :=
let (args, n_args, ret, _) := decompose_pi_aux 0 e in
(args, n_args, ret)

/-- Given a type of the form `∀ (x : T) ... (z : U), V`, this function returns
information about each of the binders `x ... z` (binder name, binder info and
type) and the return type `V`.

Given any other expression `e`, it returns an empty list and `e`.

The input expression is normalised lazily. This means that the returned
expressions are not necessarily in normal form.
-/
meta def decompose_pi_normalizing
  : expr → tactic (list (name × binder_info × expr) × expr) := λ e, do
e ← whnf e,
match e with
| (pi n binfo T rest) := do
  (args, ret) ← decompose_pi_normalizing rest,
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

/-- Auxiliary function for `decompose_app_normalizing`. -/
meta def decompose_app_normalizing_aux : expr → tactic (expr × list expr) := λ e, do
e ← whnf e,
match e with
| (app t u) := do
  (f , args) ← decompose_app_normalizing_aux t,
  pure (f , u :: args)
| _ := pure (e , [])
end

/-- Decomposes a function application. If `e` is of the form `f x ... z`, the
result is `(f, [x, ..., z])`. If `e` is not of this form, the result is
`(e, [])`.

`e` is normalised lazily. This means that the returned expressions are not
necessarily in normal form.
-/
meta def decompose_app_normalizing (e : expr) : tactic (expr × list expr) := do
(f , args) ← decompose_app_normalizing_aux e,
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
meta def match_const_application_normalizing : expr → tactic name := λ e, do
e ← whnf e,
match e with
| (app e₁ e₂) := match_const_application_normalizing e₁
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
meta def match_variable : expr → option ℕ
| (var n) := some n
| _ := none

/-- Returns the set of variables occurring in `e`. -/
meta def variable_occurrences (e : expr) : rbtree ℕ :=
e.fold (mk_rbtree ℕ)
  (λ e _ occs,
    match match_variable e with
    | some n := occs.insert n
    | none := occs
    end)

/-- Given an application `e = f x ... z`, this function returns a map
associating each de Bruijn index that occurs in `e` with the application
argument(s) that it occurs in. For instance, if `e = f (#2 + 1) #3 #3` then the
returned map is

    3 -> 1, 2
    2 -> 0

As shown in the example, arguments are counted from zero.
-/
meta def application_variable_occurrences (e : expr) : rbmultimap ℕ ℕ :=
let (_, args) := decompose_app e in
let occs := args.map variable_occurrences in
occs.foldl_with_index
  (λ i occ_map occs, occs.fold (λ var occ_map, occ_map.insert var i) occ_map)
  (mk_rbmultimap ℕ ℕ)

@[derive has_reflect]
meta structure constructor_argument_info :=
(aname : name)
(type : expr)
(dependent : bool)
(index_occurrences : list ℕ)
(arg_occs : list (ℕ × list ℕ)) -- TODO debug

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

meta def get_constructor_argument_info (num_params : ℕ)
  (num_constructor_args : ℕ) (arg_index : ℕ) (arg_name : name) (arg_type : expr)
  (arg_dependent : bool) (arg_occurrences : rbmultimap ℕ ℕ)
  : constructor_argument_info :=
let arg_var := num_constructor_args - 1 - arg_index in
let arg_occs :=
  ((arg_occurrences.find arg_var).map rbtree.to_list).get_or_else [] in
let index_occs := arg_occs.filter (λ i, i >= num_params) in
-- TODO dbg
let dbg : list (ℕ × list ℕ):= arg_occurrences.to_list.map (λ ⟨i, xs⟩, ⟨i, xs.to_list⟩) in
⟨ arg_name, arg_type, arg_dependent, index_occs, dbg ⟩

/-- Gathers information about a constructor from the environment. Fails if `c`
does not refer to a constructor. -/
meta def get_constructor_info (env : environment) (num_params : ℕ) (c : name)
  : exceptional constructor_info := do
when (¬ env.is_constructor c) $ exceptional.fail format!
  "Expected {c} to be a constructor.",
decl ← env.get c,
let (args, n_args, return_type) := decompose_pi decl.type,
let arg_occurrences := application_variable_occurrences return_type,
pure
  { cname := decl.to_name,
    args := args.map_with_index $ λ i ⟨name, _, type, dep⟩,
      get_constructor_argument_info num_params n_args i name type dep
        arg_occurrences,
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
constructors ← constructor_names.mmap
  (get_constructor_info env num_params),
pure
  { iname := T,
    constructors := constructors,
    num_constructors := constructors.length,
    type := type,
    num_params := num_params,
    num_indices := num_indices }

meta structure eliminee_info :=
(ename : name)
(type : expr)
(args : rbmap ℕ expr)

meta def get_eliminee_info (e : expr) : tactic eliminee_info := do
ename ← local_pp_name_option e <|> fail format!
  "Expected {e} to be a local constant.",
type ← infer_type e,
⟨f, args⟩ ← decompose_app_normalizing type,
pure
  { ename := ename,
    type := type,
    args := args.to_rbmap }

meta structure constructor_argument_naming_info :=
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

/--
After elaboration, Lean does not have non-dependent function types with
unnamed arguments. This means that for the declaration

```lean
inductive test : Type :=
| intro : unit → test
```

the type of `test.intro` becomes

```lean
test.intro : ∀ (a : unit), test
```lean

after elaboration, where `a` is an auto-generated name.

This means that we can't know for sure whether a constructor argument was named
by the user. Hence the following hack: If an argument is non-dependent *and* its
name is `a` or `a_n` for some `n ∈ ℕ`, then we assume that this name was
auto-generated rather than chosen by the user.
-/
library_note "unnamed constructor arguments"

-- TODO as written, this rule always fires. See previous note.
meta def constructor_argument_naming_rule_named : constructor_argument_naming_rule := λ i,
let arg_name := i.ainfo.aname in
if arg_name = name.anonymous
  then none
  else some arg_name

meta def constructor_argument_naming_rule_index : constructor_argument_naming_rule := λ i,
let index_occs := i.ainfo.index_occurrences in
let eliminee_args := i.einfo.args in
let local_index_instantiations :=
  (index_occs.map (eliminee_args.find >=> local_names_option)).all_some in
-- TODO this needs to be updated when we allow complex indices
match local_index_instantiations with
| none := none
| some [] := none
| some ((uname, ppname) :: is) :=
  if is.all (λ ⟨uname', _⟩, uname' = uname)
    then some ppname
    else none
end

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
  [ constructor_argument_naming_rule_rec
  , constructor_argument_naming_rule_index
  , constructor_argument_naming_rule_named ]

meta def ih_name (arg_name : name) : name :=
mk_simple_name ("ih_" ++ arg_name.to_string)

meta def intro_fresh (n : name) : tactic unit := do
n ← get_unused_name n,
intro n,
pure ()

meta def constructor_argument_intros (einfo : eliminee_info)
  (iinfo : inductive_info) (cinfo : constructor_info)
  : tactic unit :=
(cinfo.args.drop iinfo.num_params).mmap' $ λ ainfo, do
  let info : constructor_argument_naming_info := ⟨einfo, iinfo, cinfo, ainfo⟩,
  -- TODO debug
  trace format!"arg: {ainfo.aname}, dep: {ainfo.dependent}, index occs: {ainfo.index_occurrences}",
  intro_fresh (constructor_argument_name info)

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
-- TODO debug
trace format!"constructor: {cinfo.cname}",
constructor_argument_intros einfo iinfo cinfo,
ih_intros einfo iinfo cinfo

meta def eliminee_args_valid (args : list expr) : bool :=
args.all is_local

meta def induction'' (eliminee_name : name) : tactic unit := focus1 $ do
eliminee ← get_local eliminee_name,
einfo ← get_eliminee_info eliminee,
let eliminee_type := einfo.type,
let eliminee_args := einfo.args.to_list.map prod.snd,
env ← get_env,

-- Find the recursor and other info about the inductive type
(rec_const, iinfo) ← (do
  type_name ← match_const_application_normalizing eliminee_type,
  guard (env.is_inductive type_name),
  let rec_name := type_name ++ "rec_on",
  rec_const ← mk_const rec_name,
  iinfo ← get_inductive_info env type_name,
  pure (rec_const, iinfo)
) <|> fail format!
  "The type of {eliminee_name} should be an inductive type, but it is {eliminee_type}.",
-- TODO disallow generalised inductives; we don't want to support them

-- Disallow complex indices (for now)
guard (eliminee_args_valid eliminee_args) <|> fail format!
  "induction' can only eliminate hypotheses of the form `T x₁ ... xₙ`\n
  where `T` is an inductive family and the `xᵢ` are local hypotheses.",

-- TODO generalisation

-- Apply the recursor
let rec := ``(%%rec_const %%eliminee),
rec ← i_to_expr_for_apply rec,
apply rec,

-- Clear the eliminated hypothesis and the index args (unless used elsewhere)
focus $ flip list.repeat iinfo.num_constructors (do
  clear eliminee,
  (eliminee_args.drop iinfo.num_params).mmap' (try ∘ clear)),
  -- TODO is this the right thing to do? I don't think this necessarily
  -- preserves provability: The args we clear could contain interesting
  -- information, even if nothing else depends on them. Is there a way to avoid
  -- this, i.e. clean up even more conservatively?

-- Introduce all constructor arguments
focus $ iinfo.constructors.map $ constructor_intros einfo iinfo,
pure ()

end tactic


namespace tactic.interactive

open interactive lean.parser

meta def induction' (hyp : parse ident) : tactic unit :=
  tactic.induction'' hyp

end tactic.interactive
