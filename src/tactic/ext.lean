/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.rcases
import data.sum
import logic.function.basic

universes u₁ u₂

open interactive interactive.types
open lean.parser nat tactic

/--
`derive_struct_ext_lemma n` generates two extensionality lemmas based on
the equality of all non-propositional projections.

On the following:

```lean
@[ext]
structure foo (α : Type*) :=
(x y : ℕ)
(z : {z // z < x})
(k : α)
(h : x < y)
```

`derive_struct_lemma` generates:

```lean
lemma foo.ext : ∀ {α : Type u_1} (x y : foo α),
  x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y
lemma foo.ext_iff : ∀ {α : Type u_1} (x y : foo α),
  x = y ↔ x.x = y.x ∧ x.y = y.y ∧ x.z == y.z ∧ x.k = y.k
```

-/
meta def derive_struct_ext_lemma (n : name) : tactic name :=
do e ← get_env,
   fs ← e.structure_fields n,
   d ← get_decl n,
   n ← resolve_constant n,
   let r := @expr.const tt n $ d.univ_params.map level.param,
   (args,_) ← infer_type r >>= mk_local_pis,
   let args := args.map expr.to_implicit_local_const,
   let t := r.mk_app args,
   x ← mk_local_def `x t,
   y ← mk_local_def `y t,
   let args_x := args ++ [x],
   let args_y := args ++ [y],
   bs ← fs.mmap $ λ f,
     do { d ← get_decl (n ++ f),
          let a := @expr.const tt (n ++ f) $ d.univ_params.map level.param,
          t ← infer_type a,
          s ← infer_type t,

          if s ≠ `(Prop)
            then do
              let x := a.mk_app args_x,
              let y := a.mk_app args_y,
              t ← infer_type x,
              t' ← infer_type y,
              some <$> if t = t'
                then mk_app `eq [x,y] >>= mk_local_def `h
                else mk_mapp `heq [none,x,none,y] >>= mk_local_def `h
            else pure none },
   let bs := bs.filter_map id,
   eq_t ← mk_app `eq [x,y],
   t ← pis (args ++ [x,y] ++ bs) eq_t,
   pr ← run_async $
     do { (_,pr) ← solve_aux t (do
          { args ← intron args.length,
            x ← intro1, y ← intro1,
            cases x, cases y,
            bs.mmap' (λ _,
              do e ← intro1,
                 cases e),
            reflexivity }),
          instantiate_mvars pr },
   let decl_n := n <.> "ext",
   add_decl (declaration.thm decl_n d.univ_params t pr),
   bs ← bs.mmap infer_type,
   let rhs := expr.mk_and_lst bs,
   iff_t ← mk_app `iff [eq_t,rhs],
   t ← pis (args ++ [x,y]) iff_t,
   pr ← run_async $
     do { (_,pr) ← solve_aux t $ do
          { args ← intron args.length,
            x ← intro1, y ← intro1,
            cases x, cases y,
            split,
            solve1 $ do
            { h ← intro1, hs ← injection h, subst_vars,
              repeat (refine ``( and.intro _ _ ) >> reflexivity ),
              done <|> reflexivity },
            solve1 $ do
            { repeat (do refine ``(and_imp.mpr _),
                         h ← intro1, cases h, skip ),
              h ← intro1, cases h,
              reflexivity }  },
          instantiate_mvars pr },
   add_decl (declaration.thm (n <.> "ext_iff") d.univ_params t pr),
   pure decl_n

meta def get_ext_subject : expr → tactic name
| (expr.pi n bi d b) :=
  do v  ← mk_local' n bi d,
     b' ← whnf $ b.instantiate_var v,
     get_ext_subject b'
| (expr.app _ e) :=
  do t ← infer_type e >>= instantiate_mvars >>= head_beta,
     if t.get_app_fn.is_constant then
       pure $ t.get_app_fn.const_name
     else if t.is_pi then
       pure $ name.mk_numeral 0 name.anonymous
     else if t.is_sort then
       pure $ name.mk_numeral 1 name.anonymous
     else do
       t ← pp t,
       fail format!"only constants and Pi types are supported: {t}"
| e := fail format!"Only expressions of the form `_ → _ → ... → R ... e are supported: {e}"

open native

@[reducible] def ext_param_type := option name ⊕ option name

meta def opt_minus : lean.parser (option name → ext_param_type) :=
sum.inl <$ tk "-" <|> pure sum.inr

meta def ext_param :=
opt_minus <*> ( name.mk_numeral 0 name.anonymous <$ brackets "(" ")" (tk "→" <|> tk "->") <|>
                none <$  tk "*" <|>
                some <$> ident )

meta def saturate_fun : name → tactic expr
| (name.mk_numeral 0 name.anonymous) :=
do v₀ ← mk_mvar,
   v₁ ← mk_mvar,
   return $ v₀.imp v₁
| (name.mk_numeral 1 name.anonymous) :=
do u ← mk_meta_univ,
   pure $ expr.sort u
| n :=
do e ← resolve_constant n >>= mk_const,
   a ← get_arity e,
   e.mk_app <$> (list.iota a).mmap (λ _, mk_mvar)

meta def equiv_type_constr (n n' : name) : tactic unit :=
do e  ← saturate_fun n,
   e' ← saturate_fun n',
   unify e e' <|> fail format!"{n} and {n'} are not definitionally equal types"

section performance_hack
/--
For performance reasons, it is inadvisable to use `user_attribute.get_param`.
The parameter is stored as a reflected expression.  When calling `get_param`,
the stored parameter is evaluated using `eval_expr`, which first compiles the
expression into VM bytecode. The unevaluated expression is available using
`user_attribute.get_param_untyped`.

In particular, `user_attribute.get_param` MUST NEVER BE USED in the
implementation of an attribute cache. This is because calling `eval_expr`
disables the attribute cache.

There are several possible workarounds:
 1. Set a different attribute depending on the parameter.
 2. Use your own evaluation function instead of `eval_expr`, such as e.g. `expr.to_nat`.
 3. Write your own `has_reflect Param` instance (using a more efficient serialization format).
   The `user_attribute` code unfortunately checks whether the expression has the correct type,
   but you can use `` `(id %%e : Param) `` to pretend that your expression `e` has type `Param`.
-/
library_note "user attribute parameters"

/-!
For performance reasons, the parameters of the `@[ext]` attribute are stored
in two auxiliary attributes:
```lean
attribute [ext [thunk]] funext

-- is turned into
attribute [_ext_core (@id name @funext)] thunk
attribute [_ext_lemma_core] funext
```

see Note [user attribute parameters]
-/

local attribute [semireducible] reflected

local attribute [instance, priority 9000]
private meta def hacky_name_reflect : has_reflect name :=
λ n, `(id %%(expr.const n []) : name)

@[user_attribute]
private meta def ext_attr_core : user_attribute (name_map name) name :=
{ name := `_ext_core,
  descr := "(internal attribute used by ext)",
  cache_cfg := {
    dependencies := [],
    mk_cache := λ ns, do
      attrs ← ns.mmap (λ n, do
        ext_l ← ext_attr_core.get_param_untyped n,
        pure (n, ext_l.app_arg.const_name)),
      pure $ rb_map.of_list attrs },
  parser := failure }

end performance_hack

/-- Private attribute used to tag extensionality lemmas. -/
@[user_attribute]
private meta def ext_lemma_attr_core : user_attribute :=
{ name := `_ext_lemma_core,
  descr := "(internal attribute used by ext)",
  parser := failure }

/--
Returns the extensionality lemmas in the environment, as a map from structure
name to lemma name.
-/
meta def get_ext_lemmas : tactic (name_map name) :=
ext_attr_core.get_cache

/--
Returns the extensionality lemmas in the environment, as a list of lemma names.
-/
meta def get_ext_lemma_names : tactic (list name) :=
attribute.get_instances ext_lemma_attr_core.name

/--
Tag lemmas of the form:

```lean
@[ext]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

The attribute indexes extensionality lemma using the type of the
objects (i.e. `my_collection`) which it gets from the statement of
the lemma.  In some cases, the same lemma can be used to state the
extensionality of multiple types that are definitionally equivalent.

```lean
attribute [ext [(→),thunk,stream]] funext
```

Those parameters are cumulative. The following are equivalent:

```lean
attribute [ext [(→),thunk]] funext
attribute [ext [stream]] funext
```
and
```lean
attribute [ext [(→),thunk,stream]] funext
```

One removes type names from the list for one lemma with:
```lean
attribute [ext [-stream,-thunk]] funext
```

Also, the following:

```lean
@[ext]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

is equivalent to

```lean
@[ext *]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

This allows us specify type synonyms along with the type
that is referred to in the lemma statement.

```lean
@[ext [*,my_type_synonym]]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

The `ext` attribute can be applied to a structure to generate its extensionality lemmas:

```lean
@[ext]
structure foo (α : Type*) :=
(x y : ℕ)
(z : {z // z < x})
(k : α)
(h : x < y)
```

will generate:

```lean
@[ext] lemma foo.ext : ∀ {α : Type u_1} (x y : foo α),
x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y
lemma foo.ext_iff : ∀ {α : Type u_1} (x y : foo α),
x = y ↔ x.x = y.x ∧ x.y = y.y ∧ x.z == y.z ∧ x.k = y.k
```

-/
@[user_attribute]
meta def extensional_attribute : user_attribute unit (list ext_param_type) :=
{ name := `ext,
  descr := "lemmas usable by `ext` tactic",
  parser := pure <$> ext_param <|> list_of ext_param <|> pure [],
  after_set := some $ λ n prio b,
    do ls ← extensional_attribute.get_param n,
       e ← get_env,
       n ← if (e.structure_fields n).is_some
         then derive_struct_ext_lemma n
         else pure n,
       s ← mk_const n >>= infer_type >>= get_ext_subject,
       let (rs,ls'') := if ls.empty
                           then ([],[s])
                           else ls.partition_map (sum.map (flip option.get_or_else s)
                                                    (flip option.get_or_else s)),
       ls''.mmap' (equiv_type_constr s),
       ls' ← get_ext_lemmas,
       let l := ls'' ∪ (ls'.to_list.filter $ λ l, prod.snd l = n).map prod.fst \ rs,
       l.mmap' $ λ l, do
        ext_attr_core.set l n b prio,
        ext_lemma_attr_core.set n () b prio }

add_tactic_doc
{ name                     := "ext",
  category                 := doc_category.attr,
  decl_names               := [`extensional_attribute],
  tags                     := ["rewrite", "logic"] }

-- We mark some existing extensionality lemmas.
attribute [ext] array.ext propext function.hfunext
attribute [ext [(→),thunk]] _root_.funext

-- We create some extensionality lemmas for existing structures.
attribute [ext] ulift

namespace plift
-- This is stronger than the one generated automatically.
@[ext] lemma ext {P : Prop} (a b : plift P) : a = b :=
begin
  cases a, cases b, refl
end
end plift

-- Conservatively, we'll only add extensionality lemmas for `has_*` structures
-- as they become useful.
attribute [ext] has_zero

namespace tactic

meta def try_intros : ext_patt → tactic ext_patt
| [] := try intros $> []
| (x::xs) :=
do tgt ← target >>= whnf,
   if tgt.is_pi
     then rintro [x] >> try_intros xs
     else pure (x :: xs)

meta def ext1 (xs : ext_patt) (cfg : apply_cfg := {}) : tactic ext_patt :=
do subject ← target >>= get_ext_subject,
   m ← get_ext_lemmas,
   do { rule ← m.find subject,
        applyc rule cfg } <|>
     do { ls ← get_ext_lemma_names,
          ls.any_of (λ n, applyc n cfg) } <|>
     fail format!"no applicable extensionality rule found for {subject}",
   try_intros xs

meta def ext : ext_patt → option ℕ → tactic unit
| _  (some 0) := skip
| xs n        := focus1 $ do
  ys ← ext1 xs, try (ext ys (nat.pred <$> n))


local postfix `?`:9001 := optional
local postfix *:9001 := many

/--
`ext1 id` selects and apply one extensionality lemma (with attribute
`ext`), using `id`, if provided, to name a local constant
introduced by the lemma. If `id` is omitted, the local constant is
named automatically, as per `intro`.
-/
meta def interactive.ext1 (xs : parse ext_parse) : tactic unit :=
ext1 xs $> ()

/--
- `ext` applies as many extensionality lemmas as possible;
- `ext ids`, with `ids` a list of identifiers, finds extentionality and applies them
  until it runs out of identifiers in `ids` to name the local constants.
- `ext` can also be given an `rcases` pattern in place of an identifier.
  This will destruct the introduced local constant.

When trying to prove:

```lean
α β : Type,
f g : α → set β
⊢ f = g
```

applying `ext x y` yields:

```lean
α β : Type,
f g : α → set β,
x : α,
y : β
⊢ y ∈ f x ↔ y ∈ f x
```

by applying functional extensionality and set extensionality.

When trying to prove:

```lean
α β γ : Type
f g : α × β → γ
⊢ f = g
```

applying `ext ⟨a, b⟩` yields:

```lean
α β γ : Type,
f g : α × β → γ,
a : α,
b : β
⊢ f (a, b) = g (a, b)
```

by applying functional extensionality and destructing the introduced pair.

A maximum depth can be provided with `ext x y z : 3`.
-/
meta def interactive.ext : parse ext_parse → parse (tk ":" *> small_nat)? → tactic unit
 | [] (some n) := iterate_range 1 n (ext1 [] $> ())
 | [] none     := repeat1 (ext1 [] $> ())
 | xs n        := tactic.ext xs n

/--
* `ext1 id` selects and apply one extensionality lemma (with
  attribute `ext`), using `id`, if provided, to name a
  local constant introduced by the lemma. If `id` is omitted, the
  local constant is named automatically, as per `intro`.

* `ext` applies as many extensionality lemmas as possible;
* `ext ids`, with `ids` a list of identifiers, finds extensionality lemmas
  and applies them until it runs out of identifiers in `ids` to name
  the local constants.
* `ext` can also be given an `rcases` pattern in place of an identifier.
  This will destruct the introduced local constant.

When trying to prove:

```lean
α β : Type,
f g : α → set β
⊢ f = g
```

applying `ext x y` yields:

```lean
α β : Type,
f g : α → set β,
x : α,
y : β
⊢ y ∈ f x ↔ y ∈ g x
```
by applying functional extensionality and set extensionality.

When trying to prove:

```lean
α β γ : Type
f g : α × β → γ
⊢ f = g
```

applying `ext ⟨a, b⟩` yields:

```lean
α β γ : Type,
f g : α × β → γ,
a : α,
b : β
⊢ f (a, b) = g (a, b)
```

by applying functional extensionality and destructing the introduced pair.

A maximum depth can be provided with `ext x y z : 3`.
-/
add_tactic_doc
{ name        := "ext1 / ext",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.ext1, `tactic.interactive.ext],
  tags        := ["rewriting", "logic"] }

end tactic
