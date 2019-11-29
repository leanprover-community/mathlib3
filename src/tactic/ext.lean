/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.rcases data.list.defs data.prod data.sum
universes u₁ u₂

open interactive interactive.types
open lean.parser nat tactic

/--
`derive_struct_ext_lemma n` generates two extensionality lemmas based on
the equality of all non-propositional projections.

On the following:

```
@[ext]
structure foo (α : Type*) :=
(x y : ℕ)
(z : {z // z < x})
(k : α)
(h : x < y)
```

`derive_struct_lemma` generates:

```
lemma foo.ext : ∀ {α : Type u_1} (x y : foo α), x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y
lemma foo.ext_iff : ∀ {α : Type u_1} (x y : foo α), x = y ↔ x.x = y.x ∧ x.y = y.y ∧ x.z == y.z ∧ x.k = y.k
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

/--
 Tag lemmas of the form:

 ```
 @[ext]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 The attribute indexes extensionality lemma using the type of the
 objects (i.e. `my_collection`) which it gets from the statement of
 the lemma.  In some cases, the same lemma can be used to state the
 extensionality of multiple types that are definitionally equivalent.

 ```
 attribute [ext [(→),thunk,stream]] funext
 ```

 Those parameters are cumulative. The following are equivalent:

 ```
 attribute [ext [(→),thunk]] funext
 attribute [ext [stream]] funext
 ```
 and
 ```
 attribute [ext [(→),thunk,stream]] funext
 ```

 One removes type names from the list for one lemma with:
 ```
 attribute [ext [-stream,-thunk]] funext
  ```

 Also, the following:

 ```
 @[ext]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 is equivalent to

 ```
 @[ext *]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 This allows us specify type synonyms along with the type
 that referred to in the lemma statement.

 ```
 @[ext [*,my_type_synonym]]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 Attribute `ext` can be applied to a structure to generate its extensionality lemma:

 ```
 @[ext]
 structure foo (α : Type*) :=
 (x y : ℕ)
 (z : {z // z < x})
 (k : α)
 (h : x < y)
 ```

 will generate:

 ```
 @[ext] lemma foo.ext : ∀ {α : Type u_1} (x y : foo α), x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y
 lemma foo.ext_iff : ∀ {α : Type u_1} (x y : foo α), x = y ↔ x.x = y.x ∧ x.y = y.y ∧ x.z == y.z ∧ x.k = y.k
 ```

 -/
@[user_attribute]
meta def extensional_attribute : user_attribute (name_map name) (bool × list ext_param_type × list name × list (name × name)) :=
{ name := `ext,
  descr := "lemmas usable by `ext` tactic",
  cache_cfg := { mk_cache := λ ls,
                          do { attrs ← ls.mmap $ λ l,
                                     do { ⟨_,_,ls,_⟩ ← extensional_attribute.get_param l,
                                          pure $ prod.mk <$> ls <*> pure l },
                               pure $ rb_map.of_list $ attrs.join },
                 dependencies := [] },
  parser :=
    do { ls ← pure <$> ext_param <|> list_of ext_param <|> pure [],
         m ← extensional_attribute.get_cache,
         pure $ (ff,ls,[],m.to_list)  },
  after_set := some $ λ n _ b,
    do (ff,ls,_,ls') ← extensional_attribute.get_param n | pure (),
       e ← get_env,
       n ← if (e.structure_fields n).is_some
         then derive_struct_ext_lemma n
         else pure n,
       s ← mk_const n >>= infer_type >>= get_ext_subject,
       let (rs,ls'') := if ls.empty
                           then ([],[s])
                           else ls.partition_map (sum.map (flip option.get_or_else s) (flip option.get_or_else s)),
       ls''.mmap' (equiv_type_constr s),
       let l := ls'' ∪ (ls'.filter $ λ l, prod.snd l = n).map prod.fst \ rs,
       extensional_attribute.set n (tt,[],l,[]) b }

attribute [ext] array.ext propext prod.ext
attribute [ext [(→),thunk]] _root_.funext

namespace ulift
@[ext] lemma ext {α : Type u₁} (X Y : ulift.{u₂} α) (w : X.down = Y.down) : X = Y :=
begin
  cases X, cases Y, dsimp at w, rw w,
end
end ulift

namespace plift
@[ext] lemma ext {P : Prop} (a b : plift P) : a = b :=
begin
  cases a, cases b, refl
end
end plift

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
   m ← extensional_attribute.get_cache,
   do { rule ← m.find subject,
        applyc rule cfg } <|>
     do { ls ← attribute.get_instances `ext,
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

  When trying to prove:

  ```
  α β : Type,
  f g : α → set β
  ⊢ f = g
  ```

  applying `ext x y` yields:

  ```
  α β : Type,
  f g : α → set β,
  x : α,
  y : β
  ⊢ y ∈ f x ↔ y ∈ f x
  ```

  by applying functional extensionality and set extensionality.

  A maximum depth can be provided with `ext x y z : 3`.
  -/
meta def interactive.ext : parse ext_parse → parse (tk ":" *> small_nat)? → tactic unit
 | [] (some n) := iterate_range 1 n (ext1 [] $> ())
 | [] none     := repeat1 (ext1 [] $> ())
 | xs n        := tactic.ext xs n

end tactic
