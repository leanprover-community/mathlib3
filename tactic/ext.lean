
import tactic.basic

universes u₁ u₂

open interactive interactive.types
open lean.parser nat tactic

meta def get_ext_subject : expr → tactic name
| (expr.pi n bi d b) :=
  do v  ← mk_local' n bi d,
     b' ← whnf $ b.instantiate_var v,
     get_ext_subject b'
| (expr.app _ e) :=
  do t ← infer_type e,
     pure $ t.get_app_fn.const_name
| _ := pure name.anonymous

open native

meta def rident := do i ← ident, resolve_constant i

/--
 Tag lemmas of the form:

 ```
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```
 -/
@[user_attribute]
meta def extensional_attribute : user_attribute (name_map name) (list name) :=
{ name := `extensionality,
  descr := "lemmas usable by `ext` tactic",
  cache_cfg := { mk_cache := λ ls,
                          do { attrs ← ls.mmap $ λ l,
                                     do { ls ← extensional_attribute.get_param l,
                                          if ls.empty
                                          then list.ret <$> (prod.mk <$> (mk_const l >>= infer_type >>= get_ext_subject)
                                                                     <*> pure l)
                                          else pure $ prod.mk <$> ls <*> pure l },
                               pure $ rb_map.of_list $ attrs.join },
                 dependencies := [] },
  parser := many (name.anonymous <$ tk "*" <|> rident) }

attribute [extensionality] array.ext
attribute [extensionality * thunk] _root_.funext

namespace ulift
@[extensionality] lemma ext {α : Type u₁} (X Y : ulift.{u₂} α) (w : X.down = Y.down) : X = Y :=
begin
  cases X, cases Y, dsimp at w, rw w,
end
end ulift

namespace tactic

meta def ext1 (xs : list name) : tactic (list name) :=
do subject ← target >>= get_ext_subject,
   m ← extensional_attribute.get_cache,
   do { rule ← m.find subject,
        applyc rule } <|>
     do { ls ← attribute.get_instances `extensionality,
          ls.any_of applyc } <|>
     fail format!"no applicable extensionality rule found for {subject}",
   try_intros xs

meta def ext : list name → option ℕ → tactic unit
| _  (some 0) := skip
| xs n        := focus1 $ do
  ys ← ext1 xs, try (ext ys (nat.pred <$> n))


local postfix `?`:9001 := optional
local postfix *:9001 := many

/--
  `ext1 id` selects and apply one extensionality lemma (with attribute
  `extensionality`), using `id`, if provided, to name a local constant
  introduced by the lemma. If `id` is omitted, the local constant is
  named automatically, as per `intro`.
 -/
meta def interactive.ext1 (xs : parse ident_*) : tactic unit :=
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
meta def interactive.ext : parse ident_* → parse (tk ":" *> small_nat)? → tactic unit
 | [] (some n) := iterate_range 1 n (ext1 [] $> ())
 | [] none     := repeat1 (ext1 [] $> ())
 | xs n        := tactic.ext xs n

end tactic
