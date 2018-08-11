
import tactic.basic

universes u₁ u₂

/--
 Tag lemmas of the form:

 ```
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```
 -/
@[user_attribute]
meta def extensional_attribute : user_attribute :=
{ name := `extensionality,
  descr := "lemmas usable by `ext` tactic" }

attribute [extensionality] _root_.funext array.ext

namespace ulift
@[extensionality] lemma ext {α : Type u₁} (X Y : ulift.{u₂} α) (w : X.down = Y.down) : X = Y :=
begin
  cases X, cases Y, dsimp at w, rw w,
end
end ulift

namespace tactic
open interactive interactive.types
open lean.parser nat

local postfix `?`:9001 := optional
local postfix *:9001 := many

/--
  `ext1 id` selects and apply one extensionality lemma (with attribute
  `extensionality`), using `id`, if provided, to name a local constant
  introduced by the lemma. If `id` is omitted, the local constant is
  named automatically, as per `intro`.
 -/
meta def interactive.ext1 (x : parse ident_ ?) : tactic unit :=
do ls ← attribute.get_instances `extensionality,
   ls.any_of (λ l, applyc l) <|> fail "no applicable extensionality rule found",
   try ( interactive.intro x )

meta def ext_arg :=
prod.mk <$> (some <$> small_nat)
        <*> (tk "with" *> ident_* <|> pure [])
<|> prod.mk none <$> (ident_*)

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

  A maximum depth can be provided with `ext 3 with x y z`.
  -/
meta def interactive.ext : parse ext_arg → tactic unit
 | (some n, []) := interactive.ext1 none >> iterate_at_most (pred n) (interactive.ext1 none)
 | (none,   []) := interactive.ext1 none >> repeat (interactive.ext1 none)
 | (n, xs) := tactic.ext xs n

end tactic
