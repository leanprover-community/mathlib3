
import tactic.basic

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
