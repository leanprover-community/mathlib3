/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Eric Wieser
-/

/-!
# Reflection of universe variables

The `reflect` and `has_reflect` machinery (sometimes via the `` `(expr) `` syntax) allows
terms to be converted to the expression that constructs them. However, this construction does not
support universe variables.

This file provides a typeclass `reflected_univ.{u}` to match a universe variable `u` with a level
`l`, which allows `reflect` to be used universe-polymorphically.

## Main definitions

* `reflected_univ.{u}`: A typeclass for reflecting the universe `u` to a `level`.
* `reflect_univ.{u} : level`: Obtain the level of a universe by typeclass search.
* `tactic.interactive.reflect_name`: solve goals of the form `reflected (@foo.{u v})` by searching
  for `reflected_univ.{u}` instances.

-/

/-- A typeclass to translate a universe argument into a `level`. Note that `level.mvar` and
`level.param` are not supported.

Note that the `instance_priority` linter will complain if instance of this class have the default
priority, as it takes no arguments! Since it doesn't make any difference, we do what the linter
asks. -/
meta class {u} reflected_univ :=
(lvl : level)

universes u v w x y

/-- Reflect a universe variable `u` into a `level` via typeclass search. -/
meta def reflect_univ [reflected_univ.{u}] : level :=
reflected_univ.lvl

@[priority 100]
meta instance reflect_univ.zero : reflected_univ.{0} :=
⟨level.zero⟩

@[priority 100]
meta instance reflect_univ.succ [reflected_univ.{u}] : reflected_univ.{u+1} :=
⟨level.succ reflect_univ.{u}⟩

@[priority 100]
meta instance reflect_univ.max [reflected_univ.{u}] [reflected_univ.{v}] :
  reflected_univ.{max u v} :=
⟨level.max reflect_univ.{u} reflect_univ.{v}⟩

@[priority 100]
meta instance reflect_univ.imax [reflected_univ.{u}] [reflected_univ.{v}] :
  reflected_univ.{imax u v} :=
⟨level.imax reflect_univ.{u} reflect_univ.{v}⟩

section
local attribute [semireducible] reflected
/-- This definition circumvents the protection that `reflected` tried to enforce; so is private
such that it is only used by `tactic.interactive.reflect_name` where we have enforced the protection
manually. -/
private meta def reflected.of {α : Sort*} {a : α} (e : expr) : reflected _ a := e
end

/-- Reflect a universe-polymorphic name, by searching for `reflected_univ` instances. -/
meta def tactic.interactive.reflect_name : tactic unit :=
do
  tgt ← tactic.target,
  `(reflected _ %%x) ← pure tgt,
  expr.const name levels ← pure x,
  levels ← levels.mmap (λ l, do
    inst ← tactic.mk_instance (expr.const `reflected_univ [l]),
    pure $ expr.app (expr.const `reflect_univ [l]) inst),
  let levels := list.foldr (λ a l, `(@list.cons level %%a %%l)) `(@list.nil level) levels,
  let e := `(@expr.const tt %%`(name) %%levels),
  let e2 := ``(reflected.of %%e : %%tgt),
  e2 ← tactic.to_expr e2,
  tactic.exact e2

/-- Convenience helper for two consecutive `reflected.subst` applications -/
meta def reflected.subst₂ {α : Sort u} {β : α → Sort v} {γ : Π a, β a → Sort w}
  {f : Π a b, γ a b} {a : α} {b : β a} :
  reflected _ f → reflected _ a → reflected _ b → reflected _ (f a b) :=
(∘) reflected.subst ∘ reflected.subst

/-- Convenience helper for three consecutive `reflected.subst` applications -/
meta def reflected.subst₃ {α : Sort u} {β : α → Sort v} {γ : Π a, β a → Sort w}
  {δ : Π a b, γ a b → Sort x}
  {f : Π a b c, δ a b c} {a : α} {b : β a} {c : γ a b}:
  reflected _ f → reflected _ a → reflected _ b → reflected _ c → reflected _ (f a b c) :=
(∘) reflected.subst₂ ∘ reflected.subst

/-- Convenience helper for four consecutive `reflected.subst` applications -/
meta def reflected.subst₄ {α : Sort u} {β : α → Sort v} {γ : Π a, β a → Sort w}
  {δ : Π a b, γ a b → Sort x} {ε : Π a b c, δ a b c → Sort y}
  {f : Π a b c d, ε a b c d} {a : α} {b : β a} {c : γ a b} {d : δ a b c} :
  reflected _ f → reflected _ a → reflected _ b → reflected _ c → reflected _ d →
    reflected _ (f a b c d) :=
(∘) reflected.subst₃ ∘ reflected.subst

/-! ### Universe-polymorphic `has_reflect` instances -/

/-- Universe polymorphic version of the builtin `punit.reflect`. -/
meta instance punit.reflect' [reflected_univ.{u}] : has_reflect punit.{u}
| punit.star := by reflect_name

/-- Universe polymorphic version of the builtin `list.reflect`. -/
meta instance list.reflect' [reflected_univ.{u}] {α : Type u} [has_reflect α] [reflected _ α] :
  has_reflect (list α)
| []     := (by reflect_name : reflected _ @list.nil.{u}).subst `(α)
| (h::t) := (by reflect_name : reflected _ @list.cons.{u}).subst₃ `(α) `(h) (list.reflect' t)

meta instance ulift.reflect' [reflected_univ.{u}] [reflected_univ.{v}] {α : Type v}
  [reflected _ α] [has_reflect α] : has_reflect (ulift.{u v} α)
| (ulift.up x) := (by reflect_name : reflected _ @ulift.up.{u v}).subst₂ `(α) `(x)
