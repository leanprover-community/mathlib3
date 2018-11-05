import category_theory.limits.limits
import category_theory.limits.products
import category_theory.discrete_category

open category_theory

namespace category_theory.limits

universes u v

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section terminal

def is_terminal (X : C) := is_limit ({ X := X, π := { app := pempty.rec _ } } : cone (functor.empty C))

variables {X : C}

instance is_terminal_subsingleton : subsingleton (is_terminal X) := by dsimp [is_terminal]; apply_instance

variable (C)

class has_terminal :=
(terminal : C)
(is_terminal : is_terminal terminal . obviously)

def terminal_object [has_terminal.{u v} C] := has_terminal.terminal

-- Special cases of this may be marked with [instance] as desired.
def has_terminal_of_has_limits [limits.has_limits.{u v} C] : has_terminal.{u v} C :=
{ terminal := limit (functor.empty C),
  is_terminal := is_limit_invariance _ _ (by tidy) (limit.universal_property (functor.empty C)) }

def has_terminal_of_has_products [has_products.{u v} C] : has_terminal.{u v} C :=
{ terminal := limits.pi (pempty.rec _),
  is_terminal := sorry }

instance has_limit_of_has_terminal [has_terminal.{u v} C] : has_limit (functor.empty C) := sorry

end terminal

end category_theory.limits
