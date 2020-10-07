/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import tactic.basic

/-!
# Singleton types

`α : Sort*` is `unique` if it has a unique element `default α`. Equivalently, `unique α` means
`inhabited α` and `subsingleton α`.

We use `Type*`-valued structure for `unique` instead of `Prop` to get better definitional equalities
for `default α`.
-/

universes u v w

variables {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α : Sort*` is `unique` if it has a unique element `default α`. We use `Type*`-valued
structure instead of `Prop` to get better definitional equalities for `default α`. -/
structure unique (α : Sort u) extends inhabited α :=
(uniq : ∀ a:α, a = default)

attribute [class] unique

instance punit.unique : unique punit.{u} :=
{ default := punit.star,
  uniq := λ x, punit_eq x _ }

instance fin.unique : unique (fin 1) :=
{ default := 0,
  uniq := λ ⟨n, hn⟩, fin.eq_of_veq
    (nat.eq_zero_of_le_zero (nat.le_of_lt_succ hn)) }

namespace unique
open function

section

variables [unique α]

@[priority 100] -- see Note [lower instance priority]
instance : inhabited α := to_inhabited ‹unique α›

lemma eq_default (a : α) : a = default α := uniq _ a

lemma default_eq (a : α) : default α = a := (uniq _ a).symm

@[priority 100] -- see Note [lower instance priority]
instance : subsingleton α := ⟨λ a b, by rw [eq_default a, eq_default b]⟩

lemma forall_iff {p : α → Prop} : (∀ a, p a) ↔ p (default α) :=
⟨λ h, h _, λ h x, by rwa [unique.eq_default x]⟩

lemma exists_iff {p : α → Prop} : Exists p ↔ p (default α) :=
⟨λ ⟨a, ha⟩, eq_default a ▸ ha, exists.intro (default α)⟩

end

@[simp] lemma pi.default_apply {β : Π a : α, Sort v} [Π a, inhabited (β a)] (a : α) :
  default (Π a, β a) a = default (β a) :=
rfl

instance pi.unique {β : Π a : α, Sort v} [Π a, unique (β a)] : unique (Π a, β a) :=
{ uniq := λ f, funext $ λ x, eq_default _,
  .. pi.inhabited α }

@[ext] protected lemma subsingleton_unique' : ∀ (h₁ h₂ : unique α), h₁ = h₂
| ⟨⟨x⟩, h⟩ ⟨⟨y⟩, _⟩ := by congr; rw [h x, h y]

instance subsingleton_unique : subsingleton (unique α) :=
⟨unique.subsingleton_unique'⟩

/-- Construct `unique` from `inhabited` and `subsingleton`. Making this an instance would create
a loop in the class inheritance graph. -/
def mk' (α : Sort u) [h₁ : inhabited α] [subsingleton α] : unique α :=
{ uniq := λ x, subsingleton.elim _ _, .. h₁ }

end unique

namespace function

variable {f : α → β}

/-- If the domain of a surjective function is a singleton,
then the codomain is a singleton as well. -/
protected def surjective.unique (hf : surjective f) [unique α] : unique β :=
{ default := f (default _),
  uniq := λ b, let ⟨a, ha⟩ := hf b in ha ▸ congr_arg f (unique.eq_default _) }

/-- If the codomain of an injective function is a subsingleton, then the domain
is a subsingleton as well. -/
protected lemma injective.subsingleton (hf : injective f) [subsingleton β] :
  subsingleton α :=
⟨λ x y, hf $ subsingleton.elim _ _⟩

/-- If `α` is inhabited and admits an injective map to a subsingleton type, then `α` is `unique`. -/
protected def injective.unique [inhabited α] [subsingleton β] (hf : injective f) : unique α :=
@unique.mk' _ _ hf.subsingleton

end function
