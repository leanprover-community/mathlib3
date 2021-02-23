/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import tactic.basic

/-!
# Types with a unique term

In this file we define a typeclass `unique`,
which expresses that a type has a unique term.
In other words, a type that is `inhabited` and a `subsingleton`.

## Main declaration

* `unique`: a typeclass that expresses that a type has a unique term.

## Main statements

* `unique.mk'`: an inhabited subsingleton type is `unique`. This can not be an instance because it
  would lead to loops in typeclass inference.

* `function.surjective.unique`: if the domain of a surjective function is `unique`, then its
  codomain is `unique` as well.

* `function.injective.subsingleton`: if the codomain of an injective function is `subsingleton`,
  then its domain is `subsingleton` as well.

* `function.injective.unique`: if the codomain of an injective function is `subsingleton` and its
  domain is `inhabited`, then its domain is `unique`.

## Implementation details

The typeclass `unique α` is implemented as a type,
rather than a `Prop`-valued predicate,
for good definitional properties of the default term.

-/

universes u v w

variables {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `unique α` expresses that `α` is a type with a unique term `default α`.

This is implemented as a type, rather than a `Prop`-valued predicate,
for good definitional properties of the default term. -/
@[ext]
structure unique (α : Sort u) extends inhabited α :=
(uniq : ∀ a:α, a = default)

attribute [class] unique

instance punit.unique : unique punit.{u} :=
{ default := punit.star,
  uniq := λ x, punit_eq x _ }

lemma fin.eq_zero : ∀ n : fin 1, n = 0
| ⟨n, hn⟩ := fin.eq_of_veq (nat.eq_zero_of_le_zero (nat.le_of_lt_succ hn))

instance {n : ℕ} : inhabited (fin n.succ) := ⟨0⟩

@[simp] lemma fin.default_eq_zero (n : ℕ) : default (fin n.succ) = 0 := rfl

instance fin.unique : unique (fin 1) :=
{ uniq := fin.eq_zero, .. fin.inhabited }

namespace unique
open function

section

variables [unique α]

@[priority 100] -- see Note [lower instance priority]
instance : inhabited α := to_inhabited ‹unique α›

lemma eq_default (a : α) : a = default α := uniq _ a

lemma default_eq (a : α) : default α = a := (uniq _ a).symm

@[priority 100] -- see Note [lower instance priority]
instance : subsingleton α := subsingleton_of_forall_eq _ eq_default

lemma forall_iff {p : α → Prop} : (∀ a, p a) ↔ p (default α) :=
⟨λ h, h _, λ h x, by rwa [unique.eq_default x]⟩

lemma exists_iff {p : α → Prop} : Exists p ↔ p (default α) :=
⟨λ ⟨a, ha⟩, eq_default a ▸ ha, exists.intro (default α)⟩

end

@[ext] protected lemma subsingleton_unique' : ∀ (h₁ h₂ : unique α), h₁ = h₂
| ⟨⟨x⟩, h⟩ ⟨⟨y⟩, _⟩ := by congr; rw [h x, h y]

instance subsingleton_unique : subsingleton (unique α) :=
⟨unique.subsingleton_unique'⟩

/-- Construct `unique` from `inhabited` and `subsingleton`. Making this an instance would create
a loop in the class inheritance graph. -/
def mk' (α : Sort u) [h₁ : inhabited α] [subsingleton α] : unique α :=
{ uniq := λ x, subsingleton.elim _ _, .. h₁ }

end unique

@[simp] lemma pi.default_def {β : Π a : α, Sort v} [Π a, inhabited (β a)] :
  default (Π a, β a) = λ a, default (β a) :=
rfl

lemma pi.default_apply {β : Π a : α, Sort v} [Π a, inhabited (β a)] (a : α) :
  default (Π a, β a) a = default (β a) :=
rfl

instance pi.unique {β : Π a : α, Sort v} [Π a, unique (β a)] : unique (Π a, β a) :=
{ uniq := λ f, funext $ λ x, unique.eq_default _,
  .. pi.inhabited α }

/-- There is a unique function on an empty domain. -/
def pi.unique_of_empty (h : α → false) (β : Π a : α, Sort v) : unique (Π a, β a) :=
{ default := λ a, (h a).elim,
  uniq := λ f, funext $ λ a, (h a).elim }

/-- There is a unique function whose domain is `pempty`. -/
instance pi.pempty_unique (β : pempty.{u} → Sort v) : unique (Π a, β a) :=
pi.unique_of_empty pempty.elim β

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
