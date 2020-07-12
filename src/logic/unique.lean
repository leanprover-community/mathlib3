/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import tactic.basic

universes u v w

variables {α : Sort u} {β : Sort v} {γ : Sort w}

@[ext]
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

protected lemma subsingleton_unique' : ∀ (h₁ h₂ : unique α), h₁ = h₂
| ⟨⟨x⟩, h⟩ ⟨⟨y⟩, _⟩ := by congr; rw [h x, h y]

instance subsingleton_unique : subsingleton (unique α) :=
⟨unique.subsingleton_unique'⟩

end unique

namespace function

variable {f : α → β}

/-- If the domain of a surjective function is a singleton,
then the codomain is a singleton as well. -/
def surjective.unique (hf : surjective f) [unique α] : unique β :=
{ default := f (default _),
  uniq := λ b, let ⟨a, ha⟩ := hf b in ha ▸ congr_arg f (unique.eq_default _) }

/-- If the codomain of an injective function is a subsingleton, then the domain
is a subsingleton as well. -/
lemma injective.comap_subsingleton (hf : injective f) [subsingleton β] :
  subsingleton α :=
⟨λ x y, hf $ subsingleton.elim _ _⟩

end function

lemma nonempty_unique_or_exists_ne (x : α) : nonempty (unique α) ∨ ∃ y, y ≠ x :=
classical.by_cases or.inr
  (λ h, or.inl ⟨{ default := x,
    uniq := λ y, classical.by_contradiction $ λ hy, h ⟨y, hy⟩ }⟩)

lemma subsingleton_or_exists_ne (x : α) : subsingleton α ∨ ∃ y, y ≠ x :=
(nonempty_unique_or_exists_ne x).elim
  (λ ⟨h⟩, or.inl $ @unique.subsingleton _ h)
  or.inr
