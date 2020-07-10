/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import logic.unique
import logic.function.basic

/-!
# Nontrivial types

A type is *nontrivial* if it contains at least two elements. This is useful in particular for rings
(where it is equivalent to the fact that zero is different from one) and for vector spaces
(where it is equivalent to the fact that the dimension is positive).

We introduce a typeclass `nontrivial` formalizing this property.
-/

variables {α : Type*} {β : Type*}

open_locale classical

/-- Predicate typeclass for expressing that a type is not reduced to a single element. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. -/
class nontrivial (α : Type*) : Prop :=
(exists_pair_ne : ∃ (x y : α), x ≠ y)

lemma nontrivial_iff : nontrivial α ↔ ∃ (x y : α), x ≠ y :=
⟨λ h, h.exists_pair_ne, λ h, ⟨h⟩⟩

lemma exists_pair_ne (α : Type*) [nontrivial α] : ∃ (x y : α), x ≠ y :=
nontrivial.exists_pair_ne

lemma exists_ne [nontrivial α] (x : α) : ∃ y, y ≠ x :=
begin
  rcases exists_pair_ne α with ⟨y, y', h⟩,
  by_cases hx : x = y,
  { rw ← hx at h,
    exact ⟨y', h.symm⟩ },
  { exact ⟨y, ne.symm hx⟩ }
end

lemma nontrivial_of_ne (x y : α) (h : x ≠ y) : nontrivial α :=
⟨⟨x, y, h⟩⟩

section prio
set_option default_priority 100 -- see Note [default priority]

instance nontrivial.to_nonempty [nontrivial α] : nonempty α :=
let ⟨x, _⟩ := exists_pair_ne α in ⟨x⟩

end prio

/-- An inhabited type is either nontrivial, or has a unique element. -/
noncomputable def nontrivial_psum_unique (α : Type*) [inhabited α] :
  psum (nontrivial α) (unique α) :=
if h : nontrivial α then psum.inl h else psum.inr
{ default := default α,
  uniq := λ (x : α),
  begin
    change x = default α,
    contrapose! h,
    use [x, default α]
  end }

lemma subsingleton_iff : subsingleton α ↔ ∀ (x y : α), x = y :=
⟨by { introsI h, exact subsingleton.elim }, λ h, ⟨h⟩⟩

lemma not_nontrivial_iff_subsingleton : ¬(nontrivial α) ↔ subsingleton α :=
by { rw [nontrivial_iff, subsingleton_iff], push_neg, refl }

/-- A type is either a subsingleton or nontrivial. -/
lemma subsingleton_or_nontrivial (α : Type*) :  subsingleton α ∨ nontrivial α :=
by { rw [← not_nontrivial_iff_subsingleton, or_comm], exact classical.em _ }

instance nontrivial_prod_left [nontrivial α] [nonempty β] : nontrivial (α × β) :=
begin
  inhabit β,
  rcases exists_pair_ne α with ⟨x, y, h⟩,
  use [(x, default β), (y, default β)],
  contrapose! h,
  exact congr_arg prod.fst h
end

instance nontrivial_prod_right [nontrivial α] [nonempty β] : nontrivial (β × α) :=
begin
  inhabit β,
  rcases exists_pair_ne α with ⟨x, y, h⟩,
  use [(default β, x), (default β, y)],
  contrapose! h,
  exact congr_arg prod.snd h
end

instance option.nontrivial [nonempty α] : nontrivial (option α) :=
by { inhabit α, use [none, some (default α)] }

instance function.nontrivial [nonempty α] [nontrivial β] : nontrivial (α → β) :=
begin
  rcases exists_pair_ne β with ⟨x, y, h⟩,
  use [λ _, x, λ _, y],
  contrapose! h,
  inhabit α,
  exact congr_fun h (default α)
end

/-- Pushforward a `nontrivial` instance along an injective function. -/
protected lemma function.injective.nontrivial [nontrivial α]
  {f : α → β} (hf : function.injective f) : nontrivial β :=
let ⟨x, y, h⟩ := exists_pair_ne α in ⟨⟨f x, f y, hf.ne h⟩⟩

/-- Pullback a `nontrivial` instance along a surjective function. -/
protected lemma function.surjective.nontrivial [nontrivial β]
  {f : α → β} (hf : function.surjective f) : nontrivial α :=
begin
  rcases exists_pair_ne β with ⟨x, y, h⟩,
  rcases hf x with ⟨x', hx'⟩,
  rcases hf y with ⟨y', hy'⟩,
  have : x' ≠ y', by { contrapose! h, rw [← hx', ← hy', h] },
  exact ⟨⟨x', y', this⟩⟩
end
