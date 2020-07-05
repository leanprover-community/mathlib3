/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import logic.unique
import tactic.localized
import tactic.push_neg

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
(exists_ne : ∃ (x y : α), x ≠ y)

lemma exists_ne (α : Type*) [nontrivial α] :
  ∃ (x y : α), x ≠ y :=
nontrivial.exists_ne

lemma exists_ne' [nontrivial α] (x : α) : ∃ y, y ≠ x :=
begin
  rcases exists_ne α with ⟨y, y', h⟩,
  by_cases hx : x = y,
  { rw ← hx at h,
    exact ⟨y', h.symm⟩ },
  { exact ⟨y, ne.symm hx⟩ }
end

lemma nontrivial_of_ne (x y : α) (h : x ≠ y) : nontrivial α :=
{ exists_ne := ⟨x, y, h⟩ }

instance nontrivial.to_nonempty [nontrivial α] : nonempty α :=
let ⟨x, _⟩ := exists_ne α in ⟨x⟩

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

/-- A type is either a subsingleton or nontrivial. -/
lemma subsingleton_or_nontrivial (α : Type*) :  subsingleton α ∨ nontrivial α :=
begin
  classical,
  by_cases h : nontrivial α,
  { right, exact h },
  { left, constructor, assume x y, contrapose! h, exact nontrivial_of_ne x y h },
end

instance nontrivial_prod_left [nontrivial α] [nonempty β] : nontrivial (α × β) :=
begin
  inhabit β,
  rcases exists_ne α with ⟨x, y, h⟩,
  use [(x, default β), (y, default β)],
  contrapose! h,
  exact congr_arg prod.fst h
end

instance nontrivial_prod_right [nontrivial α] [nonempty β] : nontrivial (β × α) :=
begin
  inhabit β,
  rcases exists_ne α with ⟨x, y, h⟩,
  use [(default β, x), (default β, y)],
  contrapose! h,
  exact congr_arg prod.snd h
end

instance option.nontrivial [nonempty α] : nontrivial (option α) :=
by { inhabit α, use [none, some (default α)] }
