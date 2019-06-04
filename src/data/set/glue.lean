/- gluing together functions over sets. -/

import data.set

variables {α : Type*} {β : Sort*} {ι : Type*}
open set function

local attribute [instance] classical.prop_decidable

namespace function

section glue

/- given a cover of sᵢ of X and functions fᵢ defined on sᵢ,
   construct a function f : X → Y : at each x, take f i to be
   some arbitrary fᵢ x where x ∈ sᵢ. -/
noncomputable def glue_on_Union {s : ι → set α}
  (hU : ∀ x, x ∈ ⋃ i, s i) (f : ι → α → β) : α → β :=
λ x, f (classical.some (mem_Union.1 (hU x))) x

variables {x : α} {s : ι → set α} {f : ι → α → β}

variable (hU   : ∀ x, x ∈ ⋃ i, s i)
variable (hUeq : ∀ i j x, x ∈ s i ∩ s j → f i x = f j x)

/- if the functions being glued agree on all the intersections, then they
   agree as well with the function resulting from the gluing. -/
lemma glue_on_Union_eq {i : ι} (hi : x ∈ s i) : glue_on_Union hU f x = f i x :=
have hq : ∀ j, x ∈ s j → f j x = f i x, from λ j hj,
  hUeq j i x ⟨hj, hi⟩, classical.some_spec2 _ hq

lemma glue_on_Union_unique {f' : α → β} (hf' : ∀ i x, x ∈ s i → f' x = f i x) :
  glue_on_Union hU f = f' :=
funext $ λ x,
  have hi : _, from (classical.some_spec $ mem_Union.1 (hU x)),
  eq.trans (glue_on_Union_eq _ hUeq hi) (hf' _ _ hi).symm

/- gluing on the union of two sets. -/
noncomputable def glue_on_union (A B : set α) (f₁ f₂ : α → β) : α → β :=
  λ x, ite (x ∈ A) (f₁ x) (f₂ x)

variables {A B : set α} {f₁ f₂ : α → β}
variable  (heq : ∀ x' ∈ A ∩ B, f₁ x' = f₂ x')

lemma glue_on_union_eq_left  (hx : x ∈ A) : glue_on_union A B f₁ f₂ x = f₁ x :=
if_pos hx

lemma glue_on_union_eq_right (hx : x ∈ B) : glue_on_union A B f₁ f₂ x = f₂ x :=
have x ∈ A → glue_on_union A B f₁ f₂ x = f₂ x, from
  (λ hA, eq.trans (glue_on_union_eq_left hA) (heq _ ⟨hA, hx⟩)),
classical.by_cases this (λ hn, if_neg hn)

lemma glue_on_union_unique {f' : α → β} (h : ∀ x, x ∈ A ∪ B)
  (hA : ∀ x ∈ A, f' x = f₁ x) (hB : ∀ x ∈ B, f' x = f₂ x) :
  f' = glue_on_union A B f₁ f₂ :=
  funext $ λ x, or.elim (h x)
    (λ hx, eq.trans (hA _ hx) (glue_on_union_eq_left      hx).symm)
    (λ hx, eq.trans (hB _ hx) (glue_on_union_eq_right heq hx).symm)

end glue

end function
