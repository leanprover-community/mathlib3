/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.majorize
import analysis.convex.function

/-!
# Karamata's inequality
-/

open order_dual set

variables {𝕜 α β : Type*}

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid α] [preorder β] {f : multiset α → β}

def schur_convex (f : multiset α → β) : Prop := ∀ ⦃s t⦄, s ≼ᵐ t → f s ≤ f t

def schur_concave (f : multiset α → β) : Prop := ∀ ⦃s t⦄, s ≼ᵐ t → f t ≤ f s

def strict_schur_convex (f : multiset α → β) : Prop := ∀ ⦃s t⦄, s ≺ᵐ t → f s < f t

def strict_schur_concave (f : multiset α → β) : Prop := ∀ ⦃s t⦄, s ≺ᵐ t → f t < f s

lemma schur_convex.dual : schur_convex f → schur_concave (to_dual ∘ f) := id
lemma schur_concave.dual : schur_concave f → schur_convex (to_dual ∘ f) := id
lemma strict_schur_convex.dual : strict_schur_convex f → strict_schur_concave (to_dual ∘ f) := id
lemma strict_schur_concave.dual : strict_schur_concave f → strict_schur_convex (to_dual ∘ f) := id

end linear_ordered_add_comm_monoid

section linear_ordered_cancel_add_comm_monoid
variables [linear_ordered_cancel_add_comm_monoid α] [preorder β] {f : multiset α → β}

protected lemma strict_schur_convex.schur_convex (hf : strict_schur_convex f) : schur_convex f :=
begin
  rintro s t h,
  obtain h | rfl := h.strict_majorize_or_eq,
  { exact (hf h).le },
  { refl }
end

end linear_ordered_cancel_add_comm_monoid

variables [linear_ordered_field 𝕜] [linear_ordered_add_comm_group α] [ordered_add_comm_group β]
  [module 𝕜 α] [module 𝕜 β] [ordered_smul 𝕜 α] [ordered_smul 𝕜 β] {f : α → β}

/-- **Karamata's inequality**: Convex functions are Schur-convex. -/
lemma convex_on.schur_convex (hf : convex_on 𝕜 univ f) : schur_convex (λ s, (s.map f).sum) :=
begin
  rintro s t hst,
  sorry
end

/-- **Karamata's inequality**: Concave functions are Schur-concave. -/
lemma concave_on.schur_concave (hf : concave_on 𝕜 univ f) : schur_concave (λ s, (s.map f).sum) :=
@convex_on.schur_convex 𝕜 _ βᵒᵈ _ _ _ _ _ _ _ _ hf.dual

/-- Strict **Karamata's inequality**: Strictly convex functions are strictly Schur-convex. -/
lemma strict_convex_on.strict_schur_convex (hf : strict_convex_on 𝕜 univ f) :
  strict_schur_convex (λ s, (s.map f).sum) :=
begin
  rintro s t hst,
  sorry
end

/-- Strict **Karamata's inequality**: Strictly concave functions are strictly Schur-concave. -/
lemma strict_concave_on.strict_schur_concave (hf : strict_concave_on 𝕜 univ f) :
  strict_schur_concave (λ s, (s.map f).sum) :=
@strict_convex_on.strict_schur_convex 𝕜 _ βᵒᵈ _ _ _ _ _ _ _ _ hf.dual
