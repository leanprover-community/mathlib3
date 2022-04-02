/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.elementary_maps

/-!
#

## Main Definitions

## TODO

-/

universes u v w



namespace first_order
namespace language
open Structure

variables (L : language.{u v}) {M : Type w} [nonempty M] [L.Structure M]

/-- A language consisting of Skolem functions for another language.
Called `skolem₁` because it is the first step in building a Skolemization of a language. -/
def skolem₁ : language := ⟨λ n, L.bounded_formula empty (n + 1), λ _, empty⟩

variables {L}

noncomputable instance skolem₁_Structure : L.skolem₁.Structure M :=
⟨λ n φ x, classical.epsilon (λ a, φ.realize default (fin.snoc x a : _ → M)), λ _ r, empty.elim r⟩

lemma substructure.skolem₁_reduct_is_elementary (S : (L.sum L.skolem₁).substructure M) :
  (Lhom.sum_inl.substructure_reduct S).is_elementary :=
begin
  apply (Lhom.sum_inl.substructure_reduct S).is_elementary_of_exists,
  intros n φ x a h,
  let φ' : (L.sum L.skolem₁).functions n := (Lhom.sum_inr.on_function φ),
  exact ⟨⟨fun_map φ' (coe ∘ x), S.fun_mem (Lhom.sum_inr.on_function φ) (coe ∘ x) (λ i, (x i).2)⟩,
    classical.epsilon_spec ⟨a, h⟩⟩,
end

noncomputable def substructure.elementary_skolem₁_reduct (S : (L.sum L.skolem₁).substructure M) :
  L.elementary_substructure M :=
⟨Lhom.sum_inl.substructure_reduct S, λ _, S.skolem₁_reduct_is_elementary⟩

lemma substructure.coe_sort_elementary_skolem₁_reduct
  (S : (L.sum L.skolem₁).substructure M) :
  (S.elementary_skolem₁_reduct : Type w) = S :=
rfl

open cardinal
open_locale cardinal

variables (L) (M)

theorem exists_small_elementary_substructure :
  ∃ (S : L.elementary_substructure M), small.{max u v} S :=
begin
  refine ⟨substructure.elementary_skolem₁_reduct ⊥, _⟩,
  rw [substructure.coe_sort_elementary_skolem₁_reduct],
  apply_instance,
end

end language
end first_order
