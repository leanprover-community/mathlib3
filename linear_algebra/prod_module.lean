/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Semigroup, monoid, group and module structures on product spaces.
-/

import data.prod linear_algebra.basic
open set function

section module
variables [ring α] [module α β] [module α γ] [module α δ]
include α

lemma is_linear_map_prod_fst : is_linear_map (prod.fst : β × γ → β) :=
⟨assume x y, rfl, assume x y, rfl⟩

lemma is_linear_map_prod_snd : is_linear_map (prod.snd : β × γ → γ) :=
⟨assume x y, rfl, assume x y, rfl⟩

lemma is_linear_map_prod_mk {f : δ → β} {g : δ → γ} (hf : is_linear_map f) (hg : is_linear_map g):
  is_linear_map (λd, (f d, g d)) :=
⟨assume x y, mk.inj_iff.mpr ⟨hf.add _ _, hg.add _ _⟩,
  assume x y, mk.inj_iff.mpr ⟨hf.smul _ _, hg.smul _ _⟩⟩

lemma is_linear_map_prod_inl : is_linear_map (prod.inl : β → β × γ) :=
is_linear_map_prod_mk is_linear_map.id is_linear_map.map_zero

lemma is_linear_map_prod_inr : is_linear_map (prod.inr : γ → β × γ) :=
is_linear_map_prod_mk is_linear_map.map_zero is_linear_map.id

instance {s : set β} {t : set γ} [is_submodule s] [is_submodule t] : is_submodule (set.prod s t) :=
@is_submodule.inter_submodule _ _ _ _ _ _
  (is_submodule.preimage is_linear_map_prod_fst) (is_submodule.preimage is_linear_map_prod_snd)

lemma span_prod {s : set β} {t : set γ} : span (set.prod s t) ⊆ set.prod (span s) (span t) :=
span_minimal prod.is_submodule (set.prod_mono subset_span subset_span)

lemma span_inl_union_inr {s : set β} {t : set γ} :
  span (inl '' s ∪ inr '' t) = set.prod (span s) (span t) :=
span_eq prod.is_submodule
  (set.union_subset
    (set.image_subset_iff.mpr $ assume b hbs, ⟨subset_span hbs, is_submodule.zero⟩)
    (set.image_subset_iff.mpr $ assume c hct, ⟨is_submodule.zero, subset_span hct⟩))
  (assume ⟨b, c⟩ ⟨hb, hc⟩,
  begin
    simp [span_union, span_image_of_linear_map is_linear_map_prod_inl,
      span_image_of_linear_map is_linear_map_prod_inr],
    exact ⟨b, 0, ⟨b, hb, rfl⟩, 0, c, ⟨c, hc, rfl⟩,
      mk.inj_iff.mpr ⟨(add_zero _).symm, (zero_add _).symm⟩⟩
  end)

lemma linear_independent_inl_union_inr {s : set β} {t : set γ}
  (hs : linear_independent s) (ht : linear_independent t) :
  linear_independent (inl '' s ∪ inr '' t) :=
linear_independent_union
  (hs.image is_linear_map_prod_inl $ assume a ha b hb eq, injective_inl eq)
  (ht.image is_linear_map_prod_inr $ assume a ha b hb eq, injective_inr eq)
  (subset.antisymm
    (by rw [span_image_of_linear_map is_linear_map_prod_inl,
      span_image_of_linear_map is_linear_map_prod_inr];
      exact assume ⟨b, c⟩ ⟨⟨b', hb', beq⟩, ⟨c', hc', ceq⟩⟩,
        have c = 0, from (prod.mk.inj beq).2.symm,
        have b = 0, from (prod.mk.inj ceq).1.symm,
        by simp *; refl)
    (by simp [is_submodule.zero]))

lemma is_basis_inl_union_inr {s : set β} {t : set γ}
  (hs : is_basis s) (ht : is_basis t) : is_basis (inl '' s ∪ inr '' t) :=
⟨linear_independent_inl_union_inr hs.1 ht.1,
  by rw [span_inl_union_inr]; exact assume ⟨b, c⟩, ⟨hs.2 b, ht.2 c⟩⟩

end module

instance {f : field α} [vector_space α β] [vector_space α γ] : vector_space α (β × γ) :=
{..prod.module}

end prod
