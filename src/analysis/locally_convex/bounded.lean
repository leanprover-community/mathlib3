import analysis.normed.normed_field
import analysis.seminorm
import topology.algebra.module.basic
import topology.bornology.basic

variables {𝕜 E : Type*}

open_locale topological_space pointwise

/-def is_bounded (𝕜) [semi_normed_ring 𝕜] [has_scalar 𝕜 E]
  [topological_space E] [has_zero E] (B : set E) : Prop :=
∀ V ∈ 𝓝 (0 : E), absorbs 𝕜 B V-/

section semi_normed_ring

variables (𝕜)
variables [semi_normed_ring 𝕜] [add_comm_group E] [module 𝕜 E]
variables [topological_space E] [topological_add_group E]
--variables (s : set E)

def is_bounded (B : set E) : Prop := ∀ V ∈ 𝓝 (0 : E), absorbs 𝕜 V B

variables (E)

@[simp] lemma is_bounded_empty : is_bounded 𝕜 (∅ : set E) :=
λ _ _, absorbs_empty

variables {𝕜 E}

lemma is_bounded_iff (B : set E) : is_bounded 𝕜 B ↔ ∀ V ∈ 𝓝 (0 : E), absorbs 𝕜 V B := iff.rfl

lemma is_bounded_subset {B s : set E} (hB : is_bounded 𝕜 B) (hs : s ⊆ B) : is_bounded 𝕜 s :=
λ V hV, absorbs.mono_right (hB V hV) hs

lemma is_bounded_union {B₁ B₂ : set E} (hB₁ : is_bounded 𝕜 B₁) (hB₂ : is_bounded 𝕜 B₂):
is_bounded 𝕜 (B₁ ∪ B₂) :=
λ V hV, absorbs.union (hB₁ V hV) (hB₂ V hV)

end semi_normed_ring

section normed_field

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [topological_space E] [topological_add_group E] [has_continuous_smul 𝕜 E]

lemma is_bounded_singleton (x : E) : is_bounded 𝕜 ({x} : set E) :=
λ V hV, absorbent.absorbs (absorbent_nhds_zero hV)

def bounded_bornology : bornology E :=
bornology.of_bounded (set_of (is_bounded 𝕜)) (is_bounded_empty 𝕜 E)
  (λ _ hB _, is_bounded_subset hB)
  (λ _ hB _, is_bounded_union hB)
  (set.eq_univ_iff_forall.mpr (λ x, set.mem_sUnion.mpr
    ⟨{x}, is_bounded_singleton _, set.mem_singleton _⟩))


-- Todo:
-- finer topology has same bounded sets
-- suffices for V in a basis
-- can assume that V is balanced
-- totally bounded implies bounded


end normed_field
