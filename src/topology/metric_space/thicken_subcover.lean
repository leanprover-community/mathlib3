import topology.metric_space.shrinking_lemma
import topology.partition_of_unity
import topology.metric_space.hausdorff_distance

/-!
-/

open_locale topological_space ennreal big_operators nnreal
open set function filter topological_space emetric

lemma exists_continuous_forall_eball_subset {ι X : Type*} [emetric_space X]
  {K : ι → set X} {U : ι → set X} (hK : ∀ i, is_closed (K i)) (hU : ∀ i, is_open (U i))
  (hKU : ∀ i, K i ⊆ U i) (hfin : locally_finite K) :
  ∃ δ : X → ℝ≥0∞, continuous δ ∧ (∀ x, 0 < δ x) ∧ ∀ i (x ∈ K i), closed_ball x (δ x) ⊆ U i :=
begin
  have hK' : is_closed (⋃ i, K i), from hfin.is_closed_Union hK,
  have hKU' : (⋃ i, K i) ⊆ ⋃ i, U i, from Union_mono hKU,
  rcases partition_of_unity.exists_is_subordinate hK' U hU hKU' with ⟨f, hf⟩,
  set δ : X → ℝ≥0∞ := λ x, inf_edist x (⋃ i, K i) +
    (∑ᶠ i : ι, ennreal.of_real (f i x) * inf_edist x (U i)ᶜ) / 2,
  have hδfin : locally_finite (λ i, support (λ x, ennreal.of_real (f i x) * inf_edist x (U i)ᶜ)),
  { refine f.locally_finite.subset (λ i x, mt _), intro hx,
    simp [hx] },
  refine ⟨δ, _, λ x, _, λ i x hx, _⟩,
  { refine continuous_inf_edist.add ((ennreal.continuous_div_const _ ennreal.two_ne_zero).comp
      (continuous_finsum (λ i, _) hδfin)),
    refine (ennreal.continuous_of_real.comp _).ennreal_mul continuous_inf_edist _ _,
    -- refine continuous_iff_continuous_at.2 (λ x, ennreal.tendsto.mul _ _
      -- continuous_inf_edist.continuous_at (or.inr ennreal.of_real_ne_top)),
    
 },
  { rw [add_pos_iff],
    by_cases hx : x ∈ ⋃ i, K i,
    { refine or.inr (ennreal.half_pos _),
      
 } },
end
