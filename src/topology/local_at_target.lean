import topology.maps
import topology.opens
import topology.metric_space.basic

open topological_space

variables {α β : Type*} [topological_space α] [topological_space β] (f : α → β)
variables {s : set β} {ι : Type*} (U : ι → opens β) (hU : supr U = ⊤)

-- change this name (`set.restrict` and `set.cod_restrict` are taken)
def set.res {α β : Type*} (s : set β) (f : α → β) : f ⁻¹' s → s :=
(set.maps_to_preimage f s).restrict _ _ _

lemma continuous_at_iff_continuous_at_res (s : opens β) (x : f ⁻¹' s)
  (h : continuous_at f x) : continuous_at (s.1.res f) x :=
begin
  intros U hU,
  obtain ⟨_, e, ⟨V, hV, rfl⟩, hx⟩ := mem_nhds_iff.mp hU,
  have := h (is_open.mem_nhds hV hx),
  rw [filter.mem_map, mem_nhds_iff] at this ⊢,
  obtain ⟨W, e', hW, hx'⟩ := this,
  use coe ⁻¹' W,
  refine ⟨_, continuous_subtype_coe.1 _ hW, hx'⟩,
  intros y hy,
  apply e,
  exact e' hy
end

lemma map_nhds_of_open_embedding {f : α → β} (hf : open_embedding f) (a : α) :
  filter.map f (nhds a) = nhds (f a) :=
begin
  convert map_nhds_induced_of_mem _,
  { exact hf.to_inducing.1 },
  { exact hf.open_range.mem_nhds (set.mem_range_self a) }
end

include hU

-- this hold in arbitrary sets
lemma injective_iff_injective_res_of_supr_eq_top :
  function.injective f ↔ ∀ i, function.injective ((U i).1.res f) :=
begin
  split,
  { intros H i x y e, injection e with e, exact subtype.coe_injective (H e) },
  { intros H x y e,
    obtain ⟨i, hi⟩ := opens.mem_supr.mp (show f x ∈ supr U, by { rw hU, triv }),
    injection @H i ⟨x, hi⟩ ⟨y, show f y ∈ U i, from e ▸ hi⟩ (subtype.ext e) }
end

-- this hold in arbitrary sets
lemma surjective_iff_surjective_res_of_supr_eq_top :
  function.surjective f ↔ ∀ i, function.surjective ((U i).1.res f) :=
begin
  split,
  { exact λ H i x, ⟨⟨_, (show f (H x).some ∈ U i,
      from (H x).some_spec.symm ▸ x.2)⟩, subtype.ext (H x).some_spec⟩ },
  { intros H x,
    obtain ⟨i, hi⟩ := opens.mem_supr.mp (show x ∈ supr U, by { rw hU, triv }),
    exact ⟨_, congr_arg subtype.val (H i ⟨x, hi⟩).some_spec⟩ }
end

-- this hold in arbitrary sets
lemma bijective_iff_bijective_res_of_supr_eq_top :
  function.bijective f ↔ ∀ i, function.bijective ((U i).1.res f) :=
begin
  delta function.bijective,
  rw forall_and_distrib,
  apply and_congr,
  exacts [injective_iff_injective_res_of_supr_eq_top f U hU,
    surjective_iff_surjective_res_of_supr_eq_top f U hU]
end

-- This is probably incorrect
lemma continuous_iff_continuous_res_of_supr_eq_top :
  continuous f ↔ ∀ i, continuous ((U i).1.res f) := sorry

lemma inducing_iff_inducing_res_of_supr_eq_top (h : continuous f) :
  inducing f ↔ ∀ i, inducing ((U i).1.res f) :=
begin
  split,
  { intros H i, constructor, ext U, split,
    { rintro ⟨V, hV, rfl⟩,
      obtain ⟨s, hs, rfl⟩ := H.is_open_iff.mp hV,
      exact ⟨_, ⟨s, hs, rfl⟩, rfl⟩ },
    { rintro ⟨_, ⟨V, hV, rfl⟩, rfl⟩,
      exact ⟨_, H.is_open_iff.mpr ⟨_, hV, rfl⟩, rfl⟩ } },
  { intros H, constructor,
    rw induced_iff_nhds_eq,
    intro x,
    obtain ⟨i, hi⟩ := opens.mem_supr.mp (show f x ∈ supr U, by { rw hU, triv }),
    erw ← map_nhds_of_open_embedding (h.1 _ (U i).2).open_embedding_subtype_coe ⟨x, hi⟩,
    rw (induced_iff_nhds_eq _).mp (H i).1 ⟨x, hi⟩,
    erw (induced_iff_nhds_eq (coe : (U i).1 → β)).mp embedding_subtype_coe.to_inducing.1 ⟨_, hi⟩,
    rw [filter.comap_comap, (show coe ∘ (U i).val.res f = f ∘ coe, from rfl), subtype.coe_mk,
      ← filter.comap_comap, filter.subtype_coe_map_comap, inf_eq_left],
    intros S hS,
    rw filter.mem_comap,
    exact ⟨U i, (U i).2.mem_nhds hi, hS⟩ }
end

-- lemma bijective_iff_bijective_res_of_supr_eq_top :
--   function.bijective f ↔ ∀ i, function.bijective ((U i).1.res f) := sorry
-- lemma bijective_iff_bijective_res_of_supr_eq_top :
--   function.bijective f ↔ ∀ i, function.bijective ((U i).1.res f) := sorry
