import topology.maps
import topology.opens
import topology.metric_space.basic

open topological_space

variables {α β : Type*} [topological_space α] [topological_space β] (f : α → β)
variables {s : set β} {ι : Type*} (U : ι → opens β) (hU : supr U = ⊤)

-- change this name (`set.restrict` and `set.cod_restrict` are taken)
def set.res {α β : Type*} (s : set β) (f : α → β) : f ⁻¹' s → s :=
(set.maps_to_preimage f s).restrict _ _ _

lemma continuous_at_res (s : opens β) (x : f ⁻¹' s)
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

lemma set.range_subtype_map {α β : Type*} (f : α → β) {p : set α} {q : set β} (H : ∀ x, p x → q (f x)) :
  set.range (subtype.map f H) = coe ⁻¹' (f '' p) :=
begin
  ext ⟨x, hx⟩,
  simp only [set.mem_preimage, set.mem_range, set.mem_image, subtype.exists, subtype.map,
    subtype.coe_mk],
  congr' 2,
  ext y,
  simp only [exists_prop, and.congr_left_iff],
  exact λ _, iff.rfl,
end

lemma set.range_res {α β : Type*} (s : set β) (f : α → β) :
  set.range (s.res f) = coe ⁻¹' (set.range f) :=
begin
  delta set.res set.maps_to.restrict,
  rw [@set.range_subtype_map _ _ _ (f ⁻¹' s) s, set.image_preimage_eq_inter_range,
    set.preimage_inter, subtype.coe_preimage_self, set.univ_inter],
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

-- This is incorrect. This (should) still holds if `f ⁻¹' U i` are open though. Do we need this?
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

attribute [mk_iff] embedding open_embedding closed_embedding

lemma embedding_iff_embedding_res_of_supr_eq_top (h : continuous f) :
  embedding f ↔ ∀ i, embedding ((U i).1.res f) :=
begin
  simp_rw embedding_iff,
  rw forall_and_distrib,
  apply and_congr,
  { apply inducing_iff_inducing_res_of_supr_eq_top; assumption },
  { apply injective_iff_injective_res_of_supr_eq_top; assumption }
end

lemma Union_inter_eq_of_supr_eq_top (s : set β) :
  (⋃ (i : ι), s ∩ U i) = s :=
begin
  rw ← set.inter_Union,
  convert s.inter_univ,
  convert congr_arg coe hU,
  simp,
end

lemma open_iff_inter_of_supr_eq_top (s : set β) :
  is_open s ↔ ∀ i, is_open (s ∩ U i) :=
begin
  split,
  { exact λ H i, H.inter (U i).2 },
  { intro H, rw ← Union_inter_eq_of_supr_eq_top U hU s, exact is_open_Union H }
end

lemma open_iff_coe_preimage_of_supr_eq_top (s : set β) :
  is_open s ↔ ∀ i, is_open (coe ⁻¹' s : set (U i)) :=
begin
  simp_rw [(U _).2.open_embedding_subtype_coe.open_iff_image_open,
    set.image_preimage_eq_inter_range, subtype.range_coe],
  apply open_iff_inter_of_supr_eq_top,
  assumption
end

lemma closed_iff_coe_preimage_of_supr_eq_top (s : set β) :
  is_closed s ↔ ∀ i, is_closed (coe ⁻¹' s : set (U i)) :=
begin
  let t := sᶜ, have : s = tᶜ := by simp[t], clear_value t, subst this,
  simpa using open_iff_coe_preimage_of_supr_eq_top _ hU t,
end

lemma open_embedding_iff_open_embedding_res_of_supr_eq_top (h : continuous f) :
  open_embedding f ↔ ∀ i, open_embedding ((U i).1.res f) :=
begin
  simp_rw open_embedding_iff,
  rw forall_and_distrib,
  apply and_congr,
  { apply embedding_iff_embedding_res_of_supr_eq_top; assumption },
  { simp_rw set.range_res, apply open_iff_coe_preimage_of_supr_eq_top U hU }
end

lemma closed_embedding_iff_closed_embedding_res_of_supr_eq_top (h : continuous f) :
  closed_embedding f ↔ ∀ i, closed_embedding ((U i).1.res f) :=
begin
  simp_rw closed_embedding_iff,
  rw forall_and_distrib,
  apply and_congr,
  { apply embedding_iff_embedding_res_of_supr_eq_top; assumption },
  { simp_rw set.range_res, apply closed_iff_coe_preimage_of_supr_eq_top U hU }
end
