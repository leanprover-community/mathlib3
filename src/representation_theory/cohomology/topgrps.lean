import topology.algebra.open_subgroup
import topology.discrete_quotient
import group_theory.index
variables {G : Type*} [group G] [topological_space G] [topological_group G] (U : subgroup G)

open_locale classical

lemma quotient_group.is_open_map_coe' : is_open_map (coe : G → G ⧸ U) :=
begin
  intros s s_op,
  change is_open ((coe : G → G ⧸ U) ⁻¹' (coe '' s)),
  rw quotient_group.preimage_image_coe U s,
  exact is_open_Union (λ n, (continuous_mul_right _).is_open_preimage s s_op)
end

lemma discrete_quotient_of_open_subgroup (hU : is_open (U : set G)) :
  discrete_topology (G ⧸ U) :=
⟨eq_bot_of_singletons_open (λ x,
begin
  induction x using quotient_group.induction_on',
  rw ←set.image_preimage_eq {↑x} quotient_group.mk_surjective,
  refine quotient_group.is_open_map_coe' U _ _,
  show is_open { y : G | @coe G (G ⧸ U) _ y = @coe G (G ⧸ U) _ x},
  rw quotient_group.eq_class_eq_left_coset U,
  exact is_open.left_coset hU _,
end)⟩

lemma set_of_left_rel (H : subgroup G) (g : G) :
  set_of ((quotient_group.left_rel H).rel g) = left_coset g H :=
begin
  ext,
  dsimp,
  refine iff.trans quotient_group.left_rel_apply _,
  unfold left_coset,
  rw set.image_mul_left,
  refl,
end

@[simps] def open_subgroup.to_discrete_quotient (H : open_subgroup G) : discrete_quotient G :=
{ rel := (quotient_group.left_rel (H : subgroup G)).rel,
  equiv := (quotient_group.left_rel (H : subgroup G)).iseqv,
  clopen :=
  begin
    intro g,
    rw set_of_left_rel,
    exact ⟨is_open.left_coset H.2 _, is_closed.left_coset H.is_closed _⟩,
  end, }

noncomputable instance open_subgroup.quotient_fintype [compact_space G] (U : open_subgroup G) :
  fintype (G ⧸ (U : subgroup G)) :=
discrete_quotient.fintype U.to_discrete_quotient

lemma eq_one_iff {N : subgroup G} (x : G) : (x : G ⧸ N) = (1 : G) ↔ x ∈ N :=
begin
  refine quotient_group.eq.trans _,
  rw [mul_one, subgroup.inv_mem_iff],
end

theorem is_open_of_is_closed_fintype (hU : is_closed (U : set G)) [fintype (G ⧸ U)] :
  is_open (U : set G) :=
begin
  have h1 : @quotient_group.mk G _ U ⁻¹' {(1 : G)} = U := by ext; exact eq_one_iff _,
  have : (U : set G) = (⋃ (i ∈ ({i | i ≠ (1 : G)} : set (G ⧸ U))),
    @quotient_group.mk G _ U ⁻¹' {i})ᶜ,
  begin
    rw eq_compl_iff_is_compl,
    split,
    { rw [←set.preimage_Union₂, ←h1],
      refine disjoint.preimage _ _,
      simp },
    { show set.univ ≤ _ ∪ _,
      rw [set.le_eq_subset, set.univ_subset_iff, ←h1, ←set.preimage_Union₂, ←set.preimage_union],
      convert set.preimage_univ,
      rw [set.bUnion_of_singleton, ←set.univ_subset_iff],
      intros x hx,
      exact classical.em _ }
  end,
  rw [←is_closed_compl_iff, this, compl_compl],
  refine is_closed_bUnion _ _,
  { constructor,
    apply_instance },
  { intros q hq,
    induction q using quotient_group.induction_on',
    show is_closed ({ x | @coe G (G ⧸ U) _ x = @coe G (G ⧸ U) _ q }),
    rw quotient_group.eq_class_eq_left_coset,
    exact is_closed.left_coset hU _ }
end

lemma is_open_iff_is_closed_and_nonempty_fintype [hG : compact_space G]
  (U : subgroup G) : is_open (U : set G) ↔ is_closed (U : set G) ∧ nonempty (fintype (G ⧸ U)) :=
⟨λ hU, ⟨open_subgroup.is_closed ⟨U, hU⟩, ⟨open_subgroup.quotient_fintype ⟨U, hU⟩⟩⟩,
λ ⟨hU, ⟨hf⟩⟩, by unfreezingI { exact is_open_of_is_closed_fintype U hU }⟩
