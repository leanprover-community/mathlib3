import topology.metric_space.metrizable_uniformity
import analysis.normed.group.quotient

open topological_space filter set
open_locale topological_space uniformity

universe u

lemma filter.map.is_countably_generated {α β : Type*} (l : filter α) [H : l.is_countably_generated]
  (f : α → β) : (map f l).is_countably_generated :=
begin
  unfreezingI {rw is_countably_generated_iff_exists_antitone_basis at *; rcases H with ⟨u, hu⟩},
  exact ⟨_, hu.map⟩,
end

@[to_additive]
lemma quotient_group.nhds_eq {G : Type*} [group G] [topological_space G] [topological_group G]
  (N : subgroup G) (x : G) : 𝓝 (x : G ⧸ N) = map coe (𝓝 x) :=
le_antisymm ((quotient_group.is_open_map_coe N).nhds_le x) continuous_quot_mk.continuous_at

@[to_additive]
instance quotient_group.nhds_one_is_countably_generated {G : Type*} [group G] [topological_space G]
  [first_countable_topology G] [topological_group G] (N : subgroup G) [N.normal]
  [is_closed (N : set G)] : (𝓝 (1 : G ⧸ N)).is_countably_generated :=
(quotient_group.nhds_eq N 1).symm ▸ filter.map.is_countably_generated _ _

@[to_additive]
instance quotient_group.uniformity_is_countably_generated {G : Type*} [group G] [topological_space G]
  [first_countable_topology G] [topological_group G] (N : subgroup G) [N.normal]
  [is_closed (N : set G)] :
  (@uniformity (G ⧸ N) (topological_group.to_uniform_space (G ⧸ N))).is_countably_generated :=
comap.is_countably_generated _ _

@[to_additive]
instance quotient_group.metrizable {G : Type*} [group G] [topological_space G]
  [first_countable_topology G] [topological_group G] {N : subgroup G} [N.normal]
  [is_closed (N : set G)] : metrizable_space (G ⧸ N) :=
@uniform_space.metrizable_space (G ⧸ N) (topological_group.to_uniform_space (G ⧸ N)) _ _

open_locale pointwise


open classical

@[to_additive]
lemma filter.has_antitone_basis.nhds_one_inv {G : Type*} [topological_space G] [group G]
  [topological_group G] {ι : Sort*} [semilattice_sup ι] {u : ι → set G}
  (hu : (𝓝 1).has_antitone_basis u) : (𝓝 1).has_antitone_basis (λ n, u n ∪ (u n)⁻¹) :=
begin
  have := @filter.has_antitone_basis.map _ _ _ _ _ _ (λ g, g⁻¹) hu,
  have inv_open : is_open_map (λ g : G, g⁻¹),
    from is_open_map.of_inverse continuous_inv inv_inv inv_inv,
  have map_inv_nhds_one : map (λ g, g⁻¹) (𝓝 (1 : G)) = 𝓝 1, from le_antisymm
    (by simpa only [inv_one] using continuous_inv.tendsto (1 : G))
    (by simpa only [inv_one] using inv_open.nhds_le (1 : G)),
  simp only [map_inv_nhds_one, image_inv] at this,
  refine ⟨⟨λ t, ⟨_, _⟩⟩, _⟩,
  { intros ht,
    rcases hu.to_has_basis.mem_iff.mp ht with ⟨k, ⟨⟩, hk⟩,
    rcases this.to_has_basis.mem_iff.mp ht with ⟨j, ⟨⟩, hj⟩,
    exact ⟨k ⊔ j, true.intro, union_subset ((hu.antitone le_sup_left).trans hk)
      ((this.antitone le_sup_right).trans hj)⟩, },
  { rintro ⟨i, -, hi⟩,
    refine (𝓝 (1 : G)).sets_of_superset (hu.to_has_basis.mem_of_mem true.intro : u i ∈ 𝓝 1)
      ((subset_union_left _ _).trans hi), },
  { exact λ n m hnm, union_subset_union (hu.antitone hnm) (this.antitone hnm)},
  --{ intros n, simp only [union_comm, union_inv, inv_inv]}
end

@[to_additive]
lemma topological_group.exists_antitone_basis_nhds_one (G : Type u) [topological_space G] [group G]
  [topological_group G] [h1 : (𝓝 (1 : G)).is_countably_generated] : ∃ (x : ℕ → set G),
  (𝓝 1).has_antitone_basis x ∧ (∀ n, x (n + 1) * x (n + 1) ⊆ x n) ∧ (∀ n, (x n)⁻¹ = x n) :=
begin
  rcases is_countably_generated_iff_exists_antitone_basis.mp h1 with ⟨v, hv⟩,
  set u := λ n, v n ∪ (v n)⁻¹,
  obtain ⟨(hu : (𝓝 (1 : G)).has_basis (λ _, true) u), (u_anti : antitone u)⟩ := hv.nhds_one_inv,
  have := continuous_mul.tendsto ((1, 1) : G × G),
  simp at this,
  rw (hu.prod_nhds hu).tendsto_iff hu at this,
  simp only [and_self, mem_prod, and_imp, prod.forall, exists_true_left, prod.exists,
    forall_true_left] at this,
  have key : ∀ n : ℕ, ∃ m, n < m ∧ u m * u m ⊆ u n,
  { intros n,
    rcases this n with ⟨j, k, h⟩,
    refine ⟨max n (max j k) + 1, (le_max_left _ _).trans_lt (lt_add_one _), _⟩,
    have h' : u j * u k ⊆ u n, { rintro - ⟨a, b, ha, hb, rfl⟩, exact h a b ha hb, },
    refine (set.mul_subset_mul (u_anti _) (u_anti _)).trans h',
    exact (((le_max_left j k).trans $ le_max_right n (max j k)).trans $ (lt_add_one _).le),
    exact (((le_max_right j k).trans $ le_max_right n (max j k)).trans $ (lt_add_one _).le) },
  set y : ℕ → ℕ := λ (n : ℕ), nat.rec_on n 0 (λ k yk, (classical.some (key yk))),
  have hy : ∀ n : ℕ, y n < y (n + 1) ∧ u (y (n + 1)) * u (y (n + 1)) ⊆ u (y n),
    from λ n, classical.some_spec (key $ y n),
  have y_mono : strict_mono y := strict_mono_nat_of_lt_succ (λ n, (hy n).1),
  refine ⟨u ∘ y, (has_antitone_basis.comp_mono ⟨hu, u_anti⟩) y_mono.monotone y_mono.tendsto_at_top,
    λ n, (hy n).2, λ n, by simp only [union_comm, union_inv, inv_inv]⟩,
end

@[to_additive]
instance quotient_group.complete (G : Type u) [group G] [pseudo_metric_space G]
  [uniform_group G] [complete_space G] (N : subgroup G) [N.normal] [is_closed (N : set G)] :
  @complete_space (G ⧸ N) (topological_group.to_uniform_space (G ⧸ N)) :=
begin
  letI : uniform_space (G ⧸ N) := topological_group.to_uniform_space (G ⧸ N),
  haveI : (uniformity (G ⧸ N)).is_countably_generated := comap.is_countably_generated _ _,
  obtain ⟨U, ⟨hU, U_anti⟩, U_mul, U_inv⟩ := topological_group.exists_antitone_basis_nhds_one G,
  obtain ⟨hV, V_anti⟩ := @has_antitone_basis.map _ _ _ _ _ _ (coe : G → G ⧸ N) ⟨hU, U_anti⟩,
  rw [←quotient_group.nhds_eq N 1, quotient_group.coe_one] at hV,
  refine uniform_space.complete_of_cauchy_seq_tendsto (λ x hx, _),
  have foo : tendsto _ _ (𝓝 (1 : G ⧸ N)) := map_le_iff_le_comap.mpr hx.2,
  simp only [prod_map_map_eq, hV.tendsto_right_iff, eventually_map, forall_true_left,
    (at_top_basis.prod at_top_basis).eventually_iff, mem_image, Ici_prod_Ici, mem_Ici, prod.forall,
    true_and, prod.exists, prod.mk_le_mk, and_imp] at foo,
  have foo₁ : ∀ i j : ℕ, ∃ M : ℕ,
    j < M ∧ ∀ a b : ℕ, M ≤ a → M ≤ b → ∀ g : G, x b = g → ∃ g' : G, g / g' ∈ U i ∧ x a = g',
  { intros i j,
    rcases foo i with ⟨M₁, M₂, hM⟩,
    refine ⟨max j (max M₁ M₂) + 1, (le_max_left _ _).trans_lt (lt_add_one _), λ a b ha hb g hg, _⟩,
    obtain ⟨y, y_mem, hy⟩ := hM a b
      (((le_max_left _ _).trans $ (le_max_right j _).trans (lt_add_one _).le).trans ha)
      (((le_max_right _ _).trans $ (le_max_right j _).trans (lt_add_one _).le).trans hb),
    refine ⟨y⁻¹ * g,
      by simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left] using y_mem, _⟩,
    rw [quotient_group.coe_mul, quotient_group.coe_inv, hy, hg, inv_div, div_mul_cancel'], },

  set φ : ℕ → ℕ := λ n, nat.rec_on n (some $ foo₁ 0 0) (λ k yk, some $ foo₁ (k + 1) yk),
  have hφ : ∀ n : ℕ, φ n < φ (n + 1) ∧ ∀ a b : ℕ, φ (n + 1) ≤ a → φ (n + 1) ≤ b → ∀ g : G, x b = g → ∃ g' : G, g / g' ∈ U (n + 1) ∧ x a = g',
    from λ n, some_spec (foo₁ (n + 1) (φ n)),
  set x' : Π n, psigma (λ g : G, x (φ (n + 1)) = g) :=
    λ n, nat.rec_on n
      ⟨some (quotient_group.mk_surjective (x (φ 1))),
       (some_spec (quotient_group.mk_surjective (x (φ 1)))).symm⟩
      (λ k hk, ⟨some $ (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd,
          (some_spec $ (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd).2⟩),
  have hx' : ∀ n : ℕ, (x' n).fst / (x' (n + 1)).fst ∈ U (n + 1) :=
    λ n, (some_spec $ (hφ n).2 _ _ (hφ (n + 1)).1.le le_rfl (x' n).fst (x' n).snd).1,
  have x'_cauchy : cauchy_seq (λ n, (x' n).fst),
  { refine ⟨by simpa only [map_ne_bot_iff] using at_top_ne_bot, _⟩,
    simp only [uniformity_eq_comap_nhds_one, ←tendsto_iff_comap, prod_map_map_eq, prod.mk_le_mk,
      hU.tendsto_right_iff, eventually_map, forall_true_left, mem_Ici, prod.forall, prod.exists,
      (at_top_basis.prod at_top_basis).eventually_iff, mem_image, Ici_prod_Ici, true_and, and_imp],
    have key : ∀ m n, m ≤ n → (x' m).fst / (x' n).fst ∈ U m,
      from λ m n hmn, nat.decreasing_induction'
        (λ k hkn hkm hk, U_mul k ⟨_, _, hx' k, hk, div_mul_div_cancel' _ _ _⟩)
        hmn (by simpa only [div_self'] using mem_of_mem_nhds (hU.mem_of_mem true.intro)),
    refine λ n, ⟨n, n, λ j k hj hk, _⟩,
    rcases le_total j k with (hjk | hjk),
    { refine U_anti hj _,
      rw ←U_inv j,
      simpa only [set.mem_inv, inv_div] using key _ _ hjk, },
    { exact U_anti hk (key _ _ hjk) } },
  rcases cauchy_seq_tendsto_of_complete x'_cauchy with ⟨x₀, hx₀⟩,
  refine ⟨↑x₀, tendsto_nhds_of_cauchy_seq_of_subseq hx
    (strict_mono_nat_of_lt_succ $ λ n, (hφ (n + 1)).1).tendsto_at_top _⟩,
  convert ((continuous_coinduced_rng : continuous (coe : G → G ⧸ N)).tendsto x₀).comp hx₀,
  exact funext (λ n, (x' n).snd),
end

.


theorem it_works {G : Type u} [seminormed_add_comm_group G] [complete_space G] (N : add_subgroup G)
  [is_closed (N : set G)] : complete_space (G ⧸ N) :=
infer_instance

.
