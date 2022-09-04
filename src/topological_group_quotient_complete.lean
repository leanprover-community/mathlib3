import topology.metric_space.metrizable_uniformity

open topological_space filter set classical
open_locale topological_space uniformity pointwise

universes u v

/- The map of a countably generated filter is countably generated -/
lemma filter.map.is_countably_generated {α β : Type*} (l : filter α) [H : l.is_countably_generated]
  (f : α → β) : (map f l).is_countably_generated :=
begin
  unfreezingI {rw is_countably_generated_iff_exists_antitone_basis at *; rcases H with ⟨u, hu⟩},
  exact ⟨_, hu.map⟩,
end

/- Neighborhoods in the quotient are precisely the map of neighborhoods in prequotient. -/
@[to_additive]
lemma quotient_group.nhds_eq {G : Type u} [group G] [topological_space G] [topological_group G]
  (N : subgroup G) (x : G) : 𝓝 (x : G ⧸ N) = map coe (𝓝 x) :=
le_antisymm ((quotient_group.is_open_map_coe N).nhds_le x) continuous_quot_mk.continuous_at

/- In a first countable topological group `G` with normal subgroup `N`, `1 : G ⧸ N` has a
countable neighborhood basis. -/
@[to_additive]
instance quotient_group.nhds_one_is_countably_generated {G : Type u} [group G] [topological_space G]
  [first_countable_topology G] [topological_group G] (N : subgroup G) [N.normal] :
  (𝓝 (1 : G ⧸ N)).is_countably_generated :=
(quotient_group.nhds_eq N 1).symm ▸ filter.map.is_countably_generated _ _

/- In a first countable topological group `G` with normal subgroup `N`, `𝓤 (G ⧸ N)` is countably
generated. -/
@[to_additive]
instance quotient_group.uniformity_is_countably_generated {G : Type u} [group G]
  [topological_space G] [first_countable_topology G] [topological_group G] (N : subgroup G)
  [N.normal] [is_closed (N : set G)] :
  (@uniformity (G ⧸ N) (topological_group.to_uniform_space (G ⧸ N))).is_countably_generated :=
comap.is_countably_generated _ _

/- If `u : ι → set G` is an antitone neighborhood basis for `1 : G`, so is `λ i, u i ∪ (u i)⁻¹`. -/
@[to_additive]
lemma filter.has_antitone_basis.nhds_one_inv {G : Type*} [topological_space G] [group G]
  [topological_group G] {ι : Sort*} [semilattice_sup ι] {u : ι → set G}
  (hu : (𝓝 1).has_antitone_basis u) : (𝓝 1).has_antitone_basis (λ n, u n ∪ (u n)⁻¹) :=
begin
  have hu' := @filter.has_antitone_basis.map _ _ _ _ _ _ (λ g, g⁻¹) hu,
  have map_inv_nhds_one : map (λ g, g⁻¹) (𝓝 (1 : G)) = 𝓝 1,
  { simpa only [inv_one] using le_antisymm (continuous_inv.tendsto (1 : G))
    ((is_open_map.of_inverse continuous_inv inv_inv inv_inv).nhds_le (1 : G)) },
  simp only [map_inv_nhds_one, image_inv] at hu',
  refine ⟨⟨λ t, ⟨λ ht, _, _⟩⟩, _⟩,
  { rcases hu.to_has_basis.mem_iff.mp ht with ⟨k, ⟨⟩, hk⟩,
    rcases hu'.to_has_basis.mem_iff.mp ht with ⟨j, ⟨⟩, hj⟩,
    exact ⟨k ⊔ j, true.intro, union_subset ((hu.antitone le_sup_left).trans hk)
      ((hu'.antitone le_sup_right).trans hj)⟩, },
  { rintro ⟨i, -, hi⟩,
    exact (𝓝 (1 : G)).sets_of_superset (hu.to_has_basis.mem_of_mem true.intro : u i ∈ 𝓝 1)
      ((subset_union_left _ _).trans hi), },
  { exact λ n m hnm, union_subset_union (hu.antitone hnm) (hu'.antitone hnm)},
end

/- Any first countable topological group has an antitone neighborhood basis `u : ℕ → set G` for
which `(u n)⁻¹ = u n` and `(u (n + 1)) ^ 2 ⊆ u n`. The existence of such a neighborhood basis is
a key tool for `quotient_group.complete_space` -/
@[to_additive]
lemma topological_group.exists_antitone_basis_nhds_one (G : Type u) [topological_space G] [group G]
  [topological_group G] [first_countable_topology G] : ∃ (u : ℕ → set G),
  (𝓝 1).has_antitone_basis u ∧ (∀ n, u (n + 1) * u (n + 1) ⊆ u n) ∧ (∀ n, (u n)⁻¹ = u n) :=
begin
  rcases is_countably_generated_iff_exists_antitone_basis.mp
    (first_countable_topology.nhds_generated_countable (1 : G)) with ⟨v, hv⟩,
  set u := λ n, v n ∪ (v n)⁻¹,
  obtain ⟨(hu : (𝓝 (1 : G)).has_basis (λ _, true) u), (u_anti : antitone u)⟩ := hv.nhds_one_inv,
  have := ((hu.prod_nhds hu).tendsto_iff hu).mp
    (by simpa only [mul_one] using continuous_mul.tendsto ((1, 1) : G × G)),
  simp only [and_self, mem_prod, and_imp, prod.forall, exists_true_left, prod.exists,
    forall_true_left] at this,
  have exists_mul : ∀ n : ℕ, ∃ m, n < m ∧ u m * u m ⊆ u n,
  { intros n,
    rcases this n with ⟨j, k, h⟩,
    refine ⟨max n (max j k) + 1, (le_max_left _ _).trans_lt (lt_add_one _), _⟩,
    have h' : u j * u k ⊆ u n, { rintro - ⟨a, b, ha, hb, rfl⟩, exact h a b ha hb, },
    refine (set.mul_subset_mul (u_anti _) (u_anti _)).trans h',
    exact (((le_max_left j k).trans $ le_max_right n (max j k)).trans $ (lt_add_one _).le),
    exact (((le_max_right j k).trans $ le_max_right n (max j k)).trans $ (lt_add_one _).le) },
  set y : ℕ → ℕ := λ (n : ℕ), nat.rec_on n 0 (λ k yk, (some (exists_mul yk))),
  have hy : ∀ n : ℕ, y n < y (n + 1) ∧ u (y (n + 1)) * u (y (n + 1)) ⊆ u (y n),
    from λ n, some_spec (exists_mul $ y n),
  have y_mono : strict_mono y := strict_mono_nat_of_lt_succ (λ n, (hy n).1),
  exact ⟨u ∘ y, (has_antitone_basis.comp_mono ⟨hu, u_anti⟩) y_mono.monotone y_mono.tendsto_at_top,
    λ n, (hy n).2, λ n, by simp only [union_comm, union_inv, inv_inv]⟩,
end

/- The quotient `G ⧸ N` of a complete uniform topological group `G` which is also first countable
by a closed normal subgroup is itself complete. Consequently, quotients of Banach spaces by closed
subspaces are complete. -/
@[to_additive]
instance quotient_group.complete_space (G : Type u) [group G] [uniform_space G] [uniform_group G]
  [first_countable_topology G] [complete_space G] (N : subgroup G) [N.normal]
  [is_closed (N : set G)] : @complete_space (G ⧸ N) (topological_group.to_uniform_space (G ⧸ N)) :=
begin
  /- Since `G ⧸ N` is a topological group it is a uniform space, and since `G` is first countable
  the uniformities of both `G` and `G ⧸ N` are countably generated. Moreover, we may choose a
  sequential antitone neighborhood basis `u` for `𝓝 (1 : G)` so that `(u n)⁻¹ = u n` and also
  `(u (n + 1)) ^ 2 ⊆ u n`, and this descends to an antitone neighborhood basis `v` for
  `𝓝 (1 : G ⧸ N)`. -/
  letI : uniform_space (G ⧸ N) := topological_group.to_uniform_space (G ⧸ N),
  haveI : (𝓤 (G ⧸ N)).is_countably_generated := comap.is_countably_generated _ _,
  obtain ⟨U, ⟨hU, U_anti⟩, U_mul, U_inv⟩ := topological_group.exists_antitone_basis_nhds_one G,
  obtain ⟨hV, V_anti⟩ := @has_antitone_basis.map _ _ _ _ _ _ (coe : G → G ⧸ N) ⟨hU, U_anti⟩,
  rw [←quotient_group.nhds_eq N 1, quotient_group.coe_one] at hV,
  /- Since `G ⧸ N` is metrizable it suffices to show any Cauchy sequence `x` converges; note that
  `x` has quotients of successive terms converging to `1`. -/
  refine uniform_space.complete_of_cauchy_seq_tendsto (λ x hx, _),
  have x_div_tendsto : tendsto _ _ (𝓝 (1 : G ⧸ N)) := map_le_iff_le_comap.mpr hx.2,
  simp only [prod_map_map_eq, hV.tendsto_right_iff, eventually_map, forall_true_left,
    (at_top_basis.prod at_top_basis).eventually_iff, mem_image, Ici_prod_Ici, mem_Ici, prod.forall,
    true_and, prod.exists, prod.mk_le_mk, and_imp] at x_div_tendsto,
  /- Given `n : ℕ`, for sufficiently large `a b : ℕ`, given any lift of `x b`, we can find a lift
  of `x a` such that the quotient of the lifts lies in `u n`. -/
  have key₀ : ∀ i j : ℕ, ∃ M : ℕ,
    j < M ∧ ∀ a b : ℕ, M ≤ a → M ≤ b → ∀ g : G, x b = g → ∃ g' : G, g / g' ∈ U i ∧ x a = g',
  { intros i j,
    rcases x_div_tendsto i with ⟨M₁, M₂, hM⟩,
    refine ⟨max j (max M₁ M₂) + 1, (le_max_left _ _).trans_lt (lt_add_one _), λ a b ha hb g hg, _⟩,
    obtain ⟨y, y_mem, hy⟩ := hM a b
      (((le_max_left _ _).trans $ (le_max_right j _).trans (lt_add_one _).le).trans ha)
      (((le_max_right _ _).trans $ (le_max_right j _).trans (lt_add_one _).le).trans hb),
    refine ⟨y⁻¹ * g,
      by simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left] using y_mem, _⟩,
    rw [quotient_group.coe_mul, quotient_group.coe_inv, hy, hg, inv_div, div_mul_cancel'], },
  /- Inductively construct a subsequence `φ : ℕ → ℕ` using `key₀` so that if `a b : ℕ` exceed
  `φ (n + 1)`, then we may find lifts whose quotients lie within `u n`. -/
  set φ : ℕ → ℕ := λ n, nat.rec_on n (some $ key₀ 0 0) (λ k yk, some $ key₀ (k + 1) yk),
  have hφ : ∀ n : ℕ, φ n < φ (n + 1) ∧ ∀ a b : ℕ, φ (n + 1) ≤ a → φ (n + 1) ≤ b →
    (∀ g : G, x b = g → ∃ g' : G, g / g' ∈ U (n + 1) ∧ x a = g'),
    from λ n, some_spec (key₀ (n + 1) (φ n)),
  /- Inductively construct a sequence `x' n : G` of lifts of `x (φ (n + 1))` such that quotients of
  successive terms lie in `x' n / x' (n + 1) ∈ u (n + 1)`. We actually need the proofs that each
  term is a lift to construct the next term, so we use a Σ-type. -/
  set x' : Π n, psigma (λ g : G, x (φ (n + 1)) = g) :=
    λ n, nat.rec_on n
      ⟨some (quotient_group.mk_surjective (x (φ 1))),
       (some_spec (quotient_group.mk_surjective (x (φ 1)))).symm⟩
      (λ k hk, ⟨some $ (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd,
          (some_spec $ (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd).2⟩),
  have hx' : ∀ n : ℕ, (x' n).fst / (x' (n + 1)).fst ∈ U (n + 1) :=
    λ n, (some_spec $ (hφ n).2 _ _ (hφ (n + 1)).1.le le_rfl (x' n).fst (x' n).snd).1,
  /- The sequence `x'` is Cauchy. This is where we exploit the conditions on `u`. The key idea
  is to show by decreasing induction that `x' m / x' n ∈ u m` if `m ≤ n`. -/
  have x'_cauchy : cauchy_seq (λ n, (x' n).fst),
  { refine ⟨by simpa only [map_ne_bot_iff] using at_top_ne_bot, _⟩,
    simp only [uniformity_eq_comap_nhds_one, ←tendsto_iff_comap, prod_map_map_eq, prod.mk_le_mk,
      hU.tendsto_right_iff, eventually_map, forall_true_left, mem_Ici, prod.forall, prod.exists,
      (at_top_basis.prod at_top_basis).eventually_iff, mem_image, Ici_prod_Ici, true_and, and_imp],
    have key₁ : ∀ m n, m ≤ n → (x' m).fst / (x' n).fst ∈ U m,
      from λ m n hmn, nat.decreasing_induction'
        (λ k hkn hkm hk, U_mul k ⟨_, _, hx' k, hk, div_mul_div_cancel' _ _ _⟩)
        hmn (by simpa only [div_self'] using mem_of_mem_nhds (hU.mem_of_mem true.intro)),
    refine λ n, ⟨n, n, λ j k hj hk, _⟩,
    rcases le_total j k with (hjk | hjk),
    { refine U_anti hj _,
      rw ←U_inv j,
      simpa only [set.mem_inv, inv_div] using key₁ _ _ hjk, },
    { exact U_anti hk (key₁ _ _ hjk) } },
  /- Since `G` is complete, `x'` converges to some `x₀`, and so the image of this sequence under
  the quotient map converges to `↑x₀`. The image of `x'` is a convergent subsequence of `x`, and
  since `x` is Cauchy, this implies it converges. -/
  rcases cauchy_seq_tendsto_of_complete x'_cauchy with ⟨x₀, hx₀⟩,
  refine ⟨↑x₀, tendsto_nhds_of_cauchy_seq_of_subseq hx
    (strict_mono_nat_of_lt_succ $ λ n, (hφ (n + 1)).1).tendsto_at_top _⟩,
  convert ((continuous_coinduced_rng : continuous (coe : G → G ⧸ N)).tendsto x₀).comp hx₀,
  exact funext (λ n, (x' n).snd),
end
