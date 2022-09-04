/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import topology.algebra.uniform_group

/-!
# Quotient group of a metrizable topological group is complete

A standard fact in analysis is that the quotient of a Banach space by a closed subspace is a
Banach space. In this file, we provide a proof of the completeness portion of this theorem; the
linear and norm structure appears elsewhere in mathlib.

The proof that appears most frequently in textbooks proceeds as follows: suppose `X` is a Banach
space and `S` is a closed subspace, and let `x : ℕ → X ⧸ S` be a sequence such that the series
`∑ ∥x n∥ < ∞`. For each `n : ℕ` lift `x n` to some `x' n : X` so that `∥x' n∥ ≤ ∥x n∥ + 2 ^ (-n)`.
Then `∑ ∥x' n∥ ≤ (∑ ∥x n∥) + 1 < ∞` is an absolutely convergent series, and since `X` is complete,
the series `∑ (x' n)` converges. Then the series `∑ (x n)` converges in `X ⧸ S`. Therefore, every
absolutely convergent series in `X ⧸ S` converges, and hence `X ⧸ S` is a Banach space.

Because of its appeal to the equivalent condition for completeness in normed spaces in terms of
absolutely convergent series, the proof outlined above is not suitable for the more general setting
of topological groups, or more precisely, `uniform_group`s. It turns out that it is *not* always
the case that the quotient of a complete uniform group by a subgroup (even a closed subgroup) is
complete. However, when the prequotient is first countable, which in this context is equivalent
to metrizability, then the quotient is complete (see `quotient_group.complete_space`).

## Main statements

* `quotient_group.complete_space`
* `quotient_add_group.complete_space`

## References

* [N. Bourbaki, *General Topology*][bourbaki1966b]

## Tags

quotient group, complete space
-/

open topological_space filter set classical
open_locale topological_space uniformity pointwise

universes u v

/-- The map of a countably generated filter is countably generated -/
lemma filter.map.is_countably_generated {α β : Type*} (l : filter α) [l.is_countably_generated]
  (f : α → β) : (map f l).is_countably_generated :=
begin
  rcases l.exists_antitone_basis with ⟨u, hu⟩,
  exact has_countable_basis.is_countably_generated ⟨hu.map.to_has_basis, set.to_countable _⟩,
end

variables (G : Type u) [group G] [topological_space G] [topological_group G]

/-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/
@[to_additive "Neighborhoods in the quotient are precisely the map of neighborhoods in
the prequotient."]
lemma quotient_group.nhds_eq
  (N : subgroup G) (x : G) : 𝓝 (x : G ⧸ N) = map coe (𝓝 x) :=
le_antisymm ((quotient_group.is_open_map_coe N).nhds_le x) continuous_quot_mk.continuous_at

variables [first_countable_topology G] (N : subgroup G) [subgroup.normal N]

/-- In a first countable topological group `G` with normal subgroup `N`, `1 : G ⧸ N` has a
countable neighborhood basis. -/
@[to_additive "In a first countable topological additive group `G` with normal additive subgroup
`N`, `0 : G ⧸ N` has a countable neighborhood basis."]
instance quotient_group.nhds_one_is_countably_generated : (𝓝 (1 : G ⧸ N)).is_countably_generated :=
(quotient_group.nhds_eq G N 1).symm ▸ filter.map.is_countably_generated _ _

/-- In a first countable topological group `G` with normal subgroup `N`, `𝓤 (G ⧸ N)` is countably
generated. -/
@[to_additive "In a first countable topological additive group `G` with normal additive subgroup
`N`, `𝓤 (G ⧸ N)` is countably generated."]
instance quotient_group.uniformity_is_countably_generated :
  (@uniformity (G ⧸ N) (topological_group.to_uniform_space (G ⧸ N))).is_countably_generated :=
comap.is_countably_generated _ _

/-- Any first countable topological group has an antitone neighborhood basis `u : ℕ → set G` for
which `(u (n + 1)) ^ 2 ⊆ u n`. The existence of such a neighborhood basis is a key tool for
`quotient_group.complete_space` -/
@[to_additive "Any first countable topological additive group has an antitone neighborhood basis
`u : ℕ → set G` for which `u (n + 1) + u (n + 1) ⊆ u n`. The existence of such a neighborhood basis
is a key tool for `quotient_add_group.complete_space`"]
lemma topological_group.exists_antitone_basis_nhds_one :
  ∃ (u : ℕ → set G), (𝓝 1).has_antitone_basis u ∧ (∀ n, u (n + 1) * u (n + 1) ⊆ u n) :=
begin
  rcases (𝓝 (1 : G)).exists_antitone_basis with ⟨u, hu, u_anti⟩,
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
    λ n, (hy n).2⟩,
end

/-- The quotient `G ⧸ N` of a complete first countable topological group `G` by a normal subgroup
is itself complete. -/
@[to_additive "The quotient `G ⧸ N` of a complete first countable topological additive group
`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by
subspaces are complete."]
instance quotient_group.complete_space (G : Type u) [group G] [topological_space G]
  [topological_group G] [first_countable_topology G] (N : subgroup G) [N.normal]
  [@complete_space G (topological_group.to_uniform_space G)] :
  @complete_space (G ⧸ N) (topological_group.to_uniform_space (G ⧸ N)) :=
begin
  /- Since `G ⧸ N` is a topological group it is a uniform space, and since `G` is first countable
  the uniformities of both `G` and `G ⧸ N` are countably generated. Moreover, we may choose a
  sequential antitone neighborhood basis `u` for `𝓝 (1 : G)` so that `(u (n + 1)) ^ 2 ⊆ u n`, and
  this descends to an antitone neighborhood basis `v` for `𝓝 (1 : G ⧸ N)`. Since `𝓤 (G ⧸ N)` is
  countably generated, it suffices to show any Cauchy sequence `x` converges. -/
  letI : uniform_space (G ⧸ N) := topological_group.to_uniform_space (G ⧸ N),
  letI : uniform_space G := topological_group.to_uniform_space G,
  haveI : (𝓤 (G ⧸ N)).is_countably_generated := comap.is_countably_generated _ _,
  obtain ⟨u, hu, u_mul⟩ := topological_group.exists_antitone_basis_nhds_one G,
  obtain ⟨hv, v_anti⟩ := @has_antitone_basis.map _ _ _ _ _ _ (coe : G → G ⧸ N) hu,
  rw [←quotient_group.nhds_eq G N 1, quotient_group.coe_one] at hv,
  refine uniform_space.complete_of_cauchy_seq_tendsto (λ x hx, _),
  /- Given `n : ℕ`, for sufficiently large `a b : ℕ`, given any lift of `x b`, we can find a lift
  of `x a` such that the quotient of the lifts lies in `u n`. -/
  have key₀ : ∀ i j : ℕ, ∃ M : ℕ,
    j < M ∧ ∀ a b : ℕ, M ≤ a → M ≤ b → ∀ g : G, x b = g → ∃ g' : G, g / g' ∈ u i ∧ x a = g',
  { have h𝓤GN : (𝓤 (G ⧸ N)).has_basis (λ _, true) (λ i, {x | x.snd / x.fst ∈ coe '' u i}),
    { simpa [uniformity_eq_comap_nhds_one'] using hv.comap _ },
    simp only [h𝓤GN.cauchy_seq_iff, ge_iff_le, mem_set_of_eq, forall_true_left, mem_image] at hx,
    intros i j,
    rcases hx i with ⟨M, hM⟩,
    refine ⟨max j M + 1, (le_max_left _ _).trans_lt (lt_add_one _), λ a b ha hb g hg, _⟩,
    obtain ⟨y, y_mem, hy⟩ := hM a (((le_max_right j _).trans (lt_add_one _).le).trans ha) b
      (((le_max_right j _).trans (lt_add_one _).le).trans hb),
    refine ⟨y⁻¹ * g,
      by simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left] using y_mem, _⟩,
    rw [quotient_group.coe_mul, quotient_group.coe_inv, hy, hg, inv_div, div_mul_cancel'], },
  /- Inductively construct a subsequence `φ : ℕ → ℕ` using `key₀` so that if `a b : ℕ` exceed
  `φ (n + 1)`, then we may find lifts whose quotients lie within `u n`. -/
  set φ : ℕ → ℕ := λ n, nat.rec_on n (some $ key₀ 0 0) (λ k yk, some $ key₀ (k + 1) yk),
  have hφ : ∀ n : ℕ, φ n < φ (n + 1) ∧ ∀ a b : ℕ, φ (n + 1) ≤ a → φ (n + 1) ≤ b →
    (∀ g : G, x b = g → ∃ g' : G, g / g' ∈ u (n + 1) ∧ x a = g'),
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
  have hx' : ∀ n : ℕ, (x' n).fst / (x' (n + 1)).fst ∈ u (n + 1) :=
    λ n, (some_spec $ (hφ n).2 _ _ (hφ (n + 1)).1.le le_rfl (x' n).fst (x' n).snd).1,
  /- The sequence `x'` is Cauchy. This is where we exploit the condition on `u`. The key idea
  is to show by decreasing induction that `x' m / x' n ∈ u m` if `m ≤ n`. -/
  have x'_cauchy : cauchy_seq (λ n, (x' n).fst),
  { have h𝓤G : (𝓤 G).has_basis (λ _, true) (λ i, {x | x.snd / x.fst ∈ u i}),
    { simpa [uniformity_eq_comap_nhds_one'] using hu.to_has_basis.comap _ },
    simp only [h𝓤G.cauchy_seq_iff', ge_iff_le, mem_set_of_eq, forall_true_left],
    exact λ m, ⟨m, λ n hmn, nat.decreasing_induction'
      (λ k hkn hkm hk, u_mul k ⟨_, _, hx' k, hk, div_mul_div_cancel' _ _ _⟩)
      hmn (by simpa only [div_self'] using mem_of_mem_nhds (hu.mem _))⟩ },
  /- Since `G` is complete, `x'` converges to some `x₀`, and so the image of this sequence under
  the quotient map converges to `↑x₀`. The image of `x'` is a convergent subsequence of `x`, and
  since `x` is Cauchy, this implies it converges. -/
  rcases cauchy_seq_tendsto_of_complete x'_cauchy with ⟨x₀, hx₀⟩,
  refine ⟨↑x₀, tendsto_nhds_of_cauchy_seq_of_subseq hx
    (strict_mono_nat_of_lt_succ $ λ n, (hφ (n + 1)).1).tendsto_at_top _⟩,
  convert ((continuous_coinduced_rng : continuous (coe : G → G ⧸ N)).tendsto x₀).comp hx₀,
  exact funext (λ n, (x' n).snd),
end
