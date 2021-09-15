/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris Van Doorn
-/

import measure_theory.constructions.borel_space

/-!
# Regular measures

A measure is `regular` if it satisfies the following properties:
* it is finite on compact sets;
* it is outer regular for measurable sets with respect to open sets: the measure of any measurable
  set `A` is the infimum of `μ U` over all open sets `U` containing `A`;
* it is inner regular for open sets with respect to compacts sets: the measure of any open set `U`
  is the supremum of `μ K` over all compact sets `K` contained in `U`.

A measure is `weakly_regular` if it satisfies the following properties:
* it is outer regular for measurable sets with respect to open sets: the measure of any measurable
  set `A` is the infimum of `μ U` over all open sets `U` containing `A`;
* it is inner regular for open sets with respect to closed sets: the measure of any open set `U`
  is the supremum of `μ F` over all compact sets `F` contained in `U`.

Regularity implies weak regularity. Both these conditions are registered as typeclasses for a
measure `μ`, and this implication is recorded as an instance.

These conditions imply inner regularity for all measurable sets of finite measure (with respect to
compact sets or closed sets respectively), but in general not for all sets. For a counterexample,
consider the group `ℝ × ℝ` where the first factor has the discrete topology and the second one the
usual topology. It is a locally compact Hausdorff topological group, with Haar measure equal to
Lebesgue measure on each vertical fiber. The set `ℝ × {0}` has infinite measure (by outer
regularity), but any compact set it contains has zero measure (as it is finite).

Several authors require as a definition of regularity that all measurable sets are inner regular.
We have opted for the slightly weaker definition above as it holds for all Haar measures, it is
enough for essentially all applications, and it is equivalent to the other definition when the
measure is finite.

The interest of the notion of weak regularity is that it is enough for many applications, and it
is automatically satisfied by any finite measure on a metric space.

## Main definitions and results

* `regular μ`: a typeclass registering that a measure `μ` on a topological space is regular.
* `measurable_set.measure_eq_infi_is_open'` asserts that, when `μ` is regular, the measure of a
  measurable set is the infimum of the measure of open sets containing it. The unprimed version
  is reserved for weakly regular measures, as it should apply most of the time. Such open sets
  with suitable measures can be constructed with `measurable_set.exists_is_open_lt_of_lt'`.
* `is_open.measure_eq_supr_is_compact` asserts that the measure of an open set is the supremum of
  the measure of compact sets it contains. Such a compact set with suitable measure can be
  constructed with `is_open.exists_lt_is_compact`.
* `measurable_set.measure_eq_supr_is_compact_of_lt_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of compact sets it contains. Such a compact set
  with suitable measure can be constructed with `measurable_set.exists_lt_is_compact_of_lt_top` or
  `measurable_set.exists_lt_is_compact_of_lt_top_of_pos`.
* `regular.of_sigma_compact_space_of_is_locally_finite_measure` is an instance registering that a
  locally finite measure on a locally compact metric space is regular (in fact, an emetric space
  is enough).

* `weakly_regular μ`: a typeclass registering that a measure `μ` on a topological space is
  weakly regular.
* `measurable_set.measure_eq_infi_is_open`, `measurable_set.exists_is_open_lt_of_lt`,
  `is_open.measure_eq_supr_is_closed`, `is_open.exists_lt_is_closed`,
  `measurable_set.measure_eq_supr_is_closed_of_lt_top`,
  `measurable_set.exists_lt_is_closed_of_lt_top` and
  `measurable_set.exists_lt_is_closed_of_lt_top_of_pos`
  state the corresponding properties for weakly regular measures.
* `weakly_regular.of_pseudo_emetric_space_of_is_finite_measure` is an instance registering that a
  finite measure on a metric space is weakly regular (in fact, a pseudo emetric space is enough).

## Implementation notes

The main nontrivial statement is `weakly_regular.exists_closed_subset_self_subset_open`, expressing
that in a finite measure space, if every open set can be approximated from inside by closed sets,
then any measurable set can be approximated from inside by closed sets and from outside by open
sets. This statement is proved by measurable induction, starting from open sets and checking that
it is stable by taking complements (this is the point of this condition, being symmetrical between
inside and outside) and countable disjoint unions.

Once this statement is proved, one deduces results for general measures from this statement, by
restricting them to finite measure sets (and proving that this restriction is weakly regular,
using again the same statement).

## References

[Halmos, Measure Theory, §52][halmos1950measure]. Note that Halmos uses an unusual definition of
Borel sets (for him, they are elements of the `σ`-algebra generated by compact sets!), so his
proofs or statements do not apply directly.

[Billingsley, Convergence of Probability Measures][billingsley1999]
-/

open set filter
open_locale ennreal topological_space nnreal big_operators

namespace measure_theory
namespace measure

def inner_regular {α} {m : measurable_space α} (μ : measure α) (p q : set α → Prop) :=
∀ ⦃U⦄, q U → ∀ r < μ U, ∃ K ⊆ U, p K ∧ r < μ K

namespace inner_regular

variables {α : Type*} {m : measurable_space α} {μ : measure α} {p q : set α → Prop}
  {U : set α} {ε : ℝ≥0∞}

lemma measure_eq_supr (H : inner_regular μ p q) (hU : q U) : μ U = ⨆ (K ⊆ U) (hK : p K), μ K :=
begin
  refine le_antisymm (le_of_forall_lt (λ r hr, _)) (bsupr_le $ λ K hK, supr_le $ λ _, μ.mono hK),
  simpa only [lt_supr_iff, exists_prop] using H hU r hr
end

lemma exists_subset_lt_add (H : inner_regular μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U ≠ ∞)
  (hε : ε ≠ 0) :
  ∃ K ⊆ U, p K ∧ μ U < μ K + ε :=
begin
  cases eq_or_ne (μ U) 0 with h₀ h₀,
  { refine ⟨∅, empty_subset _, h0, _⟩,
    rwa [measure_empty, h₀, zero_add, pos_iff_ne_zero] },
  { rcases H hU _ (ennreal.sub_lt_self hμU h₀ hε) with ⟨K, hKU, hKc, hrK⟩,
    exact ⟨K, hKU, hKc, ennreal.lt_add_of_sub_lt (or.inl hμU) hrK⟩ }
end

lemma map {α β} [measurable_space α] [measurable_space β] {μ : measure α} {pa qa : set α → Prop}
  (H : inner_regular μ pa qa) (f : α ≃ β) (hf : measurable f)
  {pb qb : set β → Prop} (hAB : ∀ U, qb U → qa (f ⁻¹' U)) (hAB' : ∀ K, pa K → pb (f '' K))
  (hB₁ : ∀ K, pb K → measurable_set K) (hB₂ : ∀ U, qb U → measurable_set U) :
  inner_regular (map f μ) pb qb :=
begin
  intros U hU r hr,
  rw [map_apply hf (hB₂ _ hU)] at hr,
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩,
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, _⟩,
  rwa [map_apply hf (hB₁ _ $ hAB' _ hKc), f.preimage_image]
end

lemma smul (H : inner_regular μ p q) (c : ℝ≥0∞) : inner_regular (c • μ) p q :=
begin
  intros U hU r hr,
  rw [smul_apply, H.measure_eq_supr hU] at hr,
  simpa only [ennreal.mul_supr, lt_supr_iff, exists_prop] using hr
end

lemma trans {q' : set α → Prop} (H : inner_regular μ p q) (H' : inner_regular μ q q') :
  inner_regular μ p q' :=
begin
  intros U hU r hr,
  rcases H' hU r hr with ⟨F, hFU, hqF, hF⟩, rcases H hqF _ hF with ⟨K, hKF, hpK, hrK⟩,
  exact ⟨K, hKF.trans hFU, hpK, hrK⟩
end

end inner_regular

variables {α β : Type*} [measurable_space α] [topological_space α] {μ : measure α}

/-- A measure `μ` is outer regular if `μ(A) = inf {μ(U) | A ⊆ U open}` for a measurable set `A`. -/
@[protect_proj] class outer_regular (μ : measure α) : Prop :=
(outer_regular : ∀ ⦃A : set α⦄, measurable_set A → ∀ r > μ A, ∃ U ⊇ A, is_open U ∧ μ U < r)

/-- A measure `μ` is regular if
  - it is finite on all compact sets;
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using compact sets:
    `μ(U) = sup {μ(K) | K ⊆ U compact}` for `U` open. -/
@[protect_proj] class regular (μ : measure α) extends outer_regular μ : Prop :=
(lt_top_of_is_compact : ∀ ⦃K : set α⦄, is_compact K → μ K < ∞)
(inner_regular : inner_regular μ is_compact is_open)

/-- A measure `μ` is weakly regular if
  - it is outer regular: `μ(A) = inf { μ(U) | A ⊆ U open }` for `A` measurable;
  - it is inner regular for open sets, using closed sets:
    `μ(U) = sup {μ(F) | F ⊆ U compact}` for `U` open. -/
@[protect_proj] class weakly_regular (μ : measure α) extends outer_regular μ : Prop :=
(inner_regular : inner_regular μ is_closed is_open)

/-- A regular measure is weakly regular. -/
@[priority 100] -- see Note [lower instance priority]
instance regular.weakly_regular [t2_space α] [regular μ] : weakly_regular μ :=
{ inner_regular := λ U hU r hr, let ⟨K, hKU, hcK, hK⟩ := regular.inner_regular hU r hr
  in ⟨K, hKU, hcK.is_closed, hK⟩ }

namespace outer_regular

instance zero : outer_regular (0 : measure α) :=
⟨λ A hA r hr, ⟨univ, subset_univ A, is_open_univ, hr⟩⟩

/-- Given `r` larger than the measure of a set `A`, there exists an open superset of `A` with
measure less than `r`. -/
lemma _root_.set.exists_is_open_lt_of_lt [outer_regular μ] (A : set α) (r : ℝ≥0∞) (hr : μ A < r) :
  ∃ U ⊇ A, is_open U ∧ μ U < r :=
begin
  rcases outer_regular.outer_regular (measurable_set_to_measurable μ A) r
    (by rwa measure_to_measurable) with ⟨U, hAU, hUo, hU⟩,
  exact ⟨U, (subset_to_measurable _ _).trans hAU, hUo, hU⟩
end

/-- For an outer regular measure, the measure of a set is the infimum of the measures of open sets
containing it. -/
lemma _root_.set.measure_eq_infi_is_open (A : set α) (μ : measure α) [outer_regular μ] :
  μ A = (⨅ (U : set α) (h : A ⊆ U) (h2 : is_open U), μ U) :=
begin
  refine le_antisymm (le_binfi $ λ s hs, le_infi $ λ h2s, μ.mono hs) _,
  refine le_of_forall_lt' (λ r hr, _),
  simpa only [infi_lt_iff, exists_prop] using A.exists_is_open_lt_of_lt r hr
end

protected lemma map [opens_measurable_space α] [measurable_space β] [topological_space β]
  [borel_space β] (f : α ≃ₜ β) (μ : measure α) [outer_regular μ] :
  (measure.map f μ).outer_regular :=
begin
  refine ⟨λ A hA r hr, _⟩,
  rw [map_apply f.measurable hA, ← f.image_symm] at hr,
  rcases set.exists_is_open_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩,
  have : is_open (f.symm ⁻¹' U), from hUo.preimage f.symm.continuous,
  refine ⟨f.symm ⁻¹' U, image_subset_iff.1 hAU, this, _⟩,
  rwa [map_apply f.measurable this.measurable_set, f.preimage_symm, f.preimage_image],
end

protected lemma smul (μ : measure α) [outer_regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) :
  (x • μ).outer_regular :=
begin
  rcases eq_or_ne x 0 with rfl|h0,
  { rw zero_smul, exact outer_regular.zero },
  { refine ⟨λ A hA r hr, _⟩,
    rw [smul_apply, A.measure_eq_infi_is_open] at hr,
    simpa only [ennreal.mul_infi_of_ne h0 hx, gt_iff_lt, infi_lt_iff, exists_prop] using hr }
end

lemma of_seq_restrict (μ : measure α) (s : ℕ → set α) (h : ∀ n, outer_regular (μ.restrict (s n)))
  (hU : (⋃ n, s n) = univ) : outer_regular μ :=
⟨begin
  introsI A hA r hr,
  rcases ennreal.exists_pos_sum_of_encodable' (ennreal.sub_pos.2 hr).ne' ℕ with ⟨δ, δ0, hδε⟩,
  set t : ℕ → set α := disjointed (accumulate s),
  have htU : (⋃ n, t n) = univ, by simp only [t, Union_disjointed, Union_accumulate, hU],
  have htd : pairwise (disjoint on t) := disjoint_disjointed _,
  
end⟩

end outer_regular

namespace inner_regular

variables {p q : set α → Prop} {U s : set α} {ε r : ℝ≥0∞}

lemma measurable_set_of_open [opens_measurable_space α] [outer_regular μ]
  (H : inner_regular μ p is_open) (h0 : p ∅) (hd : ∀ ⦃s U⦄, p s → is_open U → p (s \ U)) :
  inner_regular μ p (λ s, measurable_set s ∧ μ s ≠ ∞) :=
begin
  rintros s ⟨hs, hμs⟩ r hr,
  obtain ⟨ε, hε, hεs, rfl⟩ : ∃ ε ≠ 0, ε + ε ≤ μ s ∧ r = μ s - (ε + ε),
  { use (μ s - r) / 2, simp [*, hr.le, ennreal.add_halves, ennreal.sub_sub_cancel, le_add_right] },
  rcases s.exists_is_open_lt_of_lt (μ s + ε) (ennreal.lt_add_right hμs hε)
    with ⟨U, hsU, hUo, hμU⟩,
  have : μ (U \ s) < ε,
  { rw [measure_diff hsU hUo.measurable_set hs hμs],
    refine ennreal.sub_lt_of_lt_add (measure_mono hsU) _, rwa add_comm },
  rcases (U \ s).exists_is_open_lt_of_lt _ this with ⟨U', hsU', hU'o, hμU'⟩,
  replace hsU' := diff_subset_comm.1 hsU',
  rcases H.exists_subset_lt_add h0 hUo (ne_top_of_lt hμU) hε with ⟨K, hKU, hKc, hKr⟩,
  refine ⟨K \ U', λ x hx, hsU' ⟨hKU hx.1, hx.2⟩, hd hKc hU'o, ennreal.sub_lt_of_lt_add hεs _⟩,
  calc μ s ≤ μ U                   : μ.mono hsU
       ... < μ K + ε               : hKr
       ... ≤ μ (K \ U') + μ U' + ε :
    add_le_add_right (ennreal.sub_le_iff_le_add.1 le_measure_diff) _
       ... ≤ μ (K \ U') + ε + ε    : by { mono*, exacts [hμU'.le, le_rfl] }
       ... = μ (K \ U') + (ε + ε)  : add_assoc _ _ _
end

open finset

/-- In a finite measure space, assume that any open set can be approximated from inside by closed
sets. Then any measurable set can be approximated from inside by closed sets, and from outside
by open sets. -/
lemma weakly_regular_of_finite [borel_space α] (μ : measure α) [is_finite_measure μ]
  (H : inner_regular μ is_closed is_open) : weakly_regular μ :=
begin
  have hfin : ∀ {s}, μ s ≠ ⊤ := measure_ne_top μ,
  suffices : ∀ s, measurable_set s → ∀ ε ≠ 0,
    ∃ (F ⊆ s) (U ⊇ s), is_closed F ∧ is_open U ∧ μ s ≤ μ F + ε ∧ μ U ≤ μ s + ε,
  { refine { outer_regular := λ s hs r hr, _, inner_regular := H },
    rcases exists_between hr with ⟨r', hsr', hr'r⟩,
    rcases this s hs _ (ennreal.sub_pos.2 hsr').ne' with ⟨-, -, U, hsU, -, hUo, -, H⟩,
    refine ⟨U, hsU, hUo, _⟩,
    rw [ennreal.add_sub_cancel_of_le hsr'.le] at H, exact H.trans_lt hr'r },
  refine measurable_set.induction_on_open _ _ _,
  /- The proof is by measurable induction: we should check that the property is true for the empty
  set, for open sets, and is stable by taking the complement and by taking countable disjoint
  unions. The point of the property we are proving is that it is stable by taking complements
  (exchanging the roles of closed and open sets and thanks to the finiteness of the measure). -/
  -- check for open set
  { intros U hU ε hε,
    rcases H.exists_subset_lt_add is_closed_empty hU hfin hε with ⟨F, hsF, hFc, hF⟩,
    exact ⟨F, hsF, U, subset.rfl, hFc, hU, hF.le, le_self_add⟩ },
  -- check for complements
  { rintros s hs H ε hε,
    rcases H ε hε with ⟨F, hFs, U, hsU, hFc, hUo, hF, hU⟩,
    refine ⟨Uᶜ, compl_subset_compl.2 hsU, Fᶜ, compl_subset_compl.2 hFs,
      hUo.is_closed_compl, hFc.is_open_compl, _⟩,
    simp only [measure_compl_le_add_iff, *, hUo.measurable_set, hFc.measurable_set, true_and] },
  -- check for disjoint unions
  { intros s hsd hsm H ε ε0, have ε0' : ε / 2 ≠ 0, from (ennreal.half_pos ε0).ne',
    rcases ennreal.exists_pos_sum_of_encodable' ε0' ℕ with ⟨δ, δ0, hδε⟩,
    choose F hFs U hsU hFc hUo hF hU using λ n, H n (δ n) (δ0 n).ne',
    -- the approximating closed set is constructed by considering finitely many sets `s i`, which
    -- cover all the measure up to `ε/2`, approximating each of these by a closed set `F i`, and
    -- taking the union of these (finitely many) `F i`.
    have : tendsto (λ t, ∑ k in t, μ (s k) + ε / 2) at_top (𝓝 $ μ (⋃ n, s n) + ε / 2),
    { rw measure_Union hsd hsm, exact tendsto.add ennreal.summable.has_sum tendsto_const_nhds },
    rcases (this.eventually $ lt_mem_nhds $ ennreal.lt_add_right hfin ε0').exists with ⟨t, ht⟩,
    -- the approximating open set is constructed by taking for each `s n` an approximating open set
    -- `U n` with measure at most `μ (s n) + δ n` for a summable `δ`, and taking the union of these.
    refine ⟨⋃ k ∈ t, F k, Union_subset_Union $ λ k, Union_subset $ λ _, hFs _,
      ⋃ n, U n, Union_subset_Union hsU, is_closed_bUnion t.finite_to_set $ λ k _, hFc k,
      is_open_Union hUo, ht.le.trans _, _⟩,
    { calc ∑ k in t, μ (s k) + ε / 2 ≤ ∑ k in t, μ (F k) + ∑ k in t, δ k + ε / 2 :
        by { rw ← sum_add_distrib, exact add_le_add_right (sum_le_sum $ λ k hk, hF k) _ }
      ... ≤ ∑ k in t, μ (F k) + ε / 2 + ε / 2 :
        add_le_add_right (add_le_add_left ((ennreal.sum_le_tsum _).trans hδε.le) _) _
      ... = μ (⋃ k ∈ t, F k) + ε : _,
      rw [measure_bUnion_finset, add_assoc, ennreal.add_halves],
      exacts [λ k _ n _ hkn, (hsd k n hkn).mono (hFs k) (hFs n), λ k hk, (hFc k).measurable_set] },
    { calc μ (⋃ n, U n) ≤ ∑' n, μ (U n) : measure_Union_le _
      ... ≤ ∑' n, (μ (s n) + δ n) : ennreal.tsum_le_tsum hU
      ... = μ (⋃ n, s n) + ∑' n, δ n : by rw [measure_Union hsd hsm, ennreal.tsum_add]
      ... ≤ μ (⋃ n, s n) + ε : add_le_add_left (hδε.le.trans ennreal.half_le_self) _ } }
end

/-- In a metric space (or even a pseudo emetric space), an open set can be approximated from inside
by closed sets. -/
lemma of_pseudo_emetric_space {X : Type*} [pseudo_emetric_space X] [measurable_space X]
  [opens_measurable_space X] (μ : measure X) :
  inner_regular μ is_closed is_open :=
begin
  intros U hU r hr,
  rcases hU.exists_Union_is_closed with ⟨F, F_closed, -, rfl, F_mono⟩,
  rw measure_Union_eq_supr (λ n, (F_closed n).measurable_set) F_mono.directed_le at hr,
  rcases lt_supr_iff.1 hr with ⟨n, hn⟩,
  exact ⟨F n, subset_Union _ _, F_closed n, hn⟩
end

lemma is_compact_is_closed {X : Type*} [topological_space X] [t2_space X]
  [sigma_compact_space X] [measurable_space X] [opens_measurable_space X] (μ : measure X) :
  inner_regular μ is_compact is_closed :=
begin
  intros F hF r hr,
  set B : ℕ → set X := compact_covering X,
  have hBc : ∀ n, is_compact (F ∩ B n), from λ n, (is_compact_compact_covering X n).inter_left hF,
  have hBU : (⋃ n, F ∩ B n) = F, by rw [← inter_Union, Union_compact_covering, set.inter_univ],
  have : μ F = ⨆ n, μ (F ∩ B n),
  { rw [← measure_Union_eq_supr, hBU],
    exacts [λ n, (hBc n).measurable_set, monotone.directed_le $
      λ m n h, inter_subset_inter_right _ (compact_covering_subset _ h)] },
  rw this at hr, rcases lt_supr_iff.1 hr with ⟨n, hn⟩,
  exact ⟨_, inter_subset_left _ _, hBc n, hn⟩
end

end inner_regular

namespace regular

instance zero : regular (0 : measure α) :=
⟨λ K hK, ennreal.coe_lt_top, λ U hU r hr, ⟨∅, empty_subset _, is_compact_empty, hr⟩⟩

lemma _root_.is_open.exists_lt_is_compact [regular μ] ⦃U : set α⦄ (hU : is_open U)
  {r : ℝ≥0∞} (hr : r < μ U) :
  ∃ K ⊆ U, is_compact K  ∧ r < μ K :=
regular.inner_regular hU r hr

/-- The measure of an open set is the supremum of the measures of compact sets it contains. -/
lemma _root_.is_open.measure_eq_supr_is_compact ⦃U : set α⦄ (hU : is_open U)
  (μ : measure α) [regular μ] :
  μ U = (⨆ (K : set α) (h : K ⊆ U) (h2 : is_compact K), μ K) :=
regular.inner_regular.measure_eq_supr hU

lemma _root_.is_open.exists_is_compact_lt_add [regular μ] ⦃U : set α⦄ (hU : is_open U)
  (hμU : μ U ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ K ⊆ U, is_compact K ∧ μ U < μ K + ε :=
regular.inner_regular.exists_subset_lt_add is_compact_empty hU hμU hε

lemma exists_compact_not_null [regular μ] : (∃ K, is_compact K ∧ μ K ≠ 0) ↔ μ ≠ 0 :=
by simp_rw [ne.def, ← measure_univ_eq_zero, is_open_univ.measure_eq_supr_is_compact,
    ennreal.supr_eq_zero, not_forall, exists_prop, subset_univ, true_and]

lemma inner_regular_measurable [opens_measurable_space α] [regular μ] :
  inner_regular μ is_compact (λ s, measurable_set s ∧ μ s ≠ ∞) :=
regular.inner_regular.measurable_set_of_open is_compact_empty (λ _ _, is_compact.diff)

lemma _root_.measurable_set.exists_is_compact_lt_add [opens_measurable_space α]
  [regular μ] ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ K ⊆ A, is_compact K ∧ μ A < μ K + ε :=
regular.inner_regular_measurable.exists_subset_lt_add is_compact_empty ⟨hA, h'A⟩ h'A hε

lemma _root_.measurable_set.exists_lt_is_compact_of_ne_top [regular μ]
  [opens_measurable_space α] ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞)
  {r : ℝ≥0∞} (hr : r < μ A) :
  ∃ K ⊆ A, is_compact K ∧ r < μ K :=
regular.inner_regular_measurable ⟨hA, h'A⟩ _ hr

/-- Given a regular measure, any measurable set of finite mass can be approximated from
inside by compact sets. -/
lemma _root_.measurable_set.measure_eq_supr_is_compact_of_ne_top
  [opens_measurable_space α] [t2_space α] [regular μ]
  ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞) :
  μ A = (⨆ (K ⊆ A) (h : is_compact K), μ K) :=
regular.inner_regular_measurable.measure_eq_supr ⟨hA, h'A⟩

protected lemma map [opens_measurable_space α] [measurable_space β] [topological_space β]
  [t2_space β] [borel_space β] [regular μ] (f : α ≃ₜ β) :
  (measure.map f μ).regular :=
begin
  haveI := outer_regular.map f μ,
  split,
  { intros K hK, rw [map_apply f.measurable hK.measurable_set],
    apply regular.lt_top_of_is_compact,
    rwa f.compact_preimage },
  { exact regular.inner_regular.map f.to_equiv f.measurable (λ U hU, hU.preimage f.continuous)
      (λ K hK, hK.image f.continuous) (λ K hK, hK.measurable_set) (λ U hU, hU.measurable_set) }
end

protected lemma smul [regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) :
  (x • μ).regular :=
begin
  haveI := outer_regular.smul μ hx,
  exact ⟨λ K hK, ennreal.mul_lt_top hx (regular.lt_top_of_is_compact hK).ne,
    regular.inner_regular.smul x⟩
end

/-- A regular measure in a σ-compact space is σ-finite. -/
@[priority 100] -- see Note [lower instance priority]
instance sigma_finite [sigma_compact_space α] [regular μ] : sigma_finite μ :=
⟨⟨{ set := compact_covering α,
  set_mem := λ n, trivial,
  finite := λ n, regular.lt_top_of_is_compact $ is_compact_compact_covering α n,
  spanning := Union_compact_covering α }⟩⟩

end regular

namespace weakly_regular

lemma _root_.is_open.exists_lt_is_closed [weakly_regular μ] ⦃U : set α⦄ (hU : is_open U)
  {r : ℝ≥0∞} (hr : r < μ U) :
  ∃ F ⊆ U, is_closed F ∧ r < μ F :=
weakly_regular.inner_regular hU r hr

lemma _root_.is_open.measure_eq_supr_is_closed ⦃U : set α⦄ (hU : is_open U)
  (μ : measure α) [weakly_regular μ] :
  μ U = (⨆ (F ⊆ U) (h : is_closed F), μ F) :=
weakly_regular.inner_regular.measure_eq_supr hU

lemma _root_.is_open.exists_is_closed_lt_add [weakly_regular μ] [opens_measurable_space α]
  ⦃U : set α⦄ (hU : is_open U) (hμU : μ U ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ K ⊆ U, is_closed K ∧ μ U < μ K + ε :=
weakly_regular.inner_regular.exists_subset_lt_add is_closed_empty hU hμU hε

lemma inner_regular_measurable [opens_measurable_space α] [weakly_regular μ] :
  inner_regular μ is_closed (λ s, measurable_set s ∧ μ s ≠ ∞) :=
weakly_regular.inner_regular.measurable_set_of_open is_closed_empty
  (λ _ _ h₁ h₂, h₁.inter h₂.is_closed_compl)

/-- If `s` is a measurable set, a weakly regular measure `μ` is finite on `s`, and `ε` is a positive
number, then there exist a closed set `K ⊆ s`  such that `μ s < μ K + ε`. -/
lemma _root_.measurable_set.exists_is_closed_lt_add [weakly_regular μ]
  [opens_measurable_space α] {s : set α} (hs : measurable_set s) (hμs : μ s ≠ ∞)
  {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ K ⊆ s, is_closed K ∧ μ s < μ K + ε :=
inner_regular_measurable.exists_subset_lt_add is_closed_empty ⟨hs, hμs⟩ hμs hε

/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
lemma _root_.measurable_set.exists_lt_is_closed_of_ne_top [weakly_regular μ]
  [opens_measurable_space α] ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞)
  {r : ℝ≥0∞} (hr : r < μ A) :
  ∃ K ⊆ A, is_closed K ∧ r < μ K :=
inner_regular_measurable ⟨hA, h'A⟩ _ hr

/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
lemma _root_.measurable_set.measure_eq_supr_is_closed_of_ne_top [opens_measurable_space α]
  [weakly_regular μ] ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞) :
  μ A = (⨆ (K ⊆ A) (h : is_closed K), μ K) :=
inner_regular_measurable.measure_eq_supr ⟨hA, h'A⟩

/-- The restriction of a weakly regular measure to a measurable set of finite measure is
weakly regular. -/
lemma restrict_of_measurable_set [borel_space α] [weakly_regular μ] (A : set α)
  (hA : measurable_set A) (h'A : μ A ≠ ∞) : weakly_regular (μ.restrict A) :=
begin
  haveI : fact (μ A < ∞) := ⟨h'A.lt_top⟩,
  refine inner_regular.weakly_regular_of_finite _ (λ V V_open, _),
  simp only [restrict_apply' hA], intros r hr,
  have : μ (V ∩ A) ≠ ∞, from ne_top_of_le_ne_top h'A (measure_mono $ inter_subset_right _ _),
  rcases (V_open.measurable_set.inter hA).exists_lt_is_closed_of_ne_top this hr
    with ⟨F, hFVA, hFc, hF⟩,
  refine ⟨F, hFVA.trans (inter_subset_left _ _), hFc, _⟩,
  rwa inter_eq_self_of_subset_left (hFVA.trans $ inter_subset_right _ _)
end

/-- Any finite measure on a metric space (or even a pseudo emetric space) is weakly regular. -/
@[priority 100] -- see Note [lower instance priority]
instance of_pseudo_emetric_space_of_is_finite_measure {X : Type*} [pseudo_emetric_space X]
  [measurable_space X] [borel_space X] (μ : measure X) [is_finite_measure μ] :
  weakly_regular μ :=
(inner_regular.of_pseudo_emetric_space μ).weakly_regular_of_finite μ

end weakly_regular

namespace regular

/-- Any locally finite measure on a sigma compact locally compact metric space is regular. -/
@[priority 100] -- see Note [lower instance priority]
instance of_sigma_compact_space_of_is_locally_finite_measure {X : Type*}
  [emetric_space X] [sigma_compact_space X] [locally_compact_space X]
  [measurable_space X] [borel_space X] (μ : measure X)
  [is_locally_finite_measure μ] : regular μ :=
{ lt_top_of_is_compact := λ K hK, hK.measure_lt_top,
  inner_regular := (inner_regular.is_compact_is_closed μ).trans
    (inner_regular.of_pseudo_emetric_space μ),
  outer_regular :=
  begin
    /- let `B n` be a compact exhaustion of the space, and let `C n = B n \ B (n-1)`. Consider a
    measurable set `A`. Then `A ∩ C n` is a set of finite measure, that can be approximated by an
    open set `U n` (by using the fact that the measure restricted to `B (n+1)` is finite, and
    therefore weakly regular). The union of the `U n` is an open set containing `A`, with measure
    arbitrarily close to that of `A`.
    -/
    assume A hA r hr,
    rcases ennreal.exists_pos_sum_of_encodable' (ennreal.sub_pos.2 hr).ne' ℕ with ⟨δ, δpos, hδ⟩,
    have B : compact_exhaustion X := default _,
    let C := disjointed (λ n, B n),
    have C_meas : ∀ n, measurable_set (C n) :=
      measurable_set.disjointed (λ n, (B.is_compact n).measurable_set),
    have A_eq : A = (⋃ n, A ∩ C n),
      by simp_rw [← inter_Union, C, Union_disjointed, compact_exhaustion.Union_eq, inter_univ],
    have μA_eq : μ A = ∑' n, μ (A ∩ C n),
    { conv_lhs { rw A_eq },
      rw measure_Union,
      { assume m n hmn,
        exact disjoint.mono (inter_subset_right _ _) (inter_subset_right _ _)
          (disjoint_disjointed _ m n hmn), },
      { exact (λ n, hA.inter (C_meas n)) } },
    have : ∀ n, ∃ U, is_open U ∧ (A ∩ C n ⊆ U) ∧ (μ U ≤ μ (A ∩ C n) + δ n),
    { assume n,
      set ν := μ.restrict (B (n+1)) with hν,
      haveI : fact (μ (B (n + 1)) < ∞) := ⟨(B.is_compact _).measure_lt_top⟩,
      obtain ⟨U, hACU : A ∩ C n ⊆ U, U_open : is_open U, hνU : ν U < ν (A ∩ C n) + δ n⟩ :=
        (A ∩ C n).exists_is_open_lt_of_lt _
          (ennreal.lt_add_right (measure_ne_top ν _) (δpos n).ne'),
      refine ⟨U ∩ interior (B (n+1)), U_open.inter is_open_interior, _, _⟩,
      { simp only [hACU, true_and, subset_inter_iff],
        refine (inter_subset_right _ _).trans _,
        exact (disjointed_subset _ n).trans (B.subset_interior_succ _) },
      { simp only [hν, restrict_apply' (B.is_compact _).measurable_set] at hνU,
        calc μ (U ∩ interior (B (n + 1))) ≤ μ (U ∩ B (n + 1)) :
          measure_mono (inter_subset_inter_right _ interior_subset)
        ... ≤ μ (A ∩ C n ∩ B (n + 1)) + δ n : hνU.le
        ... ≤ μ (A ∩ C n) + δ n :
          add_le_add (measure_mono (inter_subset_left _ _)) (le_refl _) } },
    choose U hU using this,
    refine ⟨⋃ n, U n, _, is_open_Union (λ n, (hU n).1), _⟩,
    { rw A_eq, exact Union_subset_Union (λ n, (hU n).2.1) },
    { calc μ (⋃ (n : ℕ), U n)
          ≤ ∑' n, μ (U n) : measure_Union_le _
      ... ≤ ∑' n, (μ (A ∩ C n) + δ n) : ennreal.tsum_le_tsum (λ n, (hU n).2.2)
      ... < μ A + (r - μ A) :
        by { rw [ennreal.tsum_add, μA_eq.symm], exact ennreal.add_lt_add_left hr.lt.ne_top hδ }
      ... = r : ennreal.add_sub_cancel_of_le hr.lt.le }
  end }

end regular

end measure
end measure_theory
