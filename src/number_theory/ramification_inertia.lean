/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.separable
import linear_algebra.free_module.finite
import ring_theory.dedekind_domain

/-!
# Ramification index and inertia degree

If `P : ideal S` lies over `p : ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed).
The **ramification index** `ramification_idx f p P` is the multiplicity of `P` in `map f p`,
and the **inertia degree** `inertia_deg f p P` is the degree of the field extension
`(S / P) : (R / p)`.

The main theorem `sum_ramification_inertia` states that for all coprime `P` lying over `p`,
`Σ P, ramification_idx f p P * inertia_deg f p P` equals the degree of the field extension
`Frac(S) : Frac(R)`.

## Implementation notes

Often the above theory is set up in the case where:
 * `R` is the ring of integers of a number field `K`,
 * `L` is a finite separable extension of `K`,
 * `S` is the integral closure of `R` in `L`,
 * `p` and `P` are maximal ideals,
 * `P` is an ideal lying over `p`
We will try to relax the above hypotheses as much as possible

-/

open_locale big_operators
open_locale non_zero_divisors

variables {R S : Type*} [integral_domain R] [integral_domain S] (f : R →+* S)
variables (p : ideal R) (P : ideal S)

open finite_dimensional
open ideal
open unique_factorization_monoid

section move_me

@[simp] lemma ideal.quotient.algebra_map_eq :
  algebra_map R p.quotient = p^.quotient.mk :=
rfl

@[simp] lemma ideal.quotient.mk_comp_algebra_map [algebra R S] :
  P^.quotient.mk^.comp (algebra_map R S) = algebra_map R P^.quotient :=
rfl

@[simp] lemma ideal.quotient.mk_algebra_map [algebra R S] (x : R) :
  ideal.quotient.mk P (algebra_map R S x) = algebra_map R P^.quotient x :=
rfl

/-- If there is an injective map `R/p → S/P` such that following diagram commutes:
```
R   → S
↓     ↓
R/p → S/P
```
then `P` lies over `p`.
-/
lemma comap_eq_of_scalar_tower_quotient [algebra R S] [algebra p.quotient P.quotient]
  [is_scalar_tower R p.quotient P.quotient]
  (h : function.injective (algebra_map p.quotient P.quotient)) :
  comap (algebra_map R S) P = p :=
begin
  ext x, split; rw [mem_comap, ← quotient.eq_zero_iff_mem, ← quotient.eq_zero_iff_mem,
    ideal.quotient.mk_algebra_map, is_scalar_tower.algebra_map_apply _ p.quotient,
    ideal.quotient.algebra_map_eq p],
  { intro hx,
    exact (algebra_map p.quotient P.quotient).injective_iff.mp h _ hx },
  { intro hx,
    rw [hx, ring_hom.map_zero] },
end

lemma ideal.quotient.subsingleton_iff : subsingleton p.quotient ↔ p = ⊤ :=
by rw [eq_top_iff_one, ← subsingleton_iff_zero_eq_one, eq_comm,
       ← p^.quotient.mk^.map_one, quotient.eq_zero_iff_mem]

/-- `R / p` has a canonical map to `S / pS`. -/
instance ideal.quotient.algebra_quotient_map_quotient :
  algebra p.quotient (map f p).quotient :=
ring_hom.to_algebra $
ideal.quotient.lift _ ((ideal.quotient.mk _).comp f) $
(λ a ha, quotient.eq_zero_iff_mem.mpr (mem_map_of_mem f ha))

@[simp] lemma ideal.quotient.algebra_map_quotient_map_quotient (x : R) :
  algebra_map p.quotient (map f p).quotient (ideal.quotient.mk p x) = ideal.quotient.mk _ (f x) :=
rfl

instance ideal.quotient.tower_quotient_map_quotient [algebra R S] :
  is_scalar_tower R p.quotient (map (algebra_map R S) p).quotient :=
is_scalar_tower.of_algebra_map_eq $ λ x,
by rw [ideal.quotient.algebra_map_eq, ideal.quotient.algebra_map_quotient_map_quotient,
       ideal.quotient.mk_algebra_map]

/-- We can clear the denominators of a finite family of fractions. -/
lemma is_localization.exist_integer_multiples_of_finset' {R Rₘ ι : Type*}
  [comm_ring R] [comm_ring Rₘ] (M : submonoid R) [algebra R Rₘ] [is_localization M Rₘ]
  (s : finset ι) (f : ι → Rₘ) :
  ∃ (b : M), ∀ i ∈ s, is_localization.is_integer R ((b : R) • f i) :=
begin
  haveI := classical.prop_decidable,
  refine ⟨∏ i in s, (is_localization.sec M (f i)).2, λ i hi, ⟨_, _⟩⟩,
  { exact (∏ j in s.erase i,
    (is_localization.sec M (f j)).2) * (is_localization.sec M (f i)).1 },
  rw [ring_hom.map_mul, is_localization.sec_spec', ←mul_assoc, ←(algebra_map R Rₘ).map_mul,
      ← algebra.smul_def],
  congr' 2,
  refine trans _ ((submonoid.subtype M).map_prod _ _).symm,
  rw [mul_comm, ←finset.prod_insert (s.not_mem_erase i),
      finset.insert_erase hi],
  refl
end

/-- We can clear the denominators of a finite family of fractions. -/
lemma is_localization.exist_integer_multiples {R Rₘ ι : Type*}
  [comm_ring R] [fintype ι] [comm_ring Rₘ] (M : submonoid R) [algebra R Rₘ] [is_localization M Rₘ]
  (f : ι → Rₘ) : ∃ (b : M), ∀ i, is_localization.is_integer R ((b : R) • f i) :=
begin
  obtain ⟨b, hb⟩ := is_localization.exist_integer_multiples_of_finset' M finset.univ f,
  exact ⟨b, λ i, hb i (finset.mem_univ _)⟩
end

instance ideal.noetherian_dimensional_quotient_map_quotient [algebra R S] [p.is_maximal]
  [is_noetherian R S] :
  is_noetherian p.quotient (map (algebra_map R S) p).quotient :=
is_noetherian_of_tower R $
is_noetherian_of_surjective S (ideal.quotient.mkₐ R _).to_linear_map $
linear_map.range_eq_top.mpr ideal.quotient.mk_surjective

/-
instance ideal.finite_dimensional_quotient_map_quotient [algebra R S] [p.is_maximal]
  [is_noetherian R S] :
  finite_dimensional p.quotient (map (algebra_map R S) p).quotient :=
is_noetherian_of_tower R $
is_noetherian_of_surjective S (ideal.quotient.mkₐ R _).to_linear_map $
linear_map.range_eq_top.mpr ideal.quotient.mk_surjective
-/

instance is_fraction_ring.no_zero_smul_divisors
  {R K : Type*} [integral_domain R] [field K] [algebra R K] [is_fraction_ring R K] :
  no_zero_smul_divisors R K :=
⟨λ x z h, by rwa [algebra.smul_def, mul_eq_zero, is_fraction_ring.to_map_eq_zero_iff] at h⟩

open fractional_ideal

/-- Strengthening of `is_localization.exist_integer_multiples`:
Let `p ≠ ⊤` be an ideal in a Dedekind domain `R`, and `f ≠ 0` a finite collection
of elements of `K = Frac(R)`, then we can multiply the elements of `f` by some `a : K`
to find a collection of elements of `R` that is not completely contained in `p`. -/
lemma ideal.exist_integer_multiples_not_mem
  {R K : Type*} [integral_domain R] [is_dedekind_domain R] [field K]
  [algebra R K] [is_fraction_ring R K]
  {p : ideal R} (hp : p ≠ ⊤) {ι : Type*} (s : finset ι) (f : ι → K)
  {j} (hjs : j ∈ s) (hjf : f j ≠ 0) :
  ∃ a : K, (∀ i ∈ s, is_localization.is_integer R (a * f i)) ∧
    ∃ i ∈ s, (a * f i) ∉ (p : fractional_ideal R⁰ K) :=
begin
  obtain ⟨a', ha'⟩ := is_localization.exist_integer_multiples_of_finset' R⁰ s f,
  let I : fractional_ideal R⁰ K := ⟨submodule.span R (f '' s), a', a'.2, _⟩,
  have hI0 : I ≠ 0,
  { intro hI0,
    rw eq_zero_iff at hI0,
    specialize hI0 (f j) (submodule.subset_span (set.mem_image_of_mem f hjs)),
    contradiction },
  suffices : ↑p / I < I⁻¹,
  { obtain ⟨_, a, hI, hpI⟩ := set_like.lt_iff_le_and_exists.mp this,
    rw mem_inv_iff hI0 at hI,
    refine ⟨a, λ i hi, _, _⟩,
    { exact (mem_one_iff _).mp (hI (f i)
        (submodule.subset_span (set.mem_image_of_mem f hi))) },
    { contrapose! hpI,
      refine (mem_div_iff_of_nonzero hI0).mpr (λ y hy, submodule.span_induction hy _ _ _ _),
      { rintros _ ⟨i, hi, rfl⟩, exact hpI i hi },
      { rw mul_zero, exact submodule.zero_mem _ },
      { intros x y hx hy, rw mul_add, exact submodule.add_mem _ hx hy },
      { intros b x hx, rw mul_smul_comm, exact submodule.smul_mem _ b hx } } },
  calc ↑p / I = ↑p * I⁻¹ : div_eq_mul_inv ↑p I
          ... < 1 * I⁻¹ : mul_right_strict_mono (inv_ne_zero hI0) _
          ... = I⁻¹ : one_mul _,
  { rw [← coe_ideal_top],
    exact strict_mono_of_le_iff_le (λ _ _, (coe_ideal_le_coe_ideal K).symm)
      (lt_top_iff_ne_top.mpr hp) },
  { intros x hx,
    refine submodule.span_induction hx _ _ _ _,
    { rintro _ ⟨i, hi, rfl⟩, exact ha' i hi },
    { rw smul_zero, exact is_localization.is_integer_zero },
    { intros x y hx hy, rw smul_add, exact is_localization.is_integer_add hx hy },
    { intros c x hx, rw smul_comm, exact is_localization.is_integer_smul hx } }
end

end move_me

open_locale classical

/-- The ramification index of `P` over `p` is the largest exponent `n`
such that `p` is contained in `P^n`.

In particular, if `p` is not contained in `P^n`, then the ramification index is `0`.

If there is no largest such `n` (e.g. because `p = ⊥`),
then `ramification_idx` is defined to be `0`.
-/
noncomputable def ramification_idx : ℕ :=
if h : ∃ n, map f p ≤ P ^ n ∧ ¬ map f p ≤ P ^ (n + 1)
then nat.find h
else 0

@[simp] lemma ramification_idx_bot : ramification_idx f ⊥ P = 0 :=
dif_neg $ not_exists.mpr $ λ n hn, hn.2 (map_bot.le.trans bot_le)

@[simp] lemma ramification_idx_of_not_le (h : ¬ map f p ≤ P) : ramification_idx f p P = 0 :=
begin
  rw [ramification_idx, dif_pos, nat.find_eq_zero ⟨0, _⟩];
    rw [zero_add, pow_zero, pow_one, ideal.one_eq_top];
    exact ⟨le_top, h⟩
end

local attribute [instance] ideal.quotient.field

/-- The inertia degree of `P : ideal S` lying over `p : ideal R` is the degree of the
extension `(S / P) : (R / p)`.

We do not assume `P` lies over `p` in the definition; we return `0` instead.

See `inertia_deg_algebra_map` for the common case where `f = algebra_map R S`
and there is an algebra structure `R / p → S / P`.
-/
noncomputable def inertia_deg [hp : p.is_maximal] : ℕ :=
if hPp : comap f P = p
then @finrank p.quotient P.quotient _ _ $ @algebra.to_module _ _ _ _ $ ring_hom.to_algebra $
ideal.quotient.lift p (P^.quotient.mk^.comp f) $
λ a ha, quotient.eq_zero_iff_mem.mpr $ mem_comap.mp $ hPp.symm ▸ ha
else 0

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp] lemma inertia_deg_of_subsingleton [hp : p.is_maximal] [hQ : subsingleton P.quotient] :
  inertia_deg f p P = 0 :=
begin
  have := (ideal.quotient.subsingleton_iff _).mp hQ,
  unfreezingI { subst this },
  exact dif_neg (λ h, hp.ne_top $ h.symm.trans comap_top)
end

@[simp] lemma inertia_deg_algebra_map [algebra R S] [algebra p.quotient P.quotient]
  [is_scalar_tower R p.quotient P.quotient]
  [hp : p.is_maximal] :
  inertia_deg (algebra_map R S) p P = finrank p.quotient P.quotient :=
begin
  nontriviality P.quotient using [inertia_deg_of_subsingleton, finrank_zero_of_subsingleton],
  have := comap_eq_of_scalar_tower_quotient p P (ring_hom.injective _),
  rw [inertia_deg, dif_pos this],
  congr,
  refine algebra.algebra_ext _ _ (λ x', quotient.induction_on' x' $ λ x, _),
  change ideal.quotient.lift p _ _ (ideal.quotient.mk p x) =
    algebra_map _ _ (ideal.quotient.mk p x),
  rw [ideal.quotient.lift_mk, ← ideal.quotient.algebra_map_eq, ← is_scalar_tower.algebra_map_eq,
      ← ideal.quotient.algebra_map_eq, ← is_scalar_tower.algebra_map_apply]
end

lemma linear_independent.of_fraction_ring (R K : Type*) [integral_domain R] [field K]
  [algebra R K] [is_fraction_ring R K] {ι V : Type*}
  [add_comm_group V] [module R V] [module K V] [is_scalar_tower R K V] {b : ι → V} :
  linear_independent R b ↔ linear_independent K b :=
begin
  refine ⟨_, linear_independent.restrict_scalars (smul_left_injective R one_ne_zero)⟩,
  rw [linear_independent_iff', linear_independent_iff'],
  intros hli s g hg i hi,
  choose a g' hg' using
    is_localization.exist_integer_multiples_of_finset' (non_zero_divisors R) s g,
  refine (smul_eq_zero.mp _).resolve_left (non_zero_divisors.coe_ne_zero a),
  rw [← hg' i hi, is_fraction_ring.to_map_eq_zero_iff],
  convert hli s (λ i, if hi : i ∈ s then g' i hi else 0) _ i hi,
  { rw dif_pos hi },
  { calc _ = (a : R) • ∑ i in s, g i • b i : _
       ... = 0 : by rw [hg, smul_zero],
    rw [finset.smul_sum, finset.sum_congr rfl],
    intros i hi,
    simp only [dif_pos hi, ← smul_assoc, ← hg' i hi, is_scalar_tower.algebra_map_smul] },
end

lemma finrank_quotient_map_aux' {R S K : Type*} [integral_domain R] [is_dedekind_domain R]
  [comm_ring S] [algebra R S] (hRS : function.injective (algebra_map R S))
  [field K] [algebra R K] [is_fraction_ring R K] {ι V V' V'' : Type*}
  [add_comm_group V] [module R V] [module K V] [is_scalar_tower R K V]
  [add_comm_group V'] [module R V'] [module S V'] [is_scalar_tower R S V']
  [add_comm_group V''] [module R V''] (f : V'' →ₗ[R] V) (hf : function.injective f)
  (f' : V'' →ₗ[R] V') {b : ι → V''}
  (hb' : linear_independent S (f' ∘ b)) : linear_independent K (f ∘ b) :=
begin
  rw [← linear_independent.of_fraction_ring R K,
      f.linear_independent_iff (linear_map.ker_eq_bot.mpr hf)],
  refine linear_independent.of_comp f' (linear_independent.restrict_scalars_algebras _ hb'),
  simpa only [algebra.smul_def, mul_one] using hRS
end

lemma finrank_quotient_map_aux {R S K : Type*} [integral_domain R] [is_dedekind_domain R]
  [comm_ring S] [algebra R S] (hRS : (algebra_map R S).ker ≠ ⊤)
  [field K] [algebra R K] [is_fraction_ring R K] {ι V V' V'' : Type*}
  [add_comm_group V] [module R V] [module K V] [is_scalar_tower R K V]
  [add_comm_group V'] [module R V'] [module S V'] [is_scalar_tower R S V']
  [add_comm_group V''] [module R V''] (f : V'' →ₗ[R] V) (hf : function.injective f)
  (f' : V'' →ₗ[R] V') {b : ι → V''}
  (hb' : linear_independent S (f' ∘ b)) : linear_independent K (f ∘ b) :=
begin
  contrapose! hb' with hb,
  -- If we have a nontrivial linear dependence with coefficients `g` in `K`,
  -- then we can find a linear dependence with coefficients `I.quotient.mk g'` in `R/I`.
  obtain ⟨s, g, eq, j', hj's, hj'g⟩ := linear_dependent_iff.mp hb,
  refine linear_dependent_iff.mpr ⟨s, _⟩,
  obtain ⟨a, hag, j, hjs, hgI⟩ :=
    ideal.exist_integer_multiples_not_mem hRS s g hj's hj'g,
  choose g'' hg'' using hag,
  let g' := λ i, if h : i ∈ s then g'' i h else 0,
  have hg' : ∀ i ∈ s, algebra_map _ _ (g' i) = a * g i,
  { intros i hi, exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi) },
  have hgI : algebra_map R S (g' j) ≠ 0,
  { simp only [fractional_ideal.mem_coe_ideal, not_exists, not_and'] at hgI,
    exact hgI _ (hg' j hjs) },
  refine ⟨λ i, algebra_map R S (g' i), _, j, hjs, hgI⟩,
  have eq : f (∑ i in s, g' i • (b i)) = 0,
  { rw [linear_map.map_sum, ← smul_zero a, ← eq, finset.smul_sum, finset.sum_congr rfl],
    intros i hi,
    rw [linear_map.map_smul, ← is_scalar_tower.algebra_map_smul K, hg' i hi, ← smul_assoc,
        smul_eq_mul],
    apply_instance },
  simp only [is_scalar_tower.algebra_map_smul, ← linear_map.map_smul, ← linear_map.map_sum,
          (f.map_eq_zero_iff hf).mp eq, linear_map.map_zero],
end

lemma finrank_quotient_map [is_dedekind_domain R] (K L : Type*) [field K] [field L]
  [algebra R S] [algebra R K] [algebra S L] [algebra K L] [is_separable K L]
  [is_fraction_ring R K]
  [hp : p.is_maximal] /- [module.free R S] [module.finite R S] -/ [is_noetherian R S] :
  finrank p.quotient (map (algebra_map R S) p).quotient = finrank K L :=
begin
  let ι := module.free.choose_basis_index p.quotient (map (algebra_map R S) p).quotient,
  let b : basis ι _ _ := module.free.choose_basis p.quotient (map (algebra_map R S) p).quotient,
  let b' : ι → L := λ i, algebra_map S L (ideal.quotient.mk_surjective (b i)).some,
  have b'_li : linear_independent _ b' := _,
  have b'_sp : submodule.span _ (set.range b') = ⊤ := _,
  let c : basis ι K L := basis.mk b'_li b'_sp,
  rw [finrank_eq_card_basis b, finrank_eq_card_basis c],
  { rw eq_top_iff, rintros x -, sorry },
  { have := b.linear_independent.of_quotient p hp.ne_top (algebra.linear_map S L) _ _, }
end

/-- The **fundamental identity** of ramification index `e` and inertia degree `f`:
for all prime `P` lying over `p`, `∑ P, e P * f P = [Frac(S) : Frac(R)]`,
if `Frac(S) : Frac(R)` is a finite separable extension, `p` is maximal
and `S` is the integral closure of `R` in `L`. -/
theorem sum_ramification_inertia (K L : Type*) [field K] [field L]
  [is_dedekind_domain S]
  [algebra R S] [algebra R K] [algebra S L] [algebra K L] [is_separable K L]
  [is_fraction_ring R K] [is_fraction_ring S L]
  [p.is_maximal] :
  ∑ P in (factors (map f p)).to_finset,
    ramification_idx (algebra_map R S) p P * inertia_deg (algebra_map R S) p P =
    finrank K L :=
begin
  let φ := quotient_inf_ring_equiv_pi_quotient (λ (P : (factors (map f p)).to_finset), ↑P) _,
end

#lint
