/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.separable
import linear_algebra.free_module.finite.basic
import linear_algebra.free_module.pid
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
We will try to relax the above hypotheses as much as possible.

-/

open_locale big_operators
open_locale non_zero_divisors

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain R] [is_domain S] (f : R →+* S)
variables (p : ideal R) (P : ideal S)

open finite_dimensional
open ideal
open unique_factorization_monoid

section move_me

lemma ideal.quotient.subsingleton_iff : subsingleton (R ⧸ p) ↔ p = ⊤ :=
by rw [eq_top_iff_one, ← subsingleton_iff_zero_eq_one, eq_comm,
       ← p^.quotient.mk^.map_one, quotient.eq_zero_iff_mem]

instance ideal.noetherian_dimensional_quotient_map_quotient [algebra R S] [p.is_maximal]
  [is_noetherian R S] :
  is_noetherian (R ⧸ p) (S ⧸ map (algebra_map R S) p) :=
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


open fractional_ideal

/-- Strengthening of `is_localization.exist_integer_multiples`:
Let `p ≠ ⊤` be an ideal in a Dedekind domain `R`, and `f ≠ 0` a finite collection
of elements of `K = Frac(R)`, then we can multiply the elements of `f` by some `a : K`
to find a collection of elements of `R` that is not completely contained in `p`. -/
lemma ideal.exist_integer_multiples_not_mem
  {R K : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] [field K]
  [algebra R K] [is_fraction_ring R K]
  {p : ideal R} (hp : p ≠ ⊤) {ι : Type*} (s : finset ι) (f : ι → K)
  {j} (hjs : j ∈ s) (hjf : f j ≠ 0) :
  ∃ a : K, (∀ i ∈ s, is_localization.is_integer R (a * f i)) ∧
    ∃ i ∈ s, (a * f i) ∉ (p : fractional_ideal R⁰ K) :=
begin
  obtain ⟨a', ha'⟩ := is_localization.exist_integer_multiples R⁰ s f,
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

lemma ideal.pow_le_self {R : Type*} [comm_semiring R]
  (I : ideal R) {n : ℕ} (hn : n ≠ 0) : I^n ≤ I :=
calc I^n ≤ I ^ 1 : ideal.pow_le_pow (nat.pos_of_ne_zero hn)
     ... = I : pow_one _

namespace linear_equiv

variables {A M M₂ : Type*} [comm_ring A] [add_comm_group M] [add_comm_group M₂]
variables [module A M] [module A M₂]

/-- The dimension of a finite dimensional space is preserved under linear equivalence. -/
-- Generalizes `linear_equiv.finrank_eq`
theorem finrank_eq' (f : M ≃ₗ[A] M₂) : finrank A M = finrank A M₂ :=
by { unfold finrank, rw [← cardinal.to_nat_lift, f.lift_dim_eq, cardinal.to_nat_lift] }

end linear_equiv

@[simp] lemma submodule.mem_restrict_scalars {R S M : Type*}
  [semiring R] [semiring S] [add_comm_monoid M] [has_scalar R S] [module R M] [module S M]
  [is_scalar_tower R S M] (s : submodule S M) (x : M) :
  x ∈ s.restrict_scalars R ↔ x ∈ s := iff.rfl

@[simp] lemma linear_map.coe_restrict_scalars (R : Type*) {S M N : Type*}
  [semiring R] [semiring S] [add_comm_monoid M] [add_comm_monoid N] [module R M] [module S M]
  [module R N] [module S N] [linear_map.compatible_smul M N R S]
  (f : M →ₗ[S] N) : (f.restrict_scalars R : M → N) = f :=
rfl
.
lemma ideal.map_le_smul_top {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  (I : ideal R) (f : R →ₗ[R] M) : submodule.map f I ≤ I • (⊤ : submodule R M) :=
begin
  rintros _ ⟨y, hy, rfl⟩,
  rw [← mul_one y, ← smul_eq_mul, f.map_smul],
  exact submodule.smul_mem_smul hy submodule.mem_top
end

lemma ideal.map_smul_le_smul_top' {R : Type*} (M : Type*) [comm_ring R] [add_comm_group M] [module R M]
  (I : ideal R) (x : M) : submodule.map (linear_map.flip (linear_map.lsmul R M) x) I ≤ I • (⊤ : submodule R M) :=
begin
  rintros _ ⟨y, hy, rfl⟩,
  simpa only [linear_map.flip_apply, linear_map.lsmul_apply]
    using submodule.smul_mem_smul hy (show x ∈ ⊤, from submodule.mem_top)
end

lemma ideal.smul_top_le_map {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S] (I : ideal R) :
  I • (⊤ : submodule R S) ≤ (I.map (algebra_map R S)).restrict_scalars R :=
submodule.smul_le.mpr (λ r hr y _,
by { rw [submodule.mem_restrict_scalars, algebra.smul_def],
     exact ideal.mul_mem_right _ _ (ideal.mem_map_of_mem _ hr) })

open_locale pointwise

lemma submodule.mem_smul_span {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  {I : ideal R} {s : set M} {x : M} : x ∈ I • submodule.span R s ↔
    x ∈ submodule.span R (⋃ (a ∈ I) (b ∈ s), ({a • b} : set M)) :=
by rw [← I.span_eq, submodule.span_smul_span, I.span_eq]; refl

/-- If `x` is an `I`-multiple of the submodule spanned by `s`,
then we can write `x` as an `I`-linear combination of the elements of `s`. -/
lemma exists_sum_of_mem_ideal_smul_span {α R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  (I : ideal R) (s : set α) (f : α → M)
  (x : M) (hx : x ∈ I • submodule.span R (f '' s)) :
  ∃ (a : s →₀ R) (ha : ∀ i, a i ∈ I), a.sum (λ i c, c • f i) = x :=
begin
  refine submodule.span_induction (submodule.mem_smul_span.mp hx) _ _ _ _,
  { simp only [set.mem_Union, set.mem_range, set.mem_singleton_iff],
    rintros x ⟨y, hy, x, ⟨i, hi, rfl⟩, rfl⟩,
    refine ⟨finsupp.single ⟨i, hi⟩ y, λ j, _, _⟩,
    { letI := classical.dec_eq s,
      rw finsupp.single_apply, split_ifs, { assumption }, { exact I.zero_mem } },
    refine @finsupp.sum_single_index s R M _ _ ⟨i, hi⟩ _ (λ i y, y • f i) _,
    simp },
  { exact ⟨0, λ i, I.zero_mem, finsupp.sum_zero_index⟩ },
  { rintros x y ⟨ax, hax, rfl⟩ ⟨ay, hay, rfl⟩,
    refine ⟨ax + ay, λ i, I.add_mem (hax i) (hay i), finsupp.sum_add_index _ _⟩;
      intros; simp only [zero_smul, add_smul] },
  { rintros c x ⟨a, ha, rfl⟩,
    refine ⟨c • a, λ i, I.mul_mem_left c (ha i), _⟩,
    rw [finsupp.sum_smul_index, finsupp.smul_sum];
      intros; simp only [zero_smul, mul_smul] },
end

@[simp] lemma submodule.smul_comap_le_comap_smul {R M N : Type*} [comm_ring R] [add_comm_group M]
  [module R M] [add_comm_group N] [module R N]
  (f : M →ₗ[R] N) (S : submodule R N) (I : ideal R) :
  I • S.comap f ≤ (I • S).comap f :=
begin
  refine (submodule.smul_le.mpr (λ r hr x hx, _)),
  rw [submodule.mem_comap] at ⊢ hx,
  rw f.map_smul,
  exact submodule.smul_mem_smul hr hx
end

@[simp] lemma submodule.restrict_scalars_eq_top {R A M : Type*} [comm_semiring R] [semiring A]
  [add_comm_monoid M] [algebra R A] [module R M] [module A M] [is_scalar_tower R A M]
  {S : submodule A M} : S.restrict_scalars R = ⊤ ↔ S = ⊤ :=
by simp [set_like.ext_iff]

open_locale matrix

lemma zero_hom_class.ne_zero_of_map {R S F : Type*} [has_zero R] [has_zero S]
  [zero_hom_class F R S] {f : F} {x : R} (hx : f x ≠ 0) : x ≠ 0 :=
mt (λ h, show f x = 0, from h.symm ▸ map_zero f) hx

@[to_additive]
lemma map_ne_one {R S F : Type*} [has_one R] [has_one S] [one_hom_class F R S] (f : F) {x : R}
  (hx : f x ≠ 1) : x ≠ 1 :=
λ h, hx (h.symm ▸ map_one f)

@[to_additive]
lemma map_ne_one_iff {R S F : Type*} [has_one R] [has_one S] [one_hom_class F R S]
  (f : F) (hf : function.injective f) {x : R} :
  f x ≠ 1 ↔ x ≠ 1 :=
not_iff_not.mpr (map_eq_one_iff f hf)

@[simp] lemma _root_.matrix.det_neg {R n : Type*} [comm_ring R] [decidable_eq n] [fintype n]
  (M : matrix n n R) : (-M).det = (-1) ^ fintype.card n * M.det :=
calc (-M).det = ((-1 : R) • M).det : by rw [neg_smul, one_smul]
          ... = (-1 : R) ^ fintype.card n * M.det : matrix.det_smul _ _

end move_me

section dec_eq

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
then @finrank (R ⧸ p) (S ⧸ P) _ _ $ @algebra.to_module _ _ _ _ $ ring_hom.to_algebra $
ideal.quotient.lift p (P^.quotient.mk^.comp f) $
λ a ha, quotient.eq_zero_iff_mem.mpr $ mem_comap.mp $ hPp.symm ▸ ha
else 0

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp] lemma inertia_deg_of_subsingleton [hp : p.is_maximal] [hQ : subsingleton (S ⧸ P)] :
  inertia_deg f p P = 0 :=
begin
  have := (ideal.quotient.subsingleton_iff _).mp hQ,
  unfreezingI { subst this },
  exact dif_neg (λ h, hp.ne_top $ h.symm.trans comap_top)
end

@[simp] lemma inertia_deg_algebra_map [algebra R S] [algebra (R ⧸ p) (S ⧸ P)]
  [is_scalar_tower R (R ⧸ p) (S ⧸ P)]
  [hp : p.is_maximal] :
  inertia_deg (algebra_map R S) p P = finrank (R ⧸ p) (S ⧸ P) :=
begin
  nontriviality (S ⧸ P) using [inertia_deg_of_subsingleton, finrank_zero_of_subsingleton],
  have := comap_eq_of_scalar_tower_quotient (algebra_map (R ⧸ p) (S ⧸ P)).injective,
  rw [inertia_deg, dif_pos this],
  congr,
  refine algebra.algebra_ext _ _ (λ x', quotient.induction_on' x' $ λ x, _),
  change ideal.quotient.lift p _ _ (ideal.quotient.mk p x) =
    algebra_map _ _ (ideal.quotient.mk p x),
  rw [ideal.quotient.lift_mk, ← ideal.quotient.algebra_map_eq, ← is_scalar_tower.algebra_map_eq,
      ← ideal.quotient.algebra_map_eq, ← is_scalar_tower.algebra_map_apply]
end

end dec_eq

lemma linear_independent.of_fraction_ring (R K : Type*) [comm_ring R] [nontrivial R] [field K]
  [algebra R K] [is_fraction_ring R K] {ι V : Type*}
  [add_comm_group V] [module R V] [module K V] [is_scalar_tower R K V] {b : ι → V} :
  linear_independent R b ↔ linear_independent K b :=
begin
  refine ⟨_, linear_independent.restrict_scalars (smul_left_injective R one_ne_zero)⟩,
  rw [linear_independent_iff', linear_independent_iff'],
  intros hli s g hg i hi,
  choose a g' hg' using
    is_localization.exist_integer_multiples (non_zero_divisors R) s g,
  refine (smul_eq_zero.mp _).resolve_left (non_zero_divisors.coe_ne_zero a),
  rw [← hg' i hi, is_fraction_ring.to_map_eq_zero_iff],
  letI := classical.prop_decidable,
  convert hli s (λ i, if hi : i ∈ s then g' i hi else 0) _ i hi,
  { rw dif_pos hi },
  { calc _ = (a : R) • ∑ i in s, g i • b i : _
       ... = 0 : by rw [hg, smul_zero],
    rw [finset.smul_sum, finset.sum_congr rfl],
    intros i hi,
    simp only [dif_pos hi, ← smul_assoc, ← hg' i hi, is_scalar_tower.algebra_map_smul] },
end

-- TODO: generalize?
lemma finrank_quotient_map.linear_independent_of_injective
  {R S K : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R]
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
  simpa only [algebra.smul_def, mul_one] using hRS,
  { apply_instance }
end

-- TODO: generalize?
lemma finrank_quotient_map.linear_independent_of_nontrivial
  {R S K : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R]
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
  simp only [linear_independent_iff', not_forall] at hb ⊢,
  obtain ⟨s, g, eq, j', hj's, hj'g⟩ := hb,
  refine ⟨s, _⟩,
  obtain ⟨a, hag, j, hjs, hgI⟩ :=
    ideal.exist_integer_multiples_not_mem hRS s g hj's hj'g,
  choose g'' hg'' using hag,
  letI := classical.prop_decidable,
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

lemma map_mem_span_algebra_map_image {R A B : Type*} [comm_ring R] [comm_ring A] [comm_ring B]
  [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B]
  (x : A) (a : set A) (hx : x ∈ submodule.span R a) :
  algebra_map A B x ∈ submodule.span R (algebra_map A B '' a) :=
begin
  rw [← algebra.coe_linear_map, ← linear_map.coe_restrict_scalars R, ← submodule.map_span],
  exact submodule.mem_map_of_mem hx,
  all_goals { apply_instance }
end

lemma is_localization.mem_span_iff {R K M : Type*} [comm_ring R] [comm_ring K] [add_comm_group M]
  [algebra R K] [module R M] [module K M] [is_scalar_tower R K M]
  (S : submonoid R) [is_localization S K] {x : M} {a : set M} :
  x ∈ submodule.span K a ↔
    ∃ (y ∈ submodule.span R a) (z : S), x = is_localization.mk' K 1 z • y :=
begin
  split, intro h,
  { refine submodule.span_induction h _ _ _ _,
    { rintros x hx,
      exact ⟨x, submodule.subset_span hx, 1, by rw [is_localization.mk'_one, map_one, one_smul]⟩ },
    { exact ⟨0, submodule.zero_mem _, 1, by rw [is_localization.mk'_one, map_one, one_smul]⟩ },
    { rintros _ _ ⟨y, hy, z, rfl⟩ ⟨y', hy', z', rfl⟩,
      refine ⟨(z' : R) • y + (z : R) • y',
        (submodule.add_mem _ (submodule.smul_mem _ _ hy) (submodule.smul_mem _ _ hy')), z * z', _⟩,
      rw [smul_add, ← is_scalar_tower.algebra_map_smul K (z : R),
          ← is_scalar_tower.algebra_map_smul K (z' : R), smul_smul, smul_smul],
      congr' 1,
      { rw [← mul_one (1 : R), is_localization.mk'_mul, mul_assoc, is_localization.mk'_spec,
            map_one, mul_one, mul_one] },
      { rw [← mul_one (1 : R), is_localization.mk'_mul, mul_right_comm, is_localization.mk'_spec,
            map_one, mul_one, one_mul] },
      all_goals { apply_instance } },
    { rintros a _ ⟨y, hy, z, rfl⟩,
      obtain ⟨y', z', rfl⟩ := is_localization.mk'_surjective S a,
      refine ⟨y' • y, submodule.smul_mem _ _ hy, z' * z, _⟩,
      rw [← is_scalar_tower.algebra_map_smul K y', smul_smul, ← is_localization.mk'_mul,
          smul_smul, mul_comm (is_localization.mk' K _ _), is_localization.mul_mk'_eq_mk'_of_mul],
      all_goals { apply_instance } } },
  { rintro ⟨y, hy, z, rfl⟩,
    exact submodule.smul_mem _ _ (submodule.span_subset_span R K _ hy) }
end

lemma is_localization.mem_span_map {R K : Type*} [comm_ring R] [comm_ring K]
  [algebra R K] (S : submonoid R) [is_localization S K] {x : K} {a : set R} :
  x ∈ ideal.span (algebra_map R K '' a) ↔
    ∃ (y ∈ ideal.span a) (z : S), x = is_localization.mk' K y z :=
begin
  refine (is_localization.mem_span_iff S).trans _,
  split,
  { rw ← is_localization.coe_submodule_span,
    rintros ⟨_, ⟨y, hy, rfl⟩, z, hz⟩,
    refine ⟨y, hy, z, _⟩,
    rw [hz, algebra.linear_map_apply, smul_eq_mul, mul_comm, is_localization.mul_mk'_eq_mk'_of_mul,
        mul_one] },
  { rintros ⟨y, hy, z, hz⟩,
    refine ⟨algebra_map R K y, _, z, _⟩,
    { exact map_mem_span_algebra_map_image _ _ hy },
    rw [hz, smul_eq_mul, mul_comm, is_localization.mul_mk'_eq_mk'_of_mul,
        mul_one] },
end

/-- If the `S`-multiples of `a` are contained in some `R`-span, then `Frac(S)`-multiples of `a`
are contained in the equivalent `Frac(R)`-span. -/
lemma is_fraction_ring.ideal_span_singleton_subset (R : Type*) {S K L : Type*}
  [comm_ring R] [comm_ring S] [is_domain R] [is_domain S] [field K] [field L]
  [algebra R K] [algebra R S] [algebra R L] [algebra S L] [is_integral_closure S R L]
  [is_fraction_ring S L] [algebra K L] [is_scalar_tower R S L] [is_scalar_tower R K L]
  {a : S} {b : set S} (alg : algebra.is_algebraic R L) (inj : function.injective (algebra_map R L))
  (h : (ideal.span ({a} : set S) : set S) ⊆ submodule.span R b) :
  (ideal.span ({algebra_map S L a} : set L) : set L) ⊆ submodule.span K (algebra_map S L '' b) :=
begin
  intros x hx,
  obtain ⟨x', rfl⟩ := ideal.mem_span_singleton.mp hx,
  obtain ⟨y', z', rfl⟩ := is_localization.mk'_surjective (S⁰) x',
  obtain ⟨y, z, hz0, yz_eq⟩ := is_integral_closure.exists_smul_eq_mul alg inj y'
    (non_zero_divisors.coe_ne_zero z'),
  have injRS : function.injective (algebra_map R S),
  { refine function.injective.of_comp
      (show function.injective (algebra_map S L ∘ algebra_map R S), from _),
    rwa [← ring_hom.coe_comp, ← is_scalar_tower.algebra_map_eq] },
  have hz0' : algebra_map R S z ∈ S⁰ := map_mem_non_zero_divisors (algebra_map R S) injRS
    (mem_non_zero_divisors_of_ne_zero hz0),
  have mk_yz_eq : is_localization.mk' L y' z' = is_localization.mk' L y ⟨_, hz0'⟩,
  { rw [algebra.smul_def, mul_comm _ y, mul_comm _ y', ← set_like.coe_mk (algebra_map R S z) hz0']
        at yz_eq,
    exact is_localization.mk'_eq_of_eq yz_eq.symm },
  suffices hy : algebra_map S L (a * y) ∈ submodule.span K (⇑(algebra_map S L) '' b),
  { rw [mk_yz_eq, is_fraction_ring.mk'_eq_div, set_like.coe_mk,
        ← is_scalar_tower.algebra_map_apply, is_scalar_tower.algebra_map_apply R K L,
        div_eq_mul_inv, ← mul_assoc, mul_comm, ← ring_hom.map_inv, ← algebra.smul_def,
        ← _root_.map_mul],
    exact (submodule.span K _).smul_mem _ hy },
  refine submodule.span_subset_span R K _ (map_mem_span_algebra_map_image _ _ _),
  exact h (ideal.mem_span_singleton.mpr ⟨y, rfl⟩)
end

open_locale matrix

/-- If `b` mod `p` spans `S/p` as `R/p`-space, then `b` itself spans `Frac(S)` as `Frac(R)`-space.
-/
lemma finrank_quotient_map.span_eq_top {K L : Type*} [field K] [field L]
  [algebra R K]
  [algebra R S] [algebra S L] [is_fraction_ring S L] [algebra K L] [is_noetherian R S]
  [algebra R L] [is_scalar_tower R S L] [is_scalar_tower R K L]
  [is_integral_closure S R L]
  (hRL : function.injective (algebra_map R L)) (hp : p ≠ ⊤)
  (b : set S) (hb' : submodule.span R b ⊔ submodule.map (algebra.linear_map R S) p = ⊤) :
  submodule.span K (algebra_map S L '' b) = ⊤ :=
begin
  -- Let `M` be the `R`-module spanned by the proposed basis elements.
  set M : submodule R S := submodule.span R b with hM,
  -- Then `S / M` is generated by some finite set of `n` vectors `a`.
  letI h : module.finite R (S ⧸ M) :=
    module.finite.of_surjective (submodule.mkq _) (submodule.quotient.mk_surjective _),
  obtain ⟨n, a, ha⟩ := @@module.finite.exists_fin _ _ _ h,
  -- Because the image of `p` in `S / M` is `⊤`,
  -- we can write the elements of `a` as `p`-linear combinations of other elements of `a`.
  have exists_sum : ∀ x : (S ⧸ M), ∃ a' : fin n → R, (∀ i, a' i ∈ p) ∧ ∑ i, a' i • a i = x,
  { intro x,
    obtain ⟨a'', ha'', hx⟩ := exists_sum_of_mem_ideal_smul_span p set.univ a x _,
    refine ⟨λ i, a'' ⟨i, set.mem_univ _⟩, λ i, ha'' _, _⟩,
    rwa [finsupp.sum_fintype, fintype.sum_equiv (equiv.set.univ (fin n))] at hx,
    { intros, simp only [eq_self_iff_true, subtype.coe_eta, equiv.set.univ_apply] },
    { intros, simp only [zero_smul] },
    suffices : p • (⊤ : submodule R (S ⧸ M)) = ⊤,
    { rw [set.image_univ, ha, this],
      exact submodule.mem_top },
    refine top_le_iff.mp ((top_le_iff.mpr _).trans $
      ideal.map_le_smul_top p (submodule.mkq M ∘ₗ algebra.linear_map R S)),
    rwa [submodule.map_comp, submodule.map_mkq_eq_top] },
  choose A' hA'p hA' using λ i, exists_sum (a i),
  -- This gives us a(n invertible) matrix `A` such that `det A ∈ M = span R b`,
  let A : matrix (fin n) (fin n) R := A' - 1,
  let B := A.adjugate,
  have A_smul : ∀ i, ∑ j, A i j • a j = 0,
  { intros,
    simp only [A, pi.sub_apply, sub_smul, finset.sum_sub_distrib, hA', matrix.one_apply, ite_smul,
      one_smul, zero_smul, finset.sum_ite_eq, finset.mem_univ, if_true, sub_self] },
  -- since `span S {det A} / M = 0`.
  have d_smul : ∀ i, A.det • a i = 0,
  { intro i,
    calc A.det • a i = ∑ j, (B ⬝ A) i j • a j : _
                 ... = ∑ k, B i k • ∑ j, (A k j • a j) : _
                 ... = 0 : finset.sum_eq_zero (λ k _, _),
    { simp only [matrix.adjugate_mul, pi.smul_apply, matrix.one_apply, mul_ite, ite_smul,
        smul_eq_mul, mul_one, mul_zero, one_smul, zero_smul, finset.sum_ite_eq, finset.mem_univ,
        if_true] },
    { simp only [matrix.mul_apply, finset.smul_sum, finset.sum_smul, smul_smul],
      rw finset.sum_comm },
    { rw [A_smul, smul_zero] } },
  -- In the rings of integers we have the desired inclusion.
  have span_d : (submodule.span S ({algebra_map R S A.det} : set S)).restrict_scalars R ≤ M,
  { intros x hx,
    rw submodule.mem_restrict_scalars at hx,
    obtain ⟨x', rfl⟩ := submodule.mem_span_singleton.mp hx,
    rw [smul_eq_mul, mul_comm, ← algebra.smul_def] at ⊢ hx,
    rw [← submodule.quotient.mk_eq_zero, submodule.quotient.mk_smul],
    obtain ⟨a', _, quot_x_eq⟩ := exists_sum (submodule.quotient.mk x'),
    simp_rw [← quot_x_eq, finset.smul_sum, smul_comm A.det, d_smul, smul_zero,
      finset.sum_const_zero] },
  -- So now we lift everything to the fraction field.
  refine top_le_iff.mp (calc ⊤ = (ideal.span {algebra_map R L A.det}).restrict_scalars K : _
                           ... ≤ submodule.span K (algebra_map S L '' b) : _),
  -- Because `det A ≠ 0`, we have `span L {det A} = ⊤`.
  { rw [eq_comm, submodule.restrict_scalars_eq_top, ideal.span_singleton_eq_top],
    refine is_unit.mk0 _ ((map_ne_zero_iff ((algebra_map R L)) hRL).mpr
      (map_ne_zero (ideal.quotient.mk p) _)),
    haveI := ideal.quotient.nontrivial hp,
    calc ideal.quotient.mk p (A.det)
          = matrix.det ((ideal.quotient.mk p).map_matrix A) :
        by rw [ring_hom.map_det, ring_hom.map_matrix_apply]
      ... = matrix.det ((ideal.quotient.mk p).map_matrix (A' - 1)) : rfl
      ... = matrix.det (λ i j, (ideal.quotient.mk p) (A' i j) -
              (1 : matrix (fin n) (fin n) (R ⧸ p)) i j) : _
      ... = matrix.det (-1 : matrix (fin n) (fin n) (R ⧸ p)) : _
      ... = (-1 : R ⧸ p) ^ n : by rw [matrix.det_neg, fintype.card_fin, matrix.det_one, mul_one]
      ... ≠ 0 : is_unit.ne_zero (is_unit_one.neg.pow _),
    { refine congr_arg matrix.det (matrix.ext (λ i j, _)),
      rw [map_sub, ring_hom.map_matrix_apply, map_one],
      refl },
    { refine congr_arg matrix.det (matrix.ext (λ i j, _)),
      rw [ideal.quotient.eq_zero_iff_mem.mpr (hA'p i j), zero_sub],
      refl } },
  -- And we conclude `L = span L {det A} ≤ span K b`, so `span K b` spans everything.
  { intros x hx,
    rw [submodule.mem_restrict_scalars, is_scalar_tower.algebra_map_apply R S L] at hx,
    refine is_fraction_ring.ideal_span_singleton_subset R _ hRL span_d hx,
    haveI : no_zero_smul_divisors R L := no_zero_smul_divisors.of_algebra_map_injective hRL,
    rw ← is_fraction_ring.is_algebraic_iff' R S,
    intros x,
    exact is_integral.is_algebraic _ (is_integral_of_noetherian infer_instance _) },
end

.

lemma algebra.span_eq_span_of_surjective {R A M : Type*} [comm_semiring R] [semiring A]
  [add_comm_monoid M]
  [algebra R A] [module A M] [module R M] [is_scalar_tower R A M]
  (h : function.surjective (algebra_map R A)) (s : set M) :
  (submodule.span A s).restrict_scalars R = submodule.span R s :=
begin
  refine le_antisymm (λ x hx, _) (submodule.span_subset_span _ _ _),
  refine submodule.span_induction hx _ _ _ _,
  { exact λ x hx, submodule.subset_span hx },
  { exact submodule.zero_mem _ },
  { exact λ x y, submodule.add_mem _ },
  { intros c x hx,
    obtain ⟨c', rfl⟩ := h c,
    rw is_scalar_tower.algebra_map_smul,
    exact submodule.smul_mem _ _ hx },
end

lemma algebra.coe_span_eq_span_of_surjective {R A M : Type*} [comm_semiring R] [semiring A]
  [add_comm_monoid M]
  [algebra R A] [module A M] [module R M] [is_scalar_tower R A M]
  (h : function.surjective (algebra_map R A)) (s : set M) :
  (submodule.span A s : set M) = submodule.span R s :=
congr_arg coe (algebra.span_eq_span_of_surjective h s)

/-- If `p` is a maximal ideal of `R`, and `R` is contained in `S`,
then the dimension `[S/pS : R/p]` is equal to `[Frac(S) : Frac(R)]`. -/
lemma finrank_quotient_map [is_dedekind_domain R] (K L : Type*) [field K] [field L]
  [algebra R S] [algebra R K] [algebra S L] [algebra K L] [is_separable K L]
  [algebra R L] [is_scalar_tower R K L] [is_scalar_tower R S L] [is_integral_closure S R L]
  [is_fraction_ring R K] [is_fraction_ring S L]
  (hRL : function.injective (algebra_map R L))
  [hp : p.is_maximal] [module.free R S] [is_noetherian R S] :
  finrank (R ⧸ p) (S ⧸ map (algebra_map R S) p) = finrank K L :=
begin
  letI : field (R ⧸ p) := ideal.quotient.field _,
  let ι := module.free.choose_basis_index (R ⧸ p) (S ⧸ map (algebra_map R S) p),
  let b : basis ι _ _ := module.free.choose_basis (R ⧸ p) (S ⧸ map (algebra_map R S) p),
  let b' : ι → S := λ i, (ideal.quotient.mk_surjective (b i)).some,
  have b_eq_b' : ⇑ b = (submodule.mkq _).restrict_scalars R ∘ b' :=
    funext (λ i, (ideal.quotient.mk_surjective (b i)).some_spec.symm),
  let b'' : ι → L := algebra_map S L ∘ b',
  have b''_li : linear_independent _ b'' := _,
  have b''_sp : submodule.span _ (set.range b'') = ⊤ := _,
  let c : basis ι K L := basis.mk b''_li b''_sp,
  rw [finrank_eq_card_basis b, finrank_eq_card_basis c],
  { rw set.range_comp,
    refine finrank_quotient_map.span_eq_top p hRL hp.ne_top _ _,
    suffices : submodule.span R (set.range b') ⊔ (p.map (algebra_map R S)).restrict_scalars R = ⊤,
    { rw [← top_le_iff, ← this],
      refine sup_le_sup_left _ _,
      },
    rw [← submodule.ker_mkq (submodule.map (algebra.linear_map R S) p), ← top_le_iff,
        ← linear_map.map_le_map_iff, submodule.map_top, submodule.range_mkq, submodule.map_span,
        top_le_iff, submodule.eq_top_iff'],
    rintros ⟨x, hx⟩,
    convert submodule.eq_top_iff'.mp b.span_eq x,
    rw [b_eq_b', set.range_comp, linear_map.coe_restrict_scalars] at this },
  { have := b.linear_independent, rw b_eq_b' at this,
    convert finrank_quotient_map.linear_independent_of_nontrivial _
      ((algebra.linear_map S L).restrict_scalars R) _
      ((submodule.mkq _).restrict_scalars R)
      this,
    { rw [quotient.algebra_map_eq, ideal.mk_ker], exact hp.ne_top },
    { apply_instance }, { apply_instance }, { apply_instance },
    exact is_fraction_ring.injective S L },
end

#exit

lemma ideal.pow_succ_lt [is_dedekind_domain S]
  (P : ideal S) (hP0 : P ≠ ⊥) [hP : P.is_prime] (e : ℕ) : P^(e+1) < P^e :=
ideal.dvd_not_unit_iff_lt.mp
⟨pow_ne_zero _ hP0, P, ((ideal.prime_iff_is_prime hP0).mpr hP).not_unit, pow_succ' P e⟩

lemma exists_mem_pow_not_mem_pow_succ [is_dedekind_domain S]
  (P : ideal S) (hP0 : P ≠ ⊥) [P.is_prime] (e : ℕ) : ∃ x ∈ P^e, x ∉ P^(e+1) :=
set_like.exists_of_lt (P.pow_succ_lt hP0 e)

lemma submodule.sub_mem_iff_left {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (N : submodule R M) {x y : M} (hy : y ∈ N) : (x - y) ∈ N ↔ x ∈ N :=
by rw [sub_eq_add_neg, N.add_mem_iff_left (N.neg_mem hy)]

lemma submodule.sub_mem_iff_right {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (N : submodule R M) {x y : M} (hx : x ∈ N) : (x - y) ∈ N ↔ y ∈ N :=
by rw [sub_eq_add_neg, N.add_mem_iff_right hx, N.neg_mem_iff]

section

open function

/-- (Non-uniquely) push forward the action of `R` on `M` along a surjective map `f : R → S`. -/
@[reducible]
noncomputable def function.surjective.has_scalar_left {R S M : Type*} [has_scalar R M]
  {f : R → S} (hf : function.surjective f) : has_scalar S M :=
⟨λ c x, function.surj_inv hf c • x⟩

/-- Let `M` be an `R`-module, then a surjective map `f : R →+* S` induces an
`S`-module structure on `M`, if the kernel of `f` are zero-smul-divisors.

See also `function.surjective.module_left` if you want more control over the definition of `(•)`,
and `function.surjective.module_left'_of_ring` if `R` and `S` have inverses.
-/
@[reducible]
noncomputable def function.surjective.module_left' {R S M : Type*}
  [comm_semiring R] [add_comm_monoid M] [module R M] [semiring S]
  {f : R →+* S} (hf : function.surjective f)
  (hsmul : ∀ {a b}, f a = f b → ∀ (x : M), a • x = b • x) :
  module S M :=
let scalar : has_scalar S M := hf.has_scalar_left in
{ smul := @@has_scalar.smul scalar,
  .. @@function.surjective.module_left _ _ _ _ scalar f hf
    (λ c (x : M), hsmul (surj_inv_eq _ _) x) }

lemma function.surjective.module_left'_smul {R S M : Type*}
  [comm_semiring R] [add_comm_monoid M] [module R M] [semiring S]
  {f : R →+* S} (hf : function.surjective f)
  (hsmul : ∀ {a b}, f a = f b → ∀ (x : M), a • x = b • x) (c : R) (x : M) :
  by { letI := hf.module_left' @hsmul, exact f c • x } = c • x :=
hsmul (surj_inv_eq hf _) _

/-- Let `M` be an `R`-module, then a surjective map `f : R →+* S` induces an
`S`-module structure on `M`, if the kernel of `f` are zero-smul-divisors.

See also `function.surjective.module_left` if you want more control over the definition of `(•)`,
and `function.surjective.module_left'` if `R` and `S` don't have inverses.
-/
@[reducible]
noncomputable def function.surjective.module_left'_of_ring {R S M : Type*} [comm_ring R]
  [add_comm_group M] [module R M] [ring S]
  {f : R →+* S} (hf : function.surjective f) (hsmul : f.ker ≤ (linear_map.lsmul R M).ker) :
  module S M :=
hf.module_left' $ λ a b hab, begin
  suffices : linear_map.lsmul R M a = linear_map.lsmul R M b,
  { intros, simp only [← linear_map.lsmul_apply, this] },
  rw [← sub_eq_zero, ← linear_map.map_sub, ← linear_map.mem_ker],
  rw [← sub_eq_zero, ← ring_hom.map_sub, ← ring_hom.mem_ker] at hab,
  exact hsmul hab
end

lemma function.surjective.module_left'_of_ring_smul {R S M : Type*} [comm_ring R]
  [add_comm_group M] [module R M] [ring S]
  {f : R →+* S} (hf : function.surjective f) (hsmul : f.ker ≤ (linear_map.lsmul R M).ker)
  (c : R) (x : M) :
  by { letI := hf.module_left'_of_ring hsmul, exact f c • x } = c • x :=
hf.module_left'_smul _ _ _

end

variables [hfp : fact (p ≤ comap f P)]
include hfp

/-- If `P` lies over `p`, then `R / p` has a canonical map to `S / P`. -/
instance ideal.quotient.algebra_quotient_of_fact_le_comap :
  algebra (R ⧸ p) (S ⧸ P) :=
quotient.algebra_quotient_of_le_comap (fact.out (p ≤ comap f P))

@[simp] lemma ideal.quotient.algebra_map_quotient_of_fact_le_comap (x : R) :
  algebra_map (R ⧸ p) (S ⧸ P) (ideal.quotient.mk p x) = ideal.quotient.mk _ (f x) :=
rfl

@[simp] lemma quotient.mk_smul_mk_quotient_map_quotient (x : R) (y : S) :
  ideal.quotient.mk p x • ideal.quotient.mk P y = ideal.quotient.mk _ (f x * y) :=
rfl

omit hfp

@[simp] lemma map_quotient_mk_self {R : Type*} [comm_ring R] (I : ideal R) :
  map (ideal.quotient.mk I) I = ⊥ :=
by simp only [eq_bot_iff, ideal.map_le_iff_le_comap, ← ring_hom.ker_eq_comap_bot,
  ideal.mk_ker, le_refl]

variables (e : ℕ) [hfPe : fact (p ≤ comap f (P^e))]
include hfPe

/-- The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`. -/
@[simps]
def pow_quot_succ_inclusion (i : ℕ) :
  ideal.map (P^e)^.quotient.mk (P ^ (i + 1)) →ₗ[R ⧸ p] ideal.map (P^e)^.quotient.mk (P ^ i) :=
{ to_fun := λ x, ⟨x, ideal.map_mono (ideal.pow_le_pow i.le_succ) x.2⟩,
  map_add' := λ x y, rfl,
  map_smul' := λ c x, rfl }

lemma pow_quot_succ_inclusion_injective (i : ℕ) :
  function.injective (pow_quot_succ_inclusion f p P e i) :=
begin
  rw [← linear_map.ker_eq_bot, linear_map.ker_eq_bot'],
  rintro ⟨x, hx⟩ hx0,
  rw subtype.ext_iff at hx0 ⊢,
  rwa pow_quot_succ_inclusion_apply_coe at hx0
end

.

instance [fact (e ≠ 0)] : fact (p ≤ comap f P) :=
⟨(fact.out $ p ≤ comap f (P^e)).trans (comap_mono (ideal.pow_le_self _ (fact.out _)))⟩

omit hfPe

/-- Promote a surjective ring homomorphism to an equivalence by dividing out its kernel. -/
noncomputable def ideal.lift_equiv {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
  (hf : function.surjective f)
  (I : ideal R) (h : f.ker = I) : (R ⧸ I) ≃+* S :=
ring_equiv.of_bijective (ideal.quotient.lift I f (λ x hx, f.mem_ker.mp (h.symm ▸ hx))) begin
  split,
  { rintro ⟨x⟩ ⟨y⟩ hxy,
    simp only [submodule.quotient.quot_mk_eq_mk, ideal.quotient.mk_eq_mk] at *,
    suffices : x - y ∈ I, { simpa only [ideal.quotient.eq, h] using this },
    have : f (x - y) = 0, { simpa only [map_sub, sub_eq_zero] using hxy },
    exact h ▸ f.mem_ker.mp this },
  { intro y,
    obtain ⟨x, hx⟩ := hf y,
    use ideal.quotient.mk I x,
    simpa using hx },
end

/-- Promote a surjective linear map to an equivalence by dividing out its kernel. -/
noncomputable def submodule.lift_equiv {R S M N : Type*} [comm_ring R] [comm_ring S]
  [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  [module S N]
  (f : M →ₗ[R] N) (hf : function.surjective f)
  (p : submodule R M) (h : f.ker = p) : (M ⧸ p) ≃ₗ[R] N :=
linear_equiv.of_bijective (p.liftq f h.ge)
  (by { rintro ⟨x⟩ ⟨y⟩ hxy, simp only [submodule.quotient.quot_mk_eq_mk] at *,
        suffices : x - y ∈ p, { simpa only [submodule.quotient.eq, h] using this },
        have : f (x - y) = 0, { simpa only [map_sub, sub_eq_zero] using hxy },
        exact h ▸ linear_map.mem_ker.mp this })
  (by { intro y, obtain ⟨x, hx⟩ := hf y, use p.mkq x, simpa using hx })

include hfPe

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`.

See `quotient_to_quotient_range_pow_quot_succ` for this as a linear map,
and `quotient_range_pow_quot_succ_inclusion_equiv` for this as a linear equivalence.
-/
def quotient_to_quotient_range_pow_quot_succ_aux (i : ℕ) (a : S) (a_mem : a ∈ P^i) :
  S ⧸ P → (_ ⧸ (pow_quot_succ_inclusion f p P e i).range) :=
quotient.map' (λ (x : S), ⟨_, ideal.mem_map_of_mem _ (ideal.mul_mem_left _ x a_mem)⟩)
  (λ x y (h : x - y ∈ P), show _ - _ ∈ _, begin
    simp only [_root_.map_mul, linear_map.mem_range],
    refine ⟨⟨_, ideal.mem_map_of_mem _ (ideal.mul_mem_mul h a_mem)⟩, _⟩,
    ext,
    rw [pow_quot_succ_inclusion_apply_coe, subtype.coe_mk, submodule.coe_sub, subtype.coe_mk,
        subtype.coe_mk, _root_.map_mul, map_sub, sub_mul]
  end)

lemma quotient_to_quotient_range_pow_quot_succ_aux_mk (i : ℕ) (a : S) (a_mem : a ∈ P^i) (x : S) :
  quotient_to_quotient_range_pow_quot_succ_aux f p P e i a a_mem (submodule.quotient.mk x) =
    submodule.quotient.mk ⟨_, ideal.mem_map_of_mem _ (ideal.mul_mem_left _ x a_mem)⟩ :=
by apply quotient.map'_mk'

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`. -/
def quotient_to_quotient_range_pow_quot_succ [fact (e ≠ 0)] (i : ℕ) (a : S) (a_mem : a ∈ P^i) :
  S ⧸ P →ₗ[R ⧸ p] (_ ⧸ (pow_quot_succ_inclusion f p P e i).range) :=
{ to_fun := quotient_to_quotient_range_pow_quot_succ_aux f p P e i a a_mem, map_add' := begin
  intros x y, refine quotient.induction_on' x (λ x, quotient.induction_on' y (λ y, _)),
  simp only [submodule.quotient.mk'_eq_mk, ← submodule.quotient.mk_add,
             quotient_to_quotient_range_pow_quot_succ_aux_mk, add_mul],
  refine congr_arg submodule.quotient.mk _,
  ext,
  refl
end, map_smul' := begin
  intros x y, refine quotient.induction_on' x (λ x, quotient.induction_on' y (λ y, _)),
  simp only [submodule.quotient.mk'_eq_mk, ← submodule.quotient.mk_add,
             quotient_to_quotient_range_pow_quot_succ_aux_mk, ring_hom.id_apply],
  refine congr_arg submodule.quotient.mk _,
  ext,
  simp only [subtype.coe_mk, _root_.map_mul, algebra.smul_def, submodule.coe_mk, mul_assoc,
             ideal.quotient.mk_eq_mk, submodule.coe_smul_of_tower,
             ideal.quotient.algebra_map_quotient_of_fact_le_comap]
end }

.

lemma quotient_to_quotient_range_pow_quot_succ_mk [is_dedekind_domain S] [fact (e ≠ 0)]
  [P.is_prime] (i : ℕ) (a : S) (a_mem : a ∈ P^i) (x : S) :
  quotient_to_quotient_range_pow_quot_succ f p P e i a a_mem (submodule.quotient.mk x) =
    submodule.quotient.mk ⟨_, ideal.mem_map_of_mem _ (ideal.mul_mem_left _ x a_mem)⟩ :=
quotient_to_quotient_range_pow_quot_succ_aux_mk f p P e i a a_mem x

section move_me

omit hfPe

theorem ideal.is_prime.mul_mem_iff {R : Type*} [comm_semiring R] {I : ideal R} (hI : I.is_prime)
  {a b : R} : a * b ∈ I ↔ a ∈ I ∨ b ∈ I :=
⟨hI.mem_or_mem, λ h, h.cases_on (I.mul_mem_right b) (I.mul_mem_left a)⟩

-- TODO: assume `unique_factorization_monoid`?
lemma prime.mul_dvd_pow {R : Type*} [comm_semiring R] (p a b : R) (hp : prime p)
  {n : ℕ} (h : p^n ∣ a * b) : p ∣ a ∨ p^n ∣ b :=
begin
  refine or_iff_not_imp_left.mpr (λ ha, _),
  induction n with n ih,
  { simp },
  sorry
end

lemma ideal.is_prime.mul_mem_pow {R : Type*} [comm_ring R] [is_domain R]
  [is_dedekind_domain R]
  (I : ideal R) [hI : I.is_prime]
  {a b : R} {n : ℕ} (h : a * b ∈ I^n) : a ∈ I ∨ b ∈ I^n :=
begin
  cases n, { simp },
  by_cases hI0 : I = ⊥, { simpa [pow_succ, hI0] using h },
  simp only [← submodule.span_singleton_le_iff_mem, ideal.submodule_span_eq, ← ideal.dvd_iff_le,
    ← ideal.span_singleton_mul_span_singleton] at h ⊢,
  exact prime.mul_dvd_pow I _ _ ((ideal.prime_iff_is_prime hI0).mpr hI) h
end

@[simp]
lemma ideal.quotient.mk_mem_map_mk {R : Type*} [comm_ring R] {I J : ideal R} {x : R} :
  ideal.quotient.mk I x ∈ J.map I^.quotient.mk ↔ x ∈ J ⊔ I :=
by rw [← ideal.mem_comap, ideal.comap_map_of_surjective _ ideal.quotient.mk_surjective,
       ← ring_hom.ker_eq_comap_bot, ideal.mk_ker]

@[simp] lemma multiset.repeat_inter {α : Type*} (x : α) (n : ℕ) (s : multiset α) :
  multiset.repeat x n ∩ s = multiset.repeat x (min n (s.count x)) :=
begin
  refine le_antisymm _ _,
  { simp only [multiset.le_iff_count, multiset.count_inter, multiset.count_repeat],
    intro a,
    split_ifs with h,
    { rw h },
    { rw [nat.zero_min] } },
  simp only [multiset.le_inter_iff, ← multiset.le_count_iff_repeat_le, multiset.count_inter,
    multiset.count_repeat_self],
end

@[simp] lemma multiset.inter_repeat {α : Type*} (s : multiset α) (x : α) (n : ℕ)  :
  s ∩ multiset.repeat x n = multiset.repeat x (min (s.count x) n) :=
by rw [multiset.inter_comm, multiset.repeat_inter, min_comm]

lemma count_normalized_factors_eq {M : Type*} [cancel_comm_monoid_with_zero M]
  [nontrivial M] [decidable_eq M] [decidable_rel ((∣) : M → M → Prop)]
  [normalization_monoid M] [unique_factorization_monoid M]
  {p x : M} (hp : prime p) (hnorm : normalize p = p) {n : ℕ}
  (hle : p^n ∣ x) (hlt : ¬ (p^(n+1) ∣ x)) :
  (normalized_factors x).count p = n :=
begin
  by_cases hx0 : x = 0,
  { simp [hx0] at hlt, contradiction },
  rw [← enat.coe_inj],
  convert (multiplicity_eq_count_normalized_factors hp.irreducible hx0).symm,
  { exact hnorm.symm },
  exact (multiplicity.eq_coe_iff.mpr ⟨hle, hlt⟩).symm
end

lemma ideal.count_normalized_factors_eq {R : Type*} [comm_ring R] [is_domain R]
  [is_dedekind_domain R] {p x : ideal R} (hp0 : p ≠ ⊥) [hp : p.is_prime] {n : ℕ}
  (hle : x ≤ p^n) (hlt : ¬ (x ≤ p^(n+1))) :
  (normalized_factors x).count p = n :=
count_normalized_factors_eq ((ideal.prime_iff_is_prime hp0).mpr hp) (normalize_eq _)
  (ideal.dvd_iff_le.mpr hle) (mt ideal.le_of_dvd hlt)

end move_me

lemma quotient_to_quotient_range_pow_quot_succ_injective [is_dedekind_domain S] [fact (e ≠ 0)]
  [P.is_prime] {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P^i) (a_not_mem : a ∉ P^(i + 1)) :
  function.injective (quotient_to_quotient_range_pow_quot_succ f p P e i a a_mem) :=
λ x, quotient.induction_on' x $ λ x y, quotient.induction_on' y $ λ y h,
begin
  have Pe_le_Pi1 : P^e ≤ P^(i + 1) := ideal.pow_le_pow hi,
  simp only [submodule.quotient.mk'_eq_mk, quotient_to_quotient_range_pow_quot_succ_mk,
    submodule.quotient.eq, linear_map.mem_range, subtype.ext_iff, subtype.coe_mk,
    submodule.coe_sub] at ⊢ h,
  rcases h with ⟨⟨⟨z⟩, hz⟩, h⟩,
  rw [submodule.quotient.quot_mk_eq_mk, ideal.quotient.mk_eq_mk, ideal.quotient.mk_mem_map_mk,
      sup_eq_left.mpr Pe_le_Pi1] at hz,
  rw [pow_quot_succ_inclusion_apply_coe, subtype.coe_mk, submodule.quotient.quot_mk_eq_mk,
      ideal.quotient.mk_eq_mk, ← map_sub, ideal.quotient.eq, ← sub_mul] at h,
  exact (ideal.is_prime.mul_mem_pow _
    ((submodule.sub_mem_iff_right _ hz).mp (Pe_le_Pi1 h))).resolve_right a_not_mem,
end

.

lemma quotient_to_quotient_range_pow_quot_succ_surjective [is_dedekind_domain S] [fact (e ≠ 0)]
  (hP0 : P ≠ ⊥) [hP : P.is_prime] {i : ℕ} (hi : i < e)
  {a : S} (a_mem : a ∈ P^i) (a_not_mem : a ∉ P^(i + 1)) :
  function.surjective (quotient_to_quotient_range_pow_quot_succ f p P e i a a_mem) :=
begin
  rintro ⟨⟨⟨x⟩, hx⟩⟩,
  have Pe_le_Pi : P^e ≤ P^i := ideal.pow_le_pow hi.le,
  have Pe_le_Pi1 : P^e ≤ P^(i + 1) := ideal.pow_le_pow hi,
  rw [submodule.quotient.quot_mk_eq_mk, ideal.quotient.mk_eq_mk, ideal.quotient.mk_mem_map_mk,
      sup_eq_left.mpr Pe_le_Pi] at hx,
  suffices hx' : x ∈ ideal.span {a} ⊔ P^(i+1),
  { obtain ⟨y', hy', z, hz, rfl⟩ := submodule.mem_sup.mp hx',
    obtain ⟨y, rfl⟩ := ideal.mem_span_singleton.mp hy',
    refine ⟨submodule.quotient.mk y, _⟩,
    simp only [submodule.quotient.quot_mk_eq_mk, quotient_to_quotient_range_pow_quot_succ_mk,
        submodule.quotient.eq, linear_map.mem_range, subtype.ext_iff, subtype.coe_mk,
        submodule.coe_sub],
    refine ⟨⟨_, ideal.mem_map_of_mem _ (submodule.neg_mem _ hz)⟩, _⟩,
    rw [pow_quot_succ_inclusion_apply_coe, subtype.coe_mk, ideal.quotient.mk_eq_mk, map_add,
        mul_comm y a, sub_add_cancel', map_neg] },
  rw [sup_eq_prod_inf_factors _ _ _ (pow_ne_zero _ hP0), normalized_factors_pow,
      normalized_factors_irreducible ((ideal.prime_iff_is_prime hP0).mpr hP).irreducible,
      normalize_eq, multiset.nsmul_singleton, multiset.inter_repeat, multiset.prod_repeat],
  rw [← submodule.span_singleton_le_iff_mem, ideal.submodule_span_eq] at a_mem a_not_mem,
  rwa [ideal.count_normalized_factors_eq hP0 a_mem a_not_mem, min_eq_left i.le_succ],
  { intro ha,
    rw ideal.span_singleton_eq_bot.mp ha at a_not_mem,
    have := (P^(i+1)).zero_mem,
    contradiction },
end

/-- Quotienting `P^i / P^e` by its subspace `P^(i+1) ⧸ P^e` is `R ⧸ p`-linear to `S ⧸ P`. -/
noncomputable def quotient_range_pow_quot_succ_inclusion_equiv [is_dedekind_domain S] [fact (e ≠ 0)]
  [P.is_prime] (hP : P ≠ ⊥) {i : ℕ} (hi : i < e) :
  (_ ⧸ (pow_quot_succ_inclusion f p P e i).range) ≃ₗ[R ⧸ p] S ⧸ P :=
begin
  choose a a_mem a_not_mem using set_like.exists_of_lt (ideal.pow_succ_lt P hP i),
  refine (linear_equiv.of_bijective
    (quotient_to_quotient_range_pow_quot_succ f p P e i a a_mem) _ _).symm,
  { exact quotient_to_quotient_range_pow_quot_succ_injective f p P e hi a_mem a_not_mem },
  { exact quotient_to_quotient_range_pow_quot_succ_surjective f p P e hP hi a_mem a_not_mem }
end

.

/-- Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to `P / S`,
`[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]` -/
lemma dim_pow_quot_aux [is_dedekind_domain S] [p.is_maximal] [P.is_prime] (hP0 : P ≠ ⊥) {i : ℕ}
  [fact (e ≠ 0)] (hi : i < e) :
  module.rank (R ⧸ p) (ideal.map (P^e)^.quotient.mk (P ^ i)) =
  module.rank (R ⧸ p) (S ⧸ P) + module.rank (R ⧸ p) (ideal.map (P^e)^.quotient.mk (P ^ (i + 1))) :=
begin
  rw [dim_eq_of_injective _ (pow_quot_succ_inclusion_injective f p P e i),
      (quotient_range_pow_quot_succ_inclusion_equiv f p P e hP0 hi).symm.dim_eq,
      dim_quotient_add_dim (linear_map.range _)],
end

lemma dim_pow_quot [is_dedekind_domain S] [p.is_maximal] [P.is_prime] (hP0 : P ≠ ⊥) (i : ℕ)
  [fact (e ≠ 0)] (hi : i ≤ e) :
  module.rank (R ⧸ p) (ideal.map (P^e)^.quotient.mk (P ^ i)) =
  (e - i) • module.rank (R ⧸ p) (S ⧸ P) :=
begin
  refine @nat.decreasing_induction' _ i e (λ j lt_e le_j ih, _) hi _,
  { rw [dim_pow_quot_aux f p P _ hP0 lt_e, ih, ← succ_nsmul, nat.sub_succ, ← nat.succ_eq_add_one,
      nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt lt_e)] },
  { rw [nat.sub_self, zero_nsmul, map_quotient_mk_self],
    exact dim_bot (R ⧸ p) (S ⧸ (P^e)) }
end

omit hfPe

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/
lemma dim_prime_pow [is_dedekind_domain S] [p.is_maximal] [P.is_prime] (hP0 : P ≠ ⊥)
  {e : ℕ} (he : e ≠ 0) (hp : p ≤ comap f (P ^ e)) :
  @module.rank (R ⧸ p) (S ⧸ P^e) _ _ (@algebra.to_module _ _ _ _ $
    quotient.algebra_quotient_of_le_comap hp) =
  e • @module.rank (R ⧸ p) (S ⧸ P) _ _ (@algebra.to_module _ _ _ _ $
    quotient.algebra_quotient_of_le_comap $ hp.trans $ comap_mono $ P.pow_le_self he) :=
begin
  letI : fact (e ≠ 0) := ⟨he⟩,
  letI : fact _ := ⟨hp⟩,
  have := dim_pow_quot f p P e hP0 0 (nat.zero_le e),
  rw [pow_zero, nat.sub_zero, ideal.one_eq_top, ideal.map_top] at this,
  exact (dim_top (R ⧸ p) _).symm.trans this
end

lemma char_zero.nsmul_eq_zero_iff {R : Type*} [semiring R] [no_zero_divisors R] [char_zero R]
  {n : ℕ} {x : R} :
  n • x = 0 ↔ n = 0 ∨ x = 0 :=
⟨λ h, by rwa [nsmul_eq_mul, mul_eq_zero, nat.cast_eq_zero] at h,
 by { rintros (h | h); simp [h]}⟩

lemma cardinal.nsmul_lt_omega_iff {n : ℕ} (hn : n ≠ 0) {a : cardinal} :
  n • a < cardinal.omega ↔ a < cardinal.omega :=
begin
  cases n,
  { contradiction },
  clear hn,
  induction n with n ih,
  { simp },
  rw [succ_nsmul, cardinal.add_lt_omega_iff, ih, and_self]
end

lemma finite_dimensional_iff_of_rank_eq_nsmul
  {K V W : Type*} [field K] [add_comm_group V] [add_comm_group W] [module K V] [module K W]
  {n : ℕ} (hn : n ≠ 0) (hVW : module.rank K V = n • module.rank K W) :
  finite_dimensional K V ↔ finite_dimensional K W :=
by simp only [finite_dimensional, ← is_noetherian.iff_fg, is_noetherian.iff_dim_lt_omega, hVW,
  cardinal.nsmul_lt_omega_iff hn]

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]`, as a natural number, is equal to `e * [S/P : R/p]`. -/
lemma finrank_prime_pow [is_dedekind_domain S]
  (hP0 : P ≠ ⊥) [p.is_maximal] [P.is_prime]
  {e : ℕ} (he : e ≠ 0) (hp : p ≤ comap f (P ^ e)) :
  @finrank (R ⧸ p) (S ⧸ P^e) _ _ (@algebra.to_module _ _ _ _ $
    quotient.algebra_quotient_of_le_comap hp) =
  e * @finrank (R ⧸ p) (S ⧸ P) _ _ (@algebra.to_module _ _ _ _ $
    quotient.algebra_quotient_of_le_comap $ hp.trans $ comap_mono $ P.pow_le_self he) :=
begin
  letI := quotient.algebra_quotient_of_le_comap hp,
  letI := quotient.algebra_quotient_of_le_comap (hp.trans (comap_mono (P.pow_le_self he))),
  have hdim := dim_prime_pow _ _ _ hP0 he hp,
  by_cases hP : finite_dimensional (R ⧸ p) (S ⧸ P),
  { haveI := hP,
    haveI := (finite_dimensional_iff_of_rank_eq_nsmul he hdim).mpr hP,
    apply cardinal.nat_cast_injective,
    rw [finrank_eq_dim, nat.cast_mul, finrank_eq_dim, hdim, nsmul_eq_mul] },
  have hPe := mt (finite_dimensional_iff_of_rank_eq_nsmul he hdim).mp hP,
  simp only [finrank_of_infinite_dimensional hP, finrank_of_infinite_dimensional hPe, mul_zero],
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
