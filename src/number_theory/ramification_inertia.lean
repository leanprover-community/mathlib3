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

instance is_fraction_ring.no_zero_smul_divisors
  {R K : Type*} [comm_ring R] [field K] [algebra R K] [is_fraction_ring R K] :
  no_zero_smul_divisors R K :=
⟨λ x z h, by rwa [algebra.smul_def, mul_eq_zero, is_fraction_ring.to_map_eq_zero_iff] at h⟩

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

.

open_locale matrix

-- TODO: generalize?
lemma finrank_quotient_map.span_eq_top {K L : Type*} [field K] [field L]
  [algebra R S] [algebra S L] [algebra K L] [module.finite R S]
  (b : set S) (hb' : submodule.span (R ⧸ p) ((map (algebra_map R S) p)^.quotient.mk '' b) = ⊤) :
  submodule.span K (algebra_map S L '' b) = ⊤ :=
begin
  -- Let `M` be the `R`-module spanned by the proposed basis elements.
  let M : submodule R S := submodule.span R b,
  -- Then `S / M` is generated by some finite set of vectors `a`.
  letI h : module.finite R (S ⧸ M) :=
    module.finite.of_surjective (submodule.mkq _) (submodule.quotient.mk_surjective _),
  obtain ⟨n, a, ha⟩ := @@module.finite.exists_fin _ _ _ h,
  -- Because the image of `p` in `S / M` is `⊤`, we can write the elements of `a` as `p`-linear
  -- combinations of other elements of `a`.
  have : ∀ x : (S ⧸ M), ∃ a' : fin n → R, (∀ i, a' i ∈ p) ∧ ∑ i, a' i • a i = x,
  { intro x,
    have hx : x ∈ submodule.span R (set.range a) := ha.symm ▸ submodule.mem_top,
    obtain ⟨a'', ha''⟩ := (finsupp.mem_span_iff_total _ _ _).mp hx,
    refine ⟨λ i, a' ⟨_, ⟨i, rfl⟩⟩, _, _⟩,
    { } },
  choose A' hA'p hA' using λ i, this (a i),
  -- This gives us a(n invertible) matrix `A` such that `span S {det A} ≤ M = span R b`,
  -- and going to the fraction fields, `L = span L {det A} ≤ span K (algebra_map S L '' b)`.
  let A : matrix (fin n) (fin n) R := A' - 1,
  let B := A.adjugate,
  have A_smul : ∀ i, ∑ j, A i j • a j = 0,
  { intros,
    simp only [A, pi.sub_apply, sub_smul, finset.sum_sub_distrib, hA', matrix.one_apply, ite_smul,
      one_smul, zero_smul, finset.sum_ite_eq, finset.mem_univ, if_true, sub_self] },
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
  have : (submodule.span S ({algebra_map R S A.det} : set S)).restrict_scalars R ≤ M,
  { intros x hx,
    rw ← submodule.quotient.mk_eq_zero,
    sorry },
  sorry
end

set_option pp.proofs true

/-- If `p` is a maximal ideal of `R`, and `R` is contained in `S`,
then the dimension `[S/pS : R/p]` is equal to `[Frac(S) : Frac(R)]`. -/
lemma finrank_quotient_map [is_dedekind_domain R] (K L : Type*) [field K] [field L]
  [algebra R S] [algebra R K] [algebra S L] [algebra K L] [is_separable K L]
  [algebra R L] [is_scalar_tower R K L] [is_scalar_tower R S L]
  [is_fraction_ring R K] [is_fraction_ring S L]
  [hp : p.is_maximal] /- [module.free R S] [module.finite R S] -/ [is_noetherian R S] :
  finrank (R ⧸ p) (S ⧸ map (algebra_map R S) p) = finrank K L :=
begin
  let ι := module.free.choose_basis_index (R ⧸ p) (S ⧸ map (algebra_map R S) p),
  let b : basis ι _ _ := module.free.choose_basis  (R ⧸ p) (S ⧸ map (algebra_map R S) p),
  let b' : ι → S := λ i, (ideal.quotient.mk_surjective (b i)).some,
  have b_eq_b' : ⇑ b = (submodule.mkq _).restrict_scalars R ∘ b' :=
    funext (λ i, (ideal.quotient.mk_surjective (b i)).some_spec.symm),
  let b'' : ι → L := algebra_map S L ∘ b',
  have b''_li : linear_independent _ b'' := _,
  have b''_sp : submodule.span _ (set.range b'') = ⊤ := _,
  let c : basis ι K L := basis.mk b''_li b''_sp,
  rw [finrank_eq_card_basis b, finrank_eq_card_basis c],
  { rw eq_top_iff, rintros x -, sorry /- apply finrank_quotient_map.span_eq_top -/ },
  { have := b.linear_independent, rw b_eq_b' at this,
    convert finrank_quotient_map.linear_independent_of_nontrivial _
      ((algebra.linear_map S L).restrict_scalars R) _
      ((submodule.mkq _).restrict_scalars R)
      this,
    { rw [quotient.algebra_map_eq, ideal.mk_ker], exact hp.ne_top },
    { apply_instance }, { apply_instance }, { apply_instance },
    exact is_fraction_ring.injective S L },
end

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
  .. @@function.surjective.module_left _ _ _ _ scalar hf
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
  algebra p.quotient P.quotient :=
quotient.algebra_quotient_of_le_comap (fact.out (p ≤ comap f P))

@[simp] lemma ideal.quotient.algebra_map_quotient_of_fact_le_comap (x : R) :
  algebra_map p.quotient P.quotient (ideal.quotient.mk p x) = ideal.quotient.mk _ (f x) :=
rfl

@[simp] lemma quotient.mk_smul_mk_quotient_map_quotient (x : R) (y : S) :
  ideal.quotient.mk p x • ideal.quotient.mk P y = ideal.quotient.mk _ (f x * y) :=
rfl

omit hfp

@[simp] lemma map_quotient_mk_self {R : Type*} [comm_ring R] (I : ideal R) :
  map (ideal.quotient.mk I) I = ⊥ :=
sorry

variables (e : ℕ) [hfPe : fact (p ≤ comap f (P^e))]
include hfPe

/-- The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`. -/
@[simps]
def pow_quot_succ_inclusion (i : ℕ) :
  ideal.map (P^e)^.quotient.mk (P ^ (i + 1)) →ₗ[p.quotient] ideal.map (P^e)^.quotient.mk (P ^ i) :=
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

def quotient_range_pow_quot_succ_inclusion [fact (e ≠ 0)] (i : ℕ) :
  (pow_quot_succ_inclusion f p P e i).range.quotient ≃ₗ[p.quotient] submodule.quotient P :=
sorry -- TODO: 3rd iso thm

/-- Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to `P / S`,
`[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]` -/
lemma dim_pow_quot_aux [p.is_maximal] {i : ℕ} [fact (e ≠ 0)] (hi : i < e) :
  module.rank p.quotient (ideal.map (P^e)^.quotient.mk (P ^ i)) =
  module.rank p.quotient P.quotient + module.rank p.quotient (ideal.map (P^e)^.quotient.mk (P ^ (i + 1))) :=
begin
  rw [dim_eq_of_injective _ (pow_quot_succ_inclusion_injective f p P e i),
      (quotient_range_pow_quot_succ_inclusion f p P e i).symm.dim_eq,
      dim_quotient_add_dim (linear_map.range _)],
end

lemma dim_pow_quot [p.is_maximal] (i : ℕ) [fact (e ≠ 0)] (hi : i ≤ e) :
  module.rank p.quotient (ideal.map (P^e)^.quotient.mk (P ^ i)) =
  (e - i) • module.rank p.quotient P.quotient :=
begin
  refine @nat.decreasing_induction' _ i e (λ j lt_e le_j ih, _) hi _,
  { rw [dim_pow_quot_aux f p P _ lt_e, ih, ← succ_nsmul, nat.sub_succ, ← nat.succ_eq_add_one,
      nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt lt_e)] },
  { rw [nat.sub_self, zero_nsmul, map_quotient_mk_self],
    exact dim_bot p.quotient (P^e).quotient }
end

omit hfPe

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/
lemma dim_prime_pow [p.is_maximal] (hP0 : P ≠ ⊥)
  {e : ℕ} (he : e ≠ 0) (hp : p ≤ comap f (P ^ e)) :
  @module.rank p.quotient (P^e).quotient _ _ (@algebra.to_module _ _ _ _ $
    quotient.algebra_quotient_of_le_comap hp) =
  e • @module.rank p.quotient P.quotient _ _ (@algebra.to_module _ _ _ _ $
    quotient.algebra_quotient_of_le_comap $ hp.trans $ comap_mono $ P.pow_le_self he) :=
begin
  letI : fact (e ≠ 0) := ⟨he⟩,
  letI : fact _ := ⟨hp⟩,
  have := dim_pow_quot f p P e 0 (nat.zero_le e),
  rw [pow_zero, nat.sub_zero, ideal.one_eq_top, ideal.map_top] at this,
  exact (dim_top p.quotient _).symm.trans this
end

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/
lemma finrank_prime_pow [is_dedekind_domain S]
  (hP0 : P ≠ ⊥) [P.is_prime]
  {e : ℕ} (he : e ≠ 0) (hp : p ≤ comap f (P ^ e)) :
  @finrank p.quotient (P^e).quotient _ _ (@algebra.to_module _ _ _ _ $
    quotient.algebra_quotient_of_le_comap hp) =
  e * @finrank p.quotient P.quotient _ _ (@algebra.to_module _ _ _ _ $
    quotient.algebra_quotient_of_le_comap $ hp.trans $ comap_mono $ P.pow_le_self he) :=
begin
  
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
