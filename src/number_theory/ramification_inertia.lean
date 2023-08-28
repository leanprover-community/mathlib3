/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.free_module.finite.rank
import ring_theory.dedekind_domain.ideal

/-!
# Ramification index and inertia degree

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given `P : ideal S` lying over `p : ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `ideal.ramification_idx f p P` is the multiplicity of `P` in `map f p`,
and the **inertia degree** `ideal.inertia_deg f p P` is the degree of the field extension
`(S / P) : (R / p)`.

## Main results

The main theorem `ideal.sum_ramification_inertia` states that for all coprime `P` lying over `p`,
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

## Notation

In this file, `e` stands for the ramification index and `f` for the inertia degree of `P` over `p`,
leaving `p` and `P` implicit.

-/

namespace ideal

universes u v

variables {R : Type u} [comm_ring R]
variables {S : Type v} [comm_ring S] (f : R →+* S)
variables (p : ideal R) (P : ideal S)

open finite_dimensional
open unique_factorization_monoid

section dec_eq

open_locale classical

/-- The ramification index of `P` over `p` is the largest exponent `n` such that
`p` is contained in `P^n`.

In particular, if `p` is not contained in `P^n`, then the ramification index is 0.

If there is no largest such `n` (e.g. because `p = ⊥`), then `ramification_idx` is
defined to be 0.
-/
noncomputable def ramification_idx : ℕ :=
Sup {n | map f p ≤ P ^ n}

variables {f p P}

lemma ramification_idx_eq_find (h : ∃ n, ∀ k, map f p ≤ P ^ k → k ≤ n) :
  ramification_idx f p P = nat.find h :=
nat.Sup_def h

lemma ramification_idx_eq_zero (h : ∀ n : ℕ, ∃ k, map f p ≤ P ^ k ∧ n < k) :
  ramification_idx f p P = 0 :=
dif_neg (by push_neg; exact h)

lemma ramification_idx_spec {n : ℕ} (hle : map f p ≤ P ^ n) (hgt : ¬ map f p ≤ P ^ (n + 1)) :
  ramification_idx f p P = n :=
begin
  have : ∀ (k : ℕ), map f p ≤ P ^ k → k ≤ n,
  { intros k hk,
    refine le_of_not_lt (λ hnk, _),
    exact hgt (hk.trans (ideal.pow_le_pow hnk)) },
  rw ramification_idx_eq_find ⟨n, this⟩,
  { refine le_antisymm (nat.find_min' _ this) (le_of_not_gt (λ (h : nat.find _ < n), _)),
    obtain this' := nat.find_spec ⟨n, this⟩,
    exact h.not_le (this' _ hle) },
end

lemma ramification_idx_lt {n : ℕ} (hgt : ¬ (map f p ≤ P ^ n)) :
  ramification_idx f p P < n :=
begin
  cases n,
  { simpa using hgt },
  rw nat.lt_succ_iff,
  have : ∀ k, map f p ≤ P ^ k → k ≤ n,
  { refine λ k hk, le_of_not_lt (λ hnk, _),
    exact hgt (hk.trans (ideal.pow_le_pow hnk)) },
  rw ramification_idx_eq_find ⟨n, this⟩,
  exact nat.find_min' ⟨n, this⟩ this
end

@[simp] lemma ramification_idx_bot : ramification_idx f ⊥ P = 0 :=
dif_neg $ not_exists.mpr $ λ n hn, n.lt_succ_self.not_le (hn _ (by simp))

@[simp] lemma ramification_idx_of_not_le (h : ¬ map f p ≤ P) : ramification_idx f p P = 0 :=
ramification_idx_spec (by simp) (by simpa using h)

lemma ramification_idx_ne_zero {e : ℕ} (he : e ≠ 0)
  (hle : map f p ≤ P ^ e) (hnle : ¬ map f p ≤ P ^ (e + 1)):
  ramification_idx f p P ≠ 0 :=
by rwa ramification_idx_spec hle hnle

lemma le_pow_of_le_ramification_idx {n : ℕ} (hn : n ≤ ramification_idx f p P) :
  map f p ≤ P ^ n :=
begin
  contrapose! hn,
  exact ramification_idx_lt hn
end

lemma le_pow_ramification_idx :
  map f p ≤ P ^ ramification_idx f p P :=
le_pow_of_le_ramification_idx (le_refl _)

lemma le_comap_pow_ramification_idx :
  p ≤ comap f (P ^ ramification_idx f p P) :=
map_le_iff_le_comap.mp le_pow_ramification_idx

lemma le_comap_of_ramification_idx_ne_zero (h : ramification_idx f p P ≠ 0) : p ≤ comap f P :=
ideal.map_le_iff_le_comap.mp $ le_pow_ramification_idx.trans $ ideal.pow_le_self $ h

namespace is_dedekind_domain

variables [is_domain S] [is_dedekind_domain S]

lemma ramification_idx_eq_normalized_factors_count
  (hp0 : map f p ≠ ⊥) (hP : P.is_prime) (hP0 : P ≠ ⊥) :
  ramification_idx f p P = (normalized_factors (map f p)).count P :=
begin
  have hPirr := (ideal.prime_of_is_prime hP0 hP).irreducible,
  refine ramification_idx_spec (ideal.le_of_dvd _) (mt ideal.dvd_iff_le.mpr _);
    rw [dvd_iff_normalized_factors_le_normalized_factors (pow_ne_zero _ hP0) hp0,
        normalized_factors_pow, normalized_factors_irreducible hPirr, normalize_eq,
        multiset.nsmul_singleton, ← multiset.le_count_iff_replicate_le],
  { exact (nat.lt_succ_self _).not_le },
end

lemma ramification_idx_eq_factors_count (hp0 : map f p ≠ ⊥) (hP : P.is_prime) (hP0 : P ≠ ⊥) :
  ramification_idx f p P = (factors (map f p)).count P :=
by rw [is_dedekind_domain.ramification_idx_eq_normalized_factors_count hp0 hP hP0,
       factors_eq_normalized_factors]

lemma ramification_idx_ne_zero (hp0 : map f p ≠ ⊥) (hP : P.is_prime) (le : map f p ≤ P) :
  ramification_idx f p P ≠ 0 :=
begin
  have hP0 : P ≠ ⊥,
  { unfreezingI { rintro rfl },
    have := le_bot_iff.mp le,
    contradiction },
  have hPirr := (ideal.prime_of_is_prime hP0 hP).irreducible,
  rw is_dedekind_domain.ramification_idx_eq_normalized_factors_count hp0 hP hP0,
  obtain ⟨P', hP', P'_eq⟩ :=
    exists_mem_normalized_factors_of_dvd hp0 hPirr (ideal.dvd_iff_le.mpr le),
  rwa [multiset.count_ne_zero, associated_iff_eq.mp P'_eq],
end

end is_dedekind_domain

variables (f p P)

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
  have := ideal.quotient.subsingleton_iff.mp hQ,
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

section finrank_quotient_map

open_locale big_operators
open_locale non_zero_divisors

variables [algebra R S]
variables {K : Type*} [field K] [algebra R K] [hRK : is_fraction_ring R K]
variables {L : Type*} [field L] [algebra S L] [is_fraction_ring S L]
variables {V V' V'' : Type*}
variables [add_comm_group V] [module R V] [module K V] [is_scalar_tower R K V]
variables [add_comm_group V'] [module R V'] [module S V'] [is_scalar_tower R S V']
variables [add_comm_group V''] [module R V'']

variables (K)
include hRK
/-- Let `V` be a vector space over `K = Frac(R)`, `S / R` a ring extension
and `V'` a module over `S`. If `b`, in the intersection `V''` of `V` and `V'`,
is linear independent over `S` in `V'`, then it is linear independent over `R` in `V`.

The statement we prove is actually slightly more general:
 * it suffices that the inclusion `algebra_map R S : R → S` is nontrivial
 * the function `f' : V'' → V'` doesn't need to be injective
-/
lemma finrank_quotient_map.linear_independent_of_nontrivial
  [is_domain R] [is_dedekind_domain R] (hRS : (algebra_map R S).ker ≠ ⊤)
  (f : V'' →ₗ[R] V) (hf : function.injective f) (f' : V'' →ₗ[R] V')
  {ι : Type*} {b : ι → V''} (hb' : linear_independent S (f' ∘ b)) :
  linear_independent K (f ∘ b) :=
begin
  contrapose! hb' with hb,
  -- Informally, if we have a nontrivial linear dependence with coefficients `g` in `K`,
  -- then we can find a linear dependence with coefficients `I.quotient.mk g'` in `R/I`,
  -- where `I = ker (algebra_map R S)`.
  -- We make use of the same principle but stay in `R` everywhere.
  simp only [linear_independent_iff', not_forall] at hb ⊢,
  obtain ⟨s, g, eq, j', hj's, hj'g⟩ := hb,
  use s,
  obtain ⟨a, hag, j, hjs, hgI⟩ :=
    ideal.exist_integer_multiples_not_mem hRS s g hj's hj'g,
  choose g'' hg'' using hag,
  letI := classical.prop_decidable,
  let g' := λ i, if h : i ∈ s then g'' i h else 0,
  have hg' : ∀ i ∈ s, algebra_map _ _ (g' i) = a * g i,
  { intros i hi, exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi) },
  -- Because `R/I` is nontrivial, we can lift `g` to a nontrivial linear dependence in `S`.
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

open_locale matrix

variables {K}
omit hRK
/-- If `b` mod `p` spans `S/p` as `R/p`-space, then `b` itself spans `Frac(S)` as `K`-space.

Here,
 * `p` is an ideal of `R` such that `R / p` is nontrivial
 * `K` is a field that has an embedding of `R` (in particular we can take `K = Frac(R)`)
 * `L` is a field extension of `K`
 * `S` is the integral closure of `R` in `L`

More precisely, we avoid quotients in this statement and instead require that `b ∪ pS` spans `S`.
-/
lemma finrank_quotient_map.span_eq_top [is_domain R] [is_domain S] [algebra K L] [is_noetherian R S]
  [algebra R L] [is_scalar_tower R S L] [is_scalar_tower R K L] [is_integral_closure S R L]
  [no_zero_smul_divisors R K]
  (hp : p ≠ ⊤)
  (b : set S) (hb' : submodule.span R b ⊔ (p.map (algebra_map R S)).restrict_scalars R = ⊤) :
  submodule.span K (algebra_map S L '' b) = ⊤ :=
begin
  have hRL : function.injective (algebra_map R L),
  { rw is_scalar_tower.algebra_map_eq R K L,
    exact (algebra_map K L).injective.comp (no_zero_smul_divisors.algebra_map_injective R K) },
  -- Let `M` be the `R`-module spanned by the proposed basis elements.
  set M : submodule R S := submodule.span R b with hM,
  -- Then `S / M` is generated by some finite set of `n` vectors `a`.
  letI h : module.finite R (S ⧸ M) :=
    module.finite.of_surjective (submodule.mkq _) (submodule.quotient.mk_surjective _),
  obtain ⟨n, a, ha⟩ := @@module.finite.exists_fin _ _ _ h,
  -- Because the image of `p` in `S / M` is `⊤`,
  have smul_top_eq : p • (⊤ : submodule R (S ⧸ M)) = ⊤,
  { calc p • ⊤ = submodule.map M.mkq (p • ⊤) :
      by rw [submodule.map_smul'', submodule.map_top, M.range_mkq]
    ... = ⊤ : by rw [ideal.smul_top_eq_map, (submodule.map_mkq_eq_top M _).mpr hb'] },
  -- we can write the elements of `a` as `p`-linear combinations of other elements of `a`.
  have exists_sum : ∀ x : (S ⧸ M), ∃ a' : fin n → R, (∀ i, a' i ∈ p) ∧ ∑ i, a' i • a i = x,
  { intro x,
    obtain ⟨a'', ha'', hx⟩ := (submodule.mem_ideal_smul_span_iff_exists_sum p a x).1 _,
    { refine ⟨λ i, a'' i, λ i, ha'' _, _⟩,
      rw [← hx, finsupp.sum_fintype],
      exact λ _, zero_smul _ _ },
    { rw [ha, smul_top_eq],
      exact submodule.mem_top } },
  choose A' hA'p hA' using λ i, exists_sum (a i),
  -- This gives us a(n invertible) matrix `A` such that `det A ∈ (M = span R b)`,
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
    rw submodule.restrict_scalars_mem at hx,
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
  { rw [eq_comm, submodule.restrict_scalars_eq_top_iff, ideal.span_singleton_eq_top],
    refine is_unit.mk0 _ ((map_ne_zero_iff ((algebra_map R L)) hRL).mpr (
      @ne_zero_of_map _ _ _ _ _ _ (ideal.quotient.mk p) _ _)),
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
    rw [submodule.restrict_scalars_mem, is_scalar_tower.algebra_map_apply R S L] at hx,
    refine is_fraction_ring.ideal_span_singleton_map_subset R _ hRL span_d hx,
    haveI : no_zero_smul_divisors R L := no_zero_smul_divisors.of_algebra_map_injective hRL,
    rw ← is_fraction_ring.is_algebraic_iff' R S,
    intros x,
    exact is_integral.is_algebraic _ (is_integral_of_noetherian infer_instance _) },
end

include hRK
variables (K L)
/-- If `p` is a maximal ideal of `R`, and `S` is the integral closure of `R` in `L`,
then the dimension `[S/pS : R/p]` is equal to `[Frac(S) : Frac(R)]`. -/
lemma finrank_quotient_map [is_domain R] [is_domain S] [is_dedekind_domain R]
  [algebra K L] [algebra R L] [is_scalar_tower R K L] [is_scalar_tower R S L]
  [is_integral_closure S R L]
  [hp : p.is_maximal] [is_noetherian R S] :
  finrank (R ⧸ p) (S ⧸ map (algebra_map R S) p) = finrank K L :=
begin
  -- Choose an arbitrary basis `b` for `[S/pS : R/p]`.
  -- We'll use the previous results to turn it into a basis on `[Frac(S) : Frac(R)]`.
  letI : field (R ⧸ p) := ideal.quotient.field _,
  let ι := module.free.choose_basis_index (R ⧸ p) (S ⧸ map (algebra_map R S) p),
  let b : basis ι (R ⧸ p) (S ⧸ map (algebra_map R S) p) := module.free.choose_basis _ _,
  -- Namely, choose a representative `b' i : S` for each `b i : S / pS`.
  let b' : ι → S := λ i, (ideal.quotient.mk_surjective (b i)).some,
  have b_eq_b' : ⇑ b = (submodule.mkq _).restrict_scalars R ∘ b' :=
    funext (λ i, (ideal.quotient.mk_surjective (b i)).some_spec.symm),
  -- We claim `b'` is a basis for `Frac(S)` over `Frac(R)` because it is linear independent
  -- and spans the whole of `Frac(S)`.
  let b'' : ι → L := algebra_map S L ∘ b',
  have b''_li : linear_independent _ b'' := _,
  have b''_sp : submodule.span _ (set.range b'') = ⊤ := _,
  -- Since the two bases have the same index set, the spaces have the same dimension.
  let c : basis ι K L := basis.mk b''_li b''_sp.ge,
  rw [finrank_eq_card_basis b, finrank_eq_card_basis c],
  -- It remains to show that the basis is indeed linear independent and spans the whole space.
  { rw set.range_comp,
    refine finrank_quotient_map.span_eq_top p hp.ne_top _ (top_le_iff.mp _),
    -- The nicest way to show `S ≤ span b' ⊔ pS` is by reducing both sides modulo pS.
    -- However, this would imply distinguishing between `pS` as `S`-ideal,
    -- and `pS` as `R`-submodule, since they have different (non-defeq) quotients.
    -- Instead we'll lift `x mod pS ∈ span b` to `y ∈ span b'` for some `y - x ∈ pS`.
    intros x hx,
    have mem_span_b :
      ((submodule.mkq (map (algebra_map R S) p)) x :
        S ⧸ map (algebra_map R S) p) ∈ submodule.span (R ⧸ p) (set.range b) := b.mem_span _,
    rw [← @submodule.restrict_scalars_mem R,
        submodule.restrict_scalars_span R (R ⧸ p) ideal.quotient.mk_surjective,
        b_eq_b', set.range_comp, ← submodule.map_span]
      at mem_span_b,
    obtain ⟨y, y_mem, y_eq⟩ := submodule.mem_map.mp mem_span_b,
    suffices : y + -(y - x) ∈ _, { simpa },
    rw [linear_map.restrict_scalars_apply, submodule.mkq_apply, submodule.mkq_apply,
        submodule.quotient.eq] at y_eq,
    exact add_mem (submodule.mem_sup_left y_mem) (neg_mem $ submodule.mem_sup_right y_eq) },
  { have := b.linear_independent, rw b_eq_b' at this,
    convert finrank_quotient_map.linear_independent_of_nontrivial K _
      ((algebra.linear_map S L).restrict_scalars R) _
      ((submodule.mkq _).restrict_scalars R)
      this,
    { rw [quotient.algebra_map_eq, ideal.mk_ker],
      exact hp.ne_top },
    { exact is_fraction_ring.injective S L } },
end

end finrank_quotient_map

section fact_le_comap

local notation `e` := ramification_idx f p P

/-- `R / p` has a canonical map to `S / (P ^ e)`, where `e` is the ramification index
of `P` over `p`. -/
noncomputable instance quotient.algebra_quotient_pow_ramification_idx :
  algebra (R ⧸ p) (S ⧸ (P ^ e)) :=
quotient.algebra_quotient_of_le_comap (ideal.map_le_iff_le_comap.mp le_pow_ramification_idx)

@[simp] lemma quotient.algebra_map_quotient_pow_ramification_idx (x : R) :
  algebra_map (R ⧸ p) (S ⧸ P ^ e) (ideal.quotient.mk p x) = ideal.quotient.mk _ (f x) :=
rfl

variables [hfp : ne_zero (ramification_idx f p P)]
include hfp

/-- If `P` lies over `p`, then `R / p` has a canonical map to `S / P`.

This can't be an instance since the map `f : R → S` is generally not inferrable.
-/
def quotient.algebra_quotient_of_ramification_idx_ne_zero :
  algebra (R ⧸ p) (S ⧸ P) :=
quotient.algebra_quotient_of_le_comap (le_comap_of_ramification_idx_ne_zero hfp.out)

-- In this file, the value for `f` can be inferred.
local attribute [instance] ideal.quotient.algebra_quotient_of_ramification_idx_ne_zero

@[simp] lemma quotient.algebra_map_quotient_of_ramification_idx_ne_zero (x : R) :
  algebra_map (R ⧸ p) (S ⧸ P) (ideal.quotient.mk p x) = ideal.quotient.mk _ (f x) :=
rfl

omit hfp

/-- The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`. -/
@[simps]
def pow_quot_succ_inclusion (i : ℕ) :
  ideal.map (P^e)^.quotient.mk (P ^ (i + 1)) →ₗ[R ⧸ p] ideal.map (P^e)^.quotient.mk (P ^ i) :=
{ to_fun := λ x, ⟨x, ideal.map_mono (ideal.pow_le_pow i.le_succ) x.2⟩,
  map_add' := λ x y, rfl,
  map_smul' := λ c x, rfl }

lemma pow_quot_succ_inclusion_injective (i : ℕ) :
  function.injective (pow_quot_succ_inclusion f p P i) :=
begin
  rw [← linear_map.ker_eq_bot, linear_map.ker_eq_bot'],
  rintro ⟨x, hx⟩ hx0,
  rw subtype.ext_iff at hx0 ⊢,
  rwa pow_quot_succ_inclusion_apply_coe at hx0
end

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`.
See `quotient_to_quotient_range_pow_quot_succ` for this as a linear map,
and `quotient_range_pow_quot_succ_inclusion_equiv` for this as a linear equivalence.
-/
noncomputable def quotient_to_quotient_range_pow_quot_succ_aux {i : ℕ} {a : S} (a_mem : a ∈ P^i) :
  S ⧸ P → ((P ^ i).map (P ^ e)^.quotient.mk ⧸ (pow_quot_succ_inclusion f p P i).range) :=
quotient.map' (λ (x : S), ⟨_, ideal.mem_map_of_mem _ (ideal.mul_mem_left _ x a_mem)⟩)
  (λ x y h, begin
    rw submodule.quotient_rel_r_def at ⊢ h,
    simp only [_root_.map_mul, linear_map.mem_range],
    refine ⟨⟨_, ideal.mem_map_of_mem _ (ideal.mul_mem_mul h a_mem)⟩, _⟩,
    ext,
    rw [pow_quot_succ_inclusion_apply_coe, subtype.coe_mk, submodule.coe_sub, subtype.coe_mk,
        subtype.coe_mk, _root_.map_mul, map_sub, sub_mul]
  end)

lemma quotient_to_quotient_range_pow_quot_succ_aux_mk {i : ℕ} {a : S} (a_mem : a ∈ P^i) (x : S) :
  quotient_to_quotient_range_pow_quot_succ_aux f p P a_mem (submodule.quotient.mk x) =
    submodule.quotient.mk ⟨_, ideal.mem_map_of_mem _ (ideal.mul_mem_left _ x a_mem)⟩ :=
by apply quotient.map'_mk'

include hfp

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`. -/
noncomputable def quotient_to_quotient_range_pow_quot_succ {i : ℕ} {a : S} (a_mem : a ∈ P^i) :
  S ⧸ P →ₗ[R ⧸ p] ((P ^ i).map (P ^ e)^.quotient.mk ⧸ (pow_quot_succ_inclusion f p P i).range) :=
{ to_fun := quotient_to_quotient_range_pow_quot_succ_aux f p P a_mem,
  map_add' := begin
    intros x y, refine quotient.induction_on' x (λ x, quotient.induction_on' y (λ y, _)),
    simp only [submodule.quotient.mk'_eq_mk, ← submodule.quotient.mk_add,
              quotient_to_quotient_range_pow_quot_succ_aux_mk, add_mul],
    refine congr_arg submodule.quotient.mk _,
    ext,
    refl
  end,
  map_smul' := begin
    intros x y, refine quotient.induction_on' x (λ x, quotient.induction_on' y (λ y, _)),
    simp only [submodule.quotient.mk'_eq_mk, ← submodule.quotient.mk_add,
              quotient_to_quotient_range_pow_quot_succ_aux_mk, ring_hom.id_apply],
    refine congr_arg submodule.quotient.mk _,
    ext,
    simp only [subtype.coe_mk, _root_.map_mul, algebra.smul_def, submodule.coe_mk, mul_assoc,
              ideal.quotient.mk_eq_mk, submodule.coe_smul_of_tower,
              ideal.quotient.algebra_map_quotient_pow_ramification_idx]
  end }

lemma quotient_to_quotient_range_pow_quot_succ_mk {i : ℕ} {a : S} (a_mem : a ∈ P^i) (x : S) :
  quotient_to_quotient_range_pow_quot_succ f p P a_mem (submodule.quotient.mk x) =
    submodule.quotient.mk ⟨_, ideal.mem_map_of_mem _ (ideal.mul_mem_left _ x a_mem)⟩ :=
quotient_to_quotient_range_pow_quot_succ_aux_mk f p P a_mem x

lemma quotient_to_quotient_range_pow_quot_succ_injective [is_domain S] [is_dedekind_domain S]
  [P.is_prime] {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P^i) (a_not_mem : a ∉ P^(i + 1)) :
  function.injective (quotient_to_quotient_range_pow_quot_succ f p P a_mem) :=
λ x, quotient.induction_on' x $ λ x y, quotient.induction_on' y $ λ y h,
begin
  have Pe_le_Pi1 : P^e ≤ P^(i + 1) := ideal.pow_le_pow hi,
  simp only [submodule.quotient.mk'_eq_mk, quotient_to_quotient_range_pow_quot_succ_mk,
    submodule.quotient.eq, linear_map.mem_range, subtype.ext_iff, subtype.coe_mk,
    submodule.coe_sub] at ⊢ h,
  rcases h with ⟨⟨⟨z⟩, hz⟩, h⟩,
  rw [submodule.quotient.quot_mk_eq_mk, ideal.quotient.mk_eq_mk, ideal.mem_quotient_iff_mem_sup,
      sup_eq_left.mpr Pe_le_Pi1] at hz,
  rw [pow_quot_succ_inclusion_apply_coe, subtype.coe_mk, submodule.quotient.quot_mk_eq_mk,
      ideal.quotient.mk_eq_mk, ← map_sub, ideal.quotient.eq, ← sub_mul] at h,
  exact (ideal.is_prime.mul_mem_pow _
    ((submodule.sub_mem_iff_right _ hz).mp (Pe_le_Pi1 h))).resolve_right a_not_mem,
end

lemma quotient_to_quotient_range_pow_quot_succ_surjective [is_domain S] [is_dedekind_domain S]
  (hP0 : P ≠ ⊥) [hP : P.is_prime] {i : ℕ} (hi : i < e)
  {a : S} (a_mem : a ∈ P^i) (a_not_mem : a ∉ P^(i + 1)) :
  function.surjective (quotient_to_quotient_range_pow_quot_succ f p P a_mem) :=
begin
  rintro ⟨⟨⟨x⟩, hx⟩⟩,
  have Pe_le_Pi : P^e ≤ P^i := ideal.pow_le_pow hi.le,
  have Pe_le_Pi1 : P^e ≤ P^(i + 1) := ideal.pow_le_pow hi,
  rw [submodule.quotient.quot_mk_eq_mk, ideal.quotient.mk_eq_mk, ideal.mem_quotient_iff_mem_sup,
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
  letI := classical.dec_eq (ideal S),
  rw [sup_eq_prod_inf_factors _ (pow_ne_zero _ hP0), normalized_factors_pow,
      normalized_factors_irreducible ((ideal.prime_iff_is_prime hP0).mpr hP).irreducible,
      normalize_eq, multiset.nsmul_singleton, multiset.inter_replicate, multiset.prod_replicate],
  rw [← submodule.span_singleton_le_iff_mem, ideal.submodule_span_eq] at a_mem a_not_mem,
  rwa [ideal.count_normalized_factors_eq a_mem a_not_mem, min_eq_left i.le_succ],
  { intro ha,
    rw ideal.span_singleton_eq_bot.mp ha at a_not_mem,
    have := (P^(i+1)).zero_mem,
    contradiction },
end

/-- Quotienting `P^i / P^e` by its subspace `P^(i+1) ⧸ P^e` is
`R ⧸ p`-linearly isomorphic to `S ⧸ P`. -/
noncomputable def quotient_range_pow_quot_succ_inclusion_equiv [is_domain S] [is_dedekind_domain S]
  [P.is_prime] (hP : P ≠ ⊥) {i : ℕ} (hi : i < e) :
  ((P ^ i).map (P ^ e)^.quotient.mk ⧸ (pow_quot_succ_inclusion f p P i).range) ≃ₗ[R ⧸ p] S ⧸ P :=
begin
  choose a a_mem a_not_mem using set_like.exists_of_lt
    (ideal.strict_anti_pow P hP (ideal.is_prime.ne_top infer_instance) (le_refl i.succ)),
  refine (linear_equiv.of_bijective _ ⟨_, _⟩).symm,
  { exact quotient_to_quotient_range_pow_quot_succ f p P a_mem },
  { exact quotient_to_quotient_range_pow_quot_succ_injective f p P hi a_mem a_not_mem },
  { exact quotient_to_quotient_range_pow_quot_succ_surjective f p P hP hi a_mem a_not_mem }
end

/-- Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to `P / S`,
`[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]` -/
lemma rank_pow_quot_aux [is_domain S] [is_dedekind_domain S] [p.is_maximal] [P.is_prime]
  (hP0 : P ≠ ⊥) {i : ℕ} (hi : i < e) :
  module.rank (R ⧸ p) (ideal.map (P^e)^.quotient.mk (P ^ i)) =
  module.rank (R ⧸ p) (S ⧸ P) + module.rank (R ⧸ p) (ideal.map (P^e)^.quotient.mk (P ^ (i + 1))) :=
begin
  letI : field (R ⧸ p) := ideal.quotient.field _,
  rw [rank_eq_of_injective _ (pow_quot_succ_inclusion_injective f p P i),
      (quotient_range_pow_quot_succ_inclusion_equiv f p P hP0 hi).symm.rank_eq],
  exact (rank_quotient_add_rank (linear_map.range (pow_quot_succ_inclusion f p P i))).symm,
end

lemma rank_pow_quot [is_domain S] [is_dedekind_domain S] [p.is_maximal] [P.is_prime]
  (hP0 : P ≠ ⊥) (i : ℕ) (hi : i ≤ e) :
  module.rank (R ⧸ p) (ideal.map (P^e)^.quotient.mk (P ^ i)) =
  (e - i) • module.rank (R ⧸ p) (S ⧸ P) :=
begin
  refine @nat.decreasing_induction' _ i e (λ j lt_e le_j ih, _) hi _,
  { rw [rank_pow_quot_aux f p P _ lt_e, ih, ← succ_nsmul, nat.sub_succ, ← nat.succ_eq_add_one,
      nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt lt_e)],
    assumption },
  { rw [nat.sub_self, zero_nsmul, map_quotient_self],
    exact rank_bot (R ⧸ p) (S ⧸ (P^e)) }
end

omit hfp

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/
lemma rank_prime_pow_ramification_idx [is_domain S] [is_dedekind_domain S] [p.is_maximal]
  [P.is_prime] (hP0 : P ≠ ⊥) (he : e ≠ 0) :
  module.rank (R ⧸ p) (S ⧸ P^e) =
  e • @module.rank (R ⧸ p) (S ⧸ P) _ _ (@algebra.to_module _ _ _ _ $
    @@quotient.algebra_quotient_of_ramification_idx_ne_zero _ _ _ _ _ ⟨he⟩) :=
begin
  letI : ne_zero e := ⟨he⟩,
  have := rank_pow_quot f p P hP0 0 (nat.zero_le e),
  rw [pow_zero, nat.sub_zero, ideal.one_eq_top, ideal.map_top] at this,
  exact (rank_top (R ⧸ p) _).symm.trans this
end

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]`, as a natural number, is equal to `e * [S/P : R/p]`. -/
lemma finrank_prime_pow_ramification_idx [is_domain S] [is_dedekind_domain S]
  (hP0 : P ≠ ⊥) [p.is_maximal] [P.is_prime] (he : e ≠ 0) :
  finrank (R ⧸ p) (S ⧸ P^e) =
  e * @finrank (R ⧸ p) (S ⧸ P) _ _ (@algebra.to_module _ _ _ _ $
    @@quotient.algebra_quotient_of_ramification_idx_ne_zero _ _ _ _ _ ⟨he⟩) :=
begin
  letI : ne_zero e := ⟨he⟩,
  letI : algebra (R ⧸ p) (S ⧸ P) := quotient.algebra_quotient_of_ramification_idx_ne_zero f p P,
  letI := ideal.quotient.field p,
  have hdim := rank_prime_pow_ramification_idx _ _ _ hP0 he,
  by_cases hP : finite_dimensional (R ⧸ p) (S ⧸ P),
  { haveI := hP,
    haveI := (finite_dimensional_iff_of_rank_eq_nsmul he hdim).mpr hP,
    refine cardinal.nat_cast_injective _,
    rw [finrank_eq_rank', nat.cast_mul, finrank_eq_rank', hdim, nsmul_eq_mul] },
  have hPe := mt (finite_dimensional_iff_of_rank_eq_nsmul he hdim).mp hP,
  simp only [finrank_of_infinite_dimensional hP, finrank_of_infinite_dimensional hPe, mul_zero],
end

end fact_le_comap

section factors_map

open_locale classical

/-! ## Properties of the factors of `p.map (algebra_map R S)` -/

variables [is_domain S] [is_dedekind_domain S] [algebra R S]

lemma factors.ne_bot (P : (factors (map (algebra_map R S) p)).to_finset) :
  (P : ideal S) ≠ ⊥ :=
(prime_of_factor _ (multiset.mem_to_finset.mp P.2)).ne_zero

instance factors.is_prime (P : (factors (map (algebra_map R S) p)).to_finset) :
  is_prime (P : ideal S) :=
ideal.is_prime_of_prime (prime_of_factor _ (multiset.mem_to_finset.mp P.2))

lemma factors.ramification_idx_ne_zero (P : (factors (map (algebra_map R S) p)).to_finset) :
  ramification_idx (algebra_map R S) p P ≠ 0 :=
is_dedekind_domain.ramification_idx_ne_zero
  (ne_zero_of_mem_factors (multiset.mem_to_finset.mp P.2))
  (factors.is_prime p P)
  (ideal.le_of_dvd (dvd_of_mem_factors (multiset.mem_to_finset.mp P.2)))

instance factors.fact_ramification_idx_ne_zero (P : (factors (map (algebra_map R S) p)).to_finset) :
  ne_zero (ramification_idx (algebra_map R S) p P) :=
⟨factors.ramification_idx_ne_zero p P⟩

local attribute [instance] quotient.algebra_quotient_of_ramification_idx_ne_zero

instance factors.is_scalar_tower
  (P : (factors (map (algebra_map R S) p)).to_finset) :
  is_scalar_tower R (R ⧸ p) (S ⧸ (P : ideal S)) :=
is_scalar_tower.of_algebra_map_eq (λ x, by simp)

local attribute [instance] ideal.quotient.field

lemma factors.finrank_pow_ramification_idx [p.is_maximal]
  (P : (factors (map (algebra_map R S) p)).to_finset) :
  finrank (R ⧸ p) (S ⧸ (P : ideal S) ^ ramification_idx (algebra_map R S) p P) =
    ramification_idx (algebra_map R S) p P * inertia_deg (algebra_map R S) p P :=
begin
  rw [finrank_prime_pow_ramification_idx, inertia_deg_algebra_map],
  exact factors.ne_bot p P,
end

instance factors.finite_dimensional_quotient [is_noetherian R S] [p.is_maximal]
  (P : (factors (map (algebra_map R S) p)).to_finset) :
  finite_dimensional (R ⧸ p) (S ⧸ (P : ideal S)) :=
is_noetherian.iff_fg.mp $
is_noetherian_of_tower R $
is_noetherian_of_surjective S (ideal.quotient.mkₐ _ _).to_linear_map $
linear_map.range_eq_top.mpr ideal.quotient.mk_surjective

lemma factors.inertia_deg_ne_zero [is_noetherian R S] [p.is_maximal]
  (P : (factors (map (algebra_map R S) p)).to_finset) :
  inertia_deg (algebra_map R S) p P ≠ 0 :=
by { rw inertia_deg_algebra_map, exact (finite_dimensional.finrank_pos_iff.mpr infer_instance).ne' }

instance factors.finite_dimensional_quotient_pow [is_noetherian R S] [p.is_maximal]
  (P : (factors (map (algebra_map R S) p)).to_finset) :
  finite_dimensional (R ⧸ p) (S ⧸ (P : ideal S) ^ ramification_idx (algebra_map R S) p P) :=
begin
  refine finite_dimensional.finite_dimensional_of_finrank _,
  rw [pos_iff_ne_zero, factors.finrank_pow_ramification_idx],
  exact mul_ne_zero (factors.ramification_idx_ne_zero p P) (factors.inertia_deg_ne_zero p P)
end

universes w

/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : ideal R`
factors in `S` as `∏ i, P i ^ e i`, then `S ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def factors.pi_quotient_equiv
  (p : ideal R) (hp : map (algebra_map R S) p ≠ ⊥) :
  (S ⧸ map (algebra_map R S) p) ≃+* Π (P : (factors (map (algebra_map R S) p)).to_finset),
    S ⧸ ((P : ideal S) ^ ramification_idx (algebra_map R S) p P) :=
(is_dedekind_domain.quotient_equiv_pi_factors hp).trans $
(@ring_equiv.Pi_congr_right (factors (map (algebra_map R S) p)).to_finset
  (λ P, S ⧸ (P : ideal S) ^ (factors (map (algebra_map R S) p)).count P)
  (λ P, S ⧸ (P : ideal S) ^ ramification_idx (algebra_map R S) p P) _ _
  (λ P : (factors (map (algebra_map R S) p)).to_finset, ideal.quot_equiv_of_eq $
  by rw is_dedekind_domain.ramification_idx_eq_factors_count hp
    (factors.is_prime p P) (factors.ne_bot p P)))

@[simp] lemma factors.pi_quotient_equiv_mk
  (p : ideal R) (hp : map (algebra_map R S) p ≠ ⊥) (x : S) :
  factors.pi_quotient_equiv p hp (ideal.quotient.mk _ x) = λ P, ideal.quotient.mk _ x :=
rfl

@[simp] lemma factors.pi_quotient_equiv_map
  (p : ideal R) (hp : map (algebra_map R S) p ≠ ⊥) (x : R) :
  factors.pi_quotient_equiv p hp (algebra_map _ _ x) =
    λ P, ideal.quotient.mk _ (algebra_map _ _ x) :=
rfl

variables (S)

/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : ideal R`
factors in `S` as `∏ i, P i ^ e i`,
then `S ⧸ I` factors `R ⧸ I`-linearly as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def factors.pi_quotient_linear_equiv
  (p : ideal R) (hp : map (algebra_map R S) p ≠ ⊥) :
  (S ⧸ map (algebra_map R S) p) ≃ₗ[R ⧸ p] Π (P : (factors (map (algebra_map R S) p)).to_finset),
    S ⧸ ((P : ideal S) ^ ramification_idx (algebra_map R S) p P) :=
{ map_smul' := begin
   rintro ⟨c⟩ ⟨x⟩, ext P,
   simp only [ideal.quotient.mk_algebra_map,
     factors.pi_quotient_equiv_mk, factors.pi_quotient_equiv_map, submodule.quotient.quot_mk_eq_mk,
     pi.algebra_map_apply, ring_equiv.to_fun_eq_coe, pi.mul_apply,
     ideal.quotient.algebra_map_quotient_map_quotient, ideal.quotient.mk_eq_mk, algebra.smul_def,
     _root_.map_mul, ring_hom_comp_triple.comp_apply],
   congr
  end,
  .. factors.pi_quotient_equiv p hp }

variables {S}

open_locale big_operators

/-- The **fundamental identity** of ramification index `e` and inertia degree `f`:
for `P` ranging over the primes lying over `p`, `∑ P, e P * f P = [Frac(S) : Frac(R)]`;
here `S` is a finite `R`-module (and thus `Frac(S) : Frac(R)` is a finite extension) and `p`
is maximal.
-/
theorem sum_ramification_inertia (K L : Type*) [field K] [field L]
  [is_domain R] [is_dedekind_domain R]
  [algebra R K] [is_fraction_ring R K] [algebra S L] [is_fraction_ring S L]
  [algebra K L] [algebra R L] [is_scalar_tower R S L] [is_scalar_tower R K L]
  [is_noetherian R S] [is_integral_closure S R L] [p.is_maximal] (hp0 : p ≠ ⊥) :
  ∑ P in (factors (map (algebra_map R S) p)).to_finset,
    ramification_idx (algebra_map R S) p P * inertia_deg (algebra_map R S) p P =
    finrank K L :=
begin
  set e := ramification_idx (algebra_map R S) p,
  set f := inertia_deg (algebra_map R S) p,
  have inj_RL : function.injective (algebra_map R L),
  { rw [is_scalar_tower.algebra_map_eq R K L, ring_hom.coe_comp],
    exact (ring_hom.injective _).comp (is_fraction_ring.injective R K) },
  have inj_RS : function.injective (algebra_map R S),
  { refine function.injective.of_comp (show function.injective (algebra_map S L ∘ _), from _),
    rw [← ring_hom.coe_comp, ← is_scalar_tower.algebra_map_eq],
    exact inj_RL },
  calc  ∑ P in (factors (map (algebra_map R S) p)).to_finset, e P * f P
      = ∑ P in (factors (map (algebra_map R S) p)).to_finset.attach,
          finrank (R ⧸ p) (S ⧸ (P : ideal S)^(e P)) : _
  ... = finrank (R ⧸ p) (Π P : (factors (map (algebra_map R S) p)).to_finset,
          (S ⧸ (P : ideal S)^(e P))) :
    (finrank_pi_fintype (R ⧸ p)).symm
  ... = finrank (R ⧸ p) (S ⧸ map (algebra_map R S) p) : _
  ... = finrank K L : _,
  { rw ← finset.sum_attach,
    refine finset.sum_congr rfl (λ P _, _),
    rw factors.finrank_pow_ramification_idx },
  { refine linear_equiv.finrank_eq (factors.pi_quotient_linear_equiv S p _).symm,
    rwa [ne.def, ideal.map_eq_bot_iff_le_ker, (ring_hom.injective_iff_ker_eq_bot _).mp inj_RS,
         le_bot_iff] },
  { exact finrank_quotient_map p K L },
end

end factors_map

end ideal
