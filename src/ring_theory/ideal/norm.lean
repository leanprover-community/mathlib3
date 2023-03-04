/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/

import algebra.char_p.quotient
import data.finsupp.fintype
import data.int.absolute_value
import data.int.associated
import number_theory.ramification_inertia
import linear_algebra.free_module.determinant
import linear_algebra.free_module.ideal_quotient
import ring_theory.dedekind_domain.pid
import ring_theory.local_properties
import ring_theory.localization.norm

/-!

# Ideal norms

This file defines the absolute ideal norm `ideal.abs_norm (I : ideal R) : ℕ` as the cardinality of
the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite),
and the relative ideal norm `ideal.span_norm R (I : ideal S) : ideal S` as the ideal spanned by
the norms of elements in `I`.

## Main definitions

 * `submodule.card_quot (S : submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
   This maps `⊥` to `0` and `⊤` to `1`.
 * `ideal.abs_norm (I : ideal R)`: the absolute ideal norm, defined as
   the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.
 * `ideal.span_norm R (I : ideal S)`: the ideal spanned by the norms of elements in `I`.
    This is used to define `ideal.rel_norm`.
 * `ideal.rel_norm R (I : ideal S)`: the relative ideal norm as a bundled monoid-with-zero morphism,
   defined as the ideal spanned by the norms of elements in `I`.

## Main results

 * `map_mul ideal.abs_norm`: multiplicativity of the ideal norm is bundled in
   the definition of `ideal.abs_norm`
 * `ideal.nat_abs_det_basis_change`: the ideal norm is given by the determinant
   of the basis change matrix
 * `ideal.abs_norm_span_singleton`: the ideal norm of a principal ideal is the
   norm of its generator
 * `map_mul ideal.rel_norm`: multiplicativity of the relative ideal norm
-/

open_locale big_operators
open_locale non_zero_divisors

section abs_norm

namespace submodule

variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

section

/-- The cardinality of `(M ⧸ S)`, if `(M ⧸ S)` is finite, and `0` otherwise.
This is used to define the absolute ideal norm `ideal.abs_norm`.
-/
noncomputable def card_quot (S : submodule R M) : ℕ :=
add_subgroup.index S.to_add_subgroup

@[simp] lemma card_quot_apply (S : submodule R M) [fintype (M ⧸ S)] :
  card_quot S = fintype.card (M ⧸ S) :=
add_subgroup.index_eq_card _

variables (R M)

@[simp] lemma card_quot_bot [infinite M] : card_quot (⊥ : submodule R M) = 0 :=
add_subgroup.index_bot.trans nat.card_eq_zero_of_infinite

@[simp] lemma card_quot_top : card_quot (⊤ : submodule R M) = 1 :=
add_subgroup.index_top

variables {R M}

@[simp] lemma card_quot_eq_one_iff {P : submodule R M} : card_quot P = 1 ↔ P = ⊤ :=
add_subgroup.index_eq_one.trans (by simp [set_like.ext_iff])

end

end submodule

section ring_of_integers

variables {S : Type*} [comm_ring S] [is_domain S]

open submodule

/-- Multiplicity of the ideal norm, for coprime ideals.
This is essentially just a repackaging of the Chinese Remainder Theorem.
-/
lemma card_quot_mul_of_coprime [is_dedekind_domain S] [module.free ℤ S] [module.finite ℤ S]
  {I J : ideal S} (coprime : I ⊔ J = ⊤) : card_quot (I * J) = card_quot I * card_quot J :=
begin
  let b := module.free.choose_basis ℤ S,
  casesI is_empty_or_nonempty (module.free.choose_basis_index ℤ S),
  { haveI : subsingleton S := function.surjective.subsingleton b.repr.to_equiv.symm.surjective,
    nontriviality S,
    exfalso,
    exact not_nontrivial_iff_subsingleton.mpr ‹subsingleton S› ‹nontrivial S› },
  haveI : infinite S := infinite.of_surjective _ b.repr.to_equiv.surjective,
  by_cases hI : I = ⊥,
  { rw [hI, submodule.bot_mul, card_quot_bot, zero_mul] },
  by_cases hJ : J = ⊥,
  { rw [hJ, submodule.mul_bot, card_quot_bot, mul_zero] },
  have hIJ : I * J ≠ ⊥ := mt ideal.mul_eq_bot.mp (not_or hI hJ),

  letI := classical.dec_eq (module.free.choose_basis_index ℤ S),
  letI := I.fintype_quotient_of_free_of_ne_bot hI,
  letI := J.fintype_quotient_of_free_of_ne_bot hJ,
  letI := (I * J).fintype_quotient_of_free_of_ne_bot hIJ,

  rw [card_quot_apply, card_quot_apply, card_quot_apply,
      fintype.card_eq.mpr ⟨(ideal.quotient_mul_equiv_quotient_prod I J coprime).to_equiv⟩,
      fintype.card_prod]
end

/-- If the `d` from `ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`,
then so are the `c`s, up to `P ^ (i + 1)`.
Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.mul_add_mem_pow_succ_inj
  (P : ideal S) {i : ℕ} (a d d' e e' : S) (a_mem : a ∈ P ^ i)
  (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
  (h : d - d' ∈ P) : (a * d + e) - (a * d' + e') ∈ P ^ (i + 1) :=
begin
  have : a * d - a * d' ∈ P ^ (i + 1),
  { convert ideal.mul_mem_mul a_mem h; simp [mul_sub, pow_succ, mul_comm] },
  convert ideal.add_mem _ this (ideal.sub_mem _ e_mem e'_mem),
  ring,
end

section P_prime

variables {P : ideal S} [P_prime : P.is_prime] (hP : P ≠ ⊥)
include P_prime hP

/-- If `a ∈ P^i \ P^(i+1)` and `c ∈ P^i`, then `a * d + e = c` for `e ∈ P^(i+1)`.
`ideal.mul_add_mem_pow_succ_unique` shows the choice of `d` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.exists_mul_add_mem_pow_succ [is_dedekind_domain S] {i : ℕ}
  (a c : S) (a_mem : a ∈ P ^ i) (a_not_mem : a ∉ P ^ (i + 1)) (c_mem : c ∈ P ^ i) :
  ∃ (d : S) (e ∈ P ^ (i + 1)), a * d + e = c :=
begin
  suffices eq_b : P ^ i = ideal.span {a} ⊔ P ^ (i + 1),
  { rw eq_b at c_mem,
    simp only [mul_comm a],
    exact ideal.mem_span_singleton_sup.mp c_mem },
  refine (ideal.eq_prime_pow_of_succ_lt_of_le hP
    (lt_of_le_of_ne le_sup_right _)
    (sup_le (ideal.span_le.mpr (set.singleton_subset_iff.mpr a_mem))
      (ideal.pow_succ_lt_pow hP i).le)).symm,
  contrapose! a_not_mem with this,
  rw this,
  exact mem_sup.mpr ⟨a, mem_span_singleton_self a, 0, by simp, by simp⟩
end

lemma ideal.mem_prime_of_mul_mem_pow [is_dedekind_domain S]
  {P : ideal S} [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  {a b : S} (a_not_mem : a ∉ P ^ (i + 1))
  (ab_mem : a * b ∈ P ^ (i + 1)) : b ∈ P :=
begin
  simp only [← ideal.span_singleton_le_iff_mem, ← ideal.dvd_iff_le, pow_succ,
       ← ideal.span_singleton_mul_span_singleton] at a_not_mem ab_mem ⊢,
  exact (prime_pow_succ_dvd_mul (ideal.prime_of_is_prime hP P_prime) ab_mem).resolve_left a_not_mem
end

/-- The choice of `d` in `ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.mul_add_mem_pow_succ_unique [is_dedekind_domain S] {i : ℕ}
  (a d d' e e' : S) (a_not_mem : a ∉ P ^ (i + 1))
  (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
  (h : (a * d + e) - (a * d' + e') ∈ P ^ (i + 1)) : d - d' ∈ P :=
begin
  have : e' - e ∈ P ^ (i + 1) := ideal.sub_mem _ e'_mem e_mem,
  have h' : a * (d - d') ∈ P ^ (i + 1),
  { convert ideal.add_mem _ h (ideal.sub_mem _ e'_mem e_mem),
    ring },
  exact ideal.mem_prime_of_mul_mem_pow hP a_not_mem h'
end

/-- Multiplicity of the ideal norm, for powers of prime ideals. -/
lemma card_quot_pow_of_prime [is_dedekind_domain S] [module.finite ℤ S] [module.free ℤ S] {i : ℕ} :
  card_quot (P ^ i) = card_quot P ^ i :=
begin
  let b := module.free.choose_basis ℤ S,
  classical,
  induction i with i ih,
  { simp },
  letI := ideal.fintype_quotient_of_free_of_ne_bot (P ^ i.succ) (pow_ne_zero _ hP),
  letI := ideal.fintype_quotient_of_free_of_ne_bot (P ^ i) (pow_ne_zero _ hP),
  letI := ideal.fintype_quotient_of_free_of_ne_bot P hP,
  have : P ^ (i + 1) < P ^ i := ideal.pow_succ_lt_pow hP i,
  suffices hquot : map (P ^ i.succ).mkq (P ^ i) ≃ S ⧸ P,
  { rw [pow_succ (card_quot P), ← ih, card_quot_apply (P ^ i.succ),
      ← card_quotient_mul_card_quotient (P ^ i) (P ^ i.succ) this.le,
      card_quot_apply (P ^ i), card_quot_apply P],
    congr' 1,
    rw fintype.card_eq,
    exact ⟨hquot⟩ },
  choose a a_mem a_not_mem using set_like.exists_of_lt this,
  choose f g hg hf using λ c (hc : c ∈ P ^ i),
    ideal.exists_mul_add_mem_pow_succ hP a c a_mem a_not_mem hc,
  choose k hk_mem hk_eq using λ c' (hc' : c' ∈ (map (mkq (P ^ i.succ)) (P ^ i))),
    submodule.mem_map.mp hc',
  refine equiv.of_bijective (λ c', quotient.mk' (f (k c' c'.prop) (hk_mem c' c'.prop))) ⟨_, _⟩,
  { rintros ⟨c₁', hc₁'⟩ ⟨c₂', hc₂'⟩ h,
    rw [subtype.mk_eq_mk, ← hk_eq _ hc₁', ← hk_eq _ hc₂', mkq_apply, mkq_apply,
        submodule.quotient.eq, ← hf _ (hk_mem _ hc₁'), ← hf _ (hk_mem _ hc₂')],
    refine ideal.mul_add_mem_pow_succ_inj _ _ _ _ _ _ a_mem (hg _ _) (hg _ _) _,
    simpa only [submodule.quotient.mk'_eq_mk, submodule.quotient.mk'_eq_mk, submodule.quotient.eq]
      using h, },
  { intros d',
    refine quotient.induction_on' d' (λ d, _),
    have hd' := mem_map.mpr ⟨a * d, ideal.mul_mem_right d _ a_mem, rfl⟩,
    refine ⟨⟨_, hd'⟩, _⟩,
    simp only [submodule.quotient.mk'_eq_mk, ideal.quotient.mk_eq_mk, ideal.quotient.eq,
        subtype.coe_mk],
    refine ideal.mul_add_mem_pow_succ_unique hP a _ _ _ _ a_not_mem
      (hg _ (hk_mem _ hd'))
      (zero_mem _)
      _,
    rw [hf, add_zero],
    exact (submodule.quotient.eq _).mp (hk_eq _ hd') }
end

end P_prime

/-- Multiplicativity of the ideal norm in number rings. -/
theorem card_quot_mul [is_dedekind_domain S] [module.free ℤ S] [module.finite ℤ S] (I J : ideal S) :
  card_quot (I * J) = card_quot I * card_quot J :=
begin
  let b := module.free.choose_basis ℤ S,
  casesI is_empty_or_nonempty (module.free.choose_basis_index ℤ S),
  { haveI : subsingleton S := function.surjective.subsingleton b.repr.to_equiv.symm.surjective,
    nontriviality S,
    exfalso,
    exact not_nontrivial_iff_subsingleton.mpr ‹subsingleton S› ‹nontrivial S›, },
  haveI : infinite S := infinite.of_surjective _ b.repr.to_equiv.surjective,
  exact unique_factorization_monoid.multiplicative_of_coprime card_quot I J
    (card_quot_bot _ _)
    (λ I J hI, by simp [ideal.is_unit_iff.mp hI, ideal.mul_top])
    (λ I i hI, have ideal.is_prime I := ideal.is_prime_of_prime hI,
              by exactI card_quot_pow_of_prime hI.ne_zero)
    (λ I J hIJ, card_quot_mul_of_coprime (ideal.is_unit_iff.mp (hIJ _
      (ideal.dvd_iff_le.mpr le_sup_left)
      (ideal.dvd_iff_le.mpr le_sup_right))))
end

/-- The absolute norm of the ideal `I : ideal R` is the cardinality of the quotient `R ⧸ I`. -/
noncomputable def ideal.abs_norm [infinite S] [is_dedekind_domain S]
  [module.free ℤ S] [module.finite ℤ S] :
  ideal S →*₀ ℕ :=
{ to_fun := submodule.card_quot,
  map_mul' := λ I J, by rw card_quot_mul,
  map_one' := by rw [ideal.one_eq_top, card_quot_top],
  map_zero' := by rw [ideal.zero_eq_bot, card_quot_bot] }

namespace ideal

variables [infinite S] [is_dedekind_domain S] [module.free ℤ S] [module.finite ℤ S]

lemma abs_norm_apply (I : ideal S) : abs_norm I = card_quot I := rfl

@[simp] lemma abs_norm_bot : abs_norm (⊥ : ideal S) = 0 :=
by rw [← ideal.zero_eq_bot, _root_.map_zero]

@[simp] lemma abs_norm_top : abs_norm (⊤ : ideal S) = 1 :=
by rw [← ideal.one_eq_top, _root_.map_one]

@[simp] lemma abs_norm_eq_one_iff {I : ideal S} : abs_norm I = 1 ↔ I = ⊤ :=
by rw [abs_norm_apply, card_quot_eq_one_iff]

/-- Let `e : S ≃ I` be an additive isomorphism (therefore a `ℤ`-linear equiv).
Then an alternative way to compute the norm of `I` is given by taking the determinant of `e`.
See `nat_abs_det_basis_change` for a more familiar formulation of this result. -/
theorem nat_abs_det_equiv (I : ideal S) {E : Type*} [add_equiv_class E S I] (e : E) :
  int.nat_abs (linear_map.det
      ((submodule.subtype I).restrict_scalars ℤ ∘ₗ add_monoid_hom.to_int_linear_map (e : S →+ I))) =
  ideal.abs_norm I :=
begin
  -- `S ⧸ I` might be infinite if `I = ⊥`, but then `e` can't be an equiv.
  by_cases hI : I = ⊥,
  { unfreezingI { subst hI },
    have : (1 : S) ≠ 0 := one_ne_zero,
    have : (1 : S) = 0 := equiv_like.injective e (subsingleton.elim _ _),
    contradiction },

  let ι := module.free.choose_basis_index ℤ S,
  let b := module.free.choose_basis ℤ S,
  casesI is_empty_or_nonempty ι,
  { nontriviality S,
    exact (not_nontrivial_iff_subsingleton.mpr
      (function.surjective.subsingleton b.repr.to_equiv.symm.surjective)
      (by apply_instance)).elim },

  -- Thus `(S ⧸ I)` is isomorphic to a product of `zmod`s, so it is a fintype.
  letI := ideal.fintype_quotient_of_free_of_ne_bot I hI,
  -- Use the Smith normal form to choose a nice basis for `I`.
  letI := classical.dec_eq ι,
  let a := I.smith_coeffs b hI,
  let b' := I.ring_basis b hI,
  let ab := I.self_basis b hI,
  have ab_eq := I.self_basis_def b hI,
  let e' : S ≃ₗ[ℤ] I := b'.equiv ab (equiv.refl _),
  let f : S →ₗ[ℤ] S := (I.subtype.restrict_scalars ℤ).comp (e' : S →ₗ[ℤ] I),
  let f_apply : ∀ x, f x = b'.equiv ab (equiv.refl _) x := λ x, rfl,
  suffices : (linear_map.det f).nat_abs = ideal.abs_norm I,
  { calc  (linear_map.det ((submodule.subtype I).restrict_scalars ℤ ∘ₗ _)).nat_abs
        = (linear_map.det ((submodule.subtype I).restrict_scalars ℤ ∘ₗ
            (↑(add_equiv.to_int_linear_equiv ↑e) : S →ₗ[ℤ] I))).nat_abs : rfl
    ... = (linear_map.det ((submodule.subtype I).restrict_scalars ℤ ∘ₗ _)).nat_abs :
      int.nat_abs_eq_iff_associated.mpr (linear_map.associated_det_comp_equiv _ _ _)
    ... = abs_norm I : this },

  have ha : ∀ i, f (b' i) = a i • b' i,
  { intro i, rw [f_apply, b'.equiv_apply, equiv.refl_apply, ab_eq] },
  have mem_I_iff : ∀ x, x ∈ I ↔ ∀ i, a i ∣ b'.repr x i,
  { intro x, simp_rw [ab.mem_ideal_iff', ab_eq],
    have : ∀ (c : ι → ℤ) i, b'.repr (∑ (j : ι), c j • a j • b' j) i = a i * c i,
    { intros c i,
      simp only [← mul_action.mul_smul, b'.repr_sum_self, mul_comm] },
    split,
    { rintro ⟨c, rfl⟩ i, exact ⟨c i, this c i⟩ },
    { rintros ha,
      choose c hc using ha, exact ⟨c, b'.ext_elem (λ i, trans (hc i) (this c i).symm)⟩ } },

  -- `det f` is equal to `∏ i, a i`,
  letI := classical.dec_eq ι,
  calc  int.nat_abs (linear_map.det f)
      = int.nat_abs (linear_map.to_matrix b' b' f).det : by rw linear_map.det_to_matrix
  ... = int.nat_abs (matrix.diagonal a).det : _
  ... = int.nat_abs (∏ i, a i) : by rw matrix.det_diagonal
  ... = ∏ i, int.nat_abs (a i) : map_prod int.nat_abs_hom a finset.univ
  ... = fintype.card (S ⧸ I) : _
  ... = abs_norm I : (submodule.card_quot_apply _).symm,
  -- since `linear_map.to_matrix b' b' f` is the diagonal matrix with `a` along the diagonal.
  { congr, ext i j,
    rw [linear_map.to_matrix_apply, ha, linear_equiv.map_smul, basis.repr_self, finsupp.smul_single,
        smul_eq_mul, mul_one],
    by_cases h : i = j,
    { rw [h, matrix.diagonal_apply_eq, finsupp.single_eq_same] },
    { rw [matrix.diagonal_apply_ne _ h, finsupp.single_eq_of_ne (ne.symm h)] } },

  -- Now we map everything through the linear equiv `S ≃ₗ (ι → ℤ)`,
  -- which maps `(S ⧸ I)` to `Π i, zmod (a i).nat_abs`.
  haveI : ∀ i, ne_zero ((a i).nat_abs) := λ i,
    ⟨int.nat_abs_ne_zero_of_ne_zero (ideal.smith_coeffs_ne_zero b I hI i)⟩,
  simp_rw [fintype.card_eq.mpr ⟨(ideal.quotient_equiv_pi_zmod I b hI).to_equiv⟩, fintype.card_pi,
           zmod.card] ,
end

/-- Let `b` be a basis for `S` over `ℤ` and `bI` a basis for `I` over `ℤ` of the same dimension.
Then an alternative way to compute the norm of `I` is given by taking the determinant of `bI`
over `b`. -/
theorem nat_abs_det_basis_change {ι : Type*} [fintype ι] [decidable_eq ι]
  (b : basis ι ℤ S) (I : ideal S) (bI : basis ι ℤ I) :
  (b.det (coe ∘ bI)).nat_abs = ideal.abs_norm I :=
begin
  let e := b.equiv bI (equiv.refl _),
  calc (b.det ((submodule.subtype I).restrict_scalars ℤ ∘ bI)).nat_abs
      = (linear_map.det ((submodule.subtype I).restrict_scalars ℤ ∘ₗ (e : S →ₗ[ℤ] I))).nat_abs
    : by rw basis.det_comp_basis
  ... = _ : nat_abs_det_equiv I e
end

@[simp]
lemma abs_norm_span_singleton (r : S) :
  abs_norm (span ({r} : set S)) = (algebra.norm ℤ r).nat_abs :=
begin
  rw algebra.norm_apply,
  by_cases hr : r = 0,
  { simp only [hr, ideal.span_zero, algebra.coe_lmul_eq_mul, eq_self_iff_true, ideal.abs_norm_bot,
      linear_map.det_zero'', set.singleton_zero, _root_.map_zero, int.nat_abs_zero] },
  letI := ideal.fintype_quotient_of_free_of_ne_bot (span {r}) (mt span_singleton_eq_bot.mp hr),
  let b := module.free.choose_basis ℤ S,
  rw [← nat_abs_det_equiv _ (b.equiv (basis_span_singleton b hr) (equiv.refl _))],
  swap, apply_instance,
  congr,
  refine b.ext (λ i, _),
  simp
end

lemma abs_norm_dvd_abs_norm_of_le {I J : ideal S} (h : J ≤ I) : I.abs_norm ∣ J.abs_norm :=
map_dvd abs_norm (dvd_iff_le.mpr h)

lemma abs_norm_dvd_norm_of_mem {I : ideal S} {x : S} (h : x ∈ I) : ↑I.abs_norm ∣ algebra.norm ℤ x :=
begin
  rw [← int.dvd_nat_abs, ← abs_norm_span_singleton x, int.coe_nat_dvd],
  exact abs_norm_dvd_abs_norm_of_le ((span_singleton_le_iff_mem _).mpr h)
end

@[simp]
lemma abs_norm_span_insert (r : S) (s : set S) :
  abs_norm (span (insert r s)) ∣ gcd (abs_norm (span s)) (algebra.norm ℤ r).nat_abs :=
(dvd_gcd_iff _ _ _).mpr
  ⟨abs_norm_dvd_abs_norm_of_le (span_mono (set.subset_insert _ _)),
  trans
    (abs_norm_dvd_abs_norm_of_le (span_mono (set.singleton_subset_iff.mpr (set.mem_insert _ _))))
    (by rw abs_norm_span_singleton)⟩

lemma irreducible_of_irreducible_abs_norm {I : ideal S} (hI : irreducible I.abs_norm) :
  irreducible I :=
irreducible_iff.mpr
  ⟨λ h, hI.not_unit (by simpa only [ideal.is_unit_iff, nat.is_unit_iff, abs_norm_eq_one_iff]
      using h),
   by rintro a b rfl; simpa only [ideal.is_unit_iff, nat.is_unit_iff, abs_norm_eq_one_iff]
      using hI.is_unit_or_is_unit (_root_.map_mul abs_norm a b)⟩

lemma is_prime_of_irreducible_abs_norm {I : ideal S} (hI : irreducible I.abs_norm) :
  I.is_prime :=
is_prime_of_prime (unique_factorization_monoid.irreducible_iff_prime.mp
  (irreducible_of_irreducible_abs_norm hI))

lemma prime_of_irreducible_abs_norm_span {a : S} (ha : a ≠ 0)
  (hI : irreducible (ideal.span ({a} : set S)).abs_norm) :
  prime a :=
(ideal.span_singleton_prime ha).mp (is_prime_of_irreducible_abs_norm hI)

lemma abs_norm_mem (I : ideal S) : ↑I.abs_norm ∈ I :=
by rw [abs_norm_apply, card_quot, ← ideal.quotient.eq_zero_iff_mem, map_nat_cast,
       quotient.index_eq_zero]

end ideal

end ring_of_integers

end abs_norm

section span_norm

namespace ideal

open submodule

variables (R : Type*) [comm_ring R] {S : Type*} [comm_ring S] [algebra R S]

/-- `ideal.span_norm R (I : ideal S)` is the ideal generated by mapping `algebra.norm R` over `I`.

See also `ideal.rel_norm`.
-/
def span_norm (I : ideal S) : ideal R :=
ideal.span (algebra.norm R '' (I : set S))

@[simp] lemma span_norm_bot
  [nontrivial S] [module.free R S] [module.finite R S] :
  span_norm R (⊥ : ideal S) = ⊥ :=
span_eq_bot.mpr (λ x hx, by simpa using hx)

variables {R}

@[simp] lemma span_norm_eq_bot_iff [is_domain R] [is_domain S]
  [module.free R S] [module.finite R S] {I : ideal S} :
  span_norm R I = ⊥ ↔ I = ⊥ :=
begin
  simp only [span_norm, ideal.span_eq_bot, set.mem_image, set_like.mem_coe, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂,
    algebra.norm_eq_zero_iff_of_basis (module.free.choose_basis R S), @eq_bot_iff _ _ _ I,
    set_like.le_def],
  refl
end

variables (R)

lemma norm_mem_span_norm {I : ideal S} (x : S) (hx : x ∈ I) : algebra.norm R x ∈ I.span_norm R :=
subset_span (set.mem_image_of_mem _ hx)

@[simp] lemma span_norm_singleton {r : S} :
  span_norm R (span ({r} : set S)) = span {algebra.norm R r} :=
le_antisymm
  (span_le.mpr (λ x hx, mem_span_singleton.mpr begin
    obtain ⟨x, hx', rfl⟩ := (set.mem_image _ _ _).mp hx,
    exact map_dvd _ (mem_span_singleton.mp hx')
  end))
  ((span_singleton_le_iff_mem _).mpr (norm_mem_span_norm _ _ (mem_span_singleton_self _)))

@[simp] lemma span_norm_top : span_norm R (⊤ : ideal S) = ⊤ :=
by simp [← ideal.span_singleton_one]

lemma map_span_norm (I : ideal S) {T : Type*} [comm_ring T] (f : R →+* T) :
  map f (span_norm R I) = span ((f ∘ algebra.norm R) '' (I : set S)) :=
by rw [span_norm, map_span, set.image_image]

@[mono]
lemma span_norm_mono {I J : ideal S} (h : I ≤ J) : span_norm R I ≤ span_norm R J :=
ideal.span_mono (set.monotone_image h)

lemma span_norm_localization (I : ideal S) [module.finite R S] [module.free R S]
  (M : submonoid R) {Rₘ : Type*} (Sₘ : Type*)
  [comm_ring Rₘ] [algebra R Rₘ] [comm_ring Sₘ] [algebra S Sₘ]
  [algebra Rₘ Sₘ] [algebra R Sₘ] [is_scalar_tower R Rₘ Sₘ] [is_scalar_tower R S Sₘ]
  [is_localization M Rₘ] [is_localization (algebra.algebra_map_submonoid S M) Sₘ] :
  span_norm Rₘ (I.map (algebra_map S Sₘ)) = (span_norm R I).map (algebra_map R Rₘ) :=
begin
  casesI h : subsingleton_or_nontrivial R,
  { haveI := is_localization.unique R Rₘ M,
    simp },
  let b := module.free.choose_basis R S,
  rw map_span_norm,
  refine span_eq_span (set.image_subset_iff.mpr _) (set.image_subset_iff.mpr _),
  { rintros a' ha',
    simp only [set.mem_preimage, submodule_span_eq, ← map_span_norm, set_like.mem_coe,
        is_localization.mem_map_algebra_map_iff (algebra.algebra_map_submonoid S M) Sₘ,
        is_localization.mem_map_algebra_map_iff M Rₘ, prod.exists]
      at ⊢ ha',
    obtain ⟨⟨a, ha⟩, ⟨_, ⟨s, hs, rfl⟩⟩, has⟩ := ha',
    refine ⟨⟨algebra.norm R a, norm_mem_span_norm _ _ ha⟩,
            ⟨s ^ fintype.card (module.free.choose_basis_index R S), pow_mem hs _⟩, _⟩,
    swap,
    simp only [submodule.coe_mk, subtype.coe_mk, map_pow] at ⊢ has,
    apply_fun algebra.norm Rₘ at has,
    rwa [_root_.map_mul, ← is_scalar_tower.algebra_map_apply,
        is_scalar_tower.algebra_map_apply R Rₘ,
        algebra.norm_algebra_map_of_basis (b.localization_localization Rₘ M Sₘ),
        algebra.norm_localization R M a] at has,
    all_goals { apply_instance } },
  { intros a ha,
    rw [set.mem_preimage, function.comp_app, ← algebra.norm_localization R M a],
    exact subset_span (set.mem_image_of_mem _ (mem_map_of_mem _ ha)),
    all_goals { apply_instance } },
end

lemma span_norm_mul_span_norm_le (I J : ideal S) :
  span_norm R I * span_norm R J ≤ span_norm R (I * J) :=
begin
  rw [span_norm, span_norm, span_norm, ideal.span_mul_span', ← set.image_mul],
  refine ideal.span_mono (set.monotone_image _),
  rintros _ ⟨x, y, hxI, hyJ, rfl⟩,
  exact ideal.mul_mem_mul hxI hyJ
end

/-- This condition `eq_bot_or_top` is equivalent to being a field.
However, `span_norm_mul_of_field` is harder to apply since we'd need to upgrade a `comm_ring R`
instance to a `field R` instance. -/
lemma span_norm_mul_of_bot_or_top [is_domain R] [is_domain S]
  [module.free R S] [module.finite R S]
  (eq_bot_or_top : ∀ I : ideal R, I = ⊥ ∨ I = ⊤)
  (I J : ideal S) :
  span_norm R (I * J) = span_norm R I * span_norm R J :=
begin
  refine le_antisymm _ (span_norm_mul_span_norm_le _ _ _),
  cases eq_bot_or_top (span_norm R I) with hI hI,
  { rw [hI, span_norm_eq_bot_iff.mp hI, bot_mul, span_norm_bot],
    exact bot_le },
  rw [hI, ideal.top_mul],
  cases eq_bot_or_top (span_norm R J) with hJ hJ,
  { rw [hJ, span_norm_eq_bot_iff.mp hJ, mul_bot, span_norm_bot],
    exact bot_le },
  rw hJ,
  exact le_top
end

@[simp] lemma span_norm_mul_of_field {K : Type*} [field K] [algebra K S] [is_domain S]
  [module.finite K S] (I J : ideal S) :
  span_norm K (I * J) = span_norm K I * span_norm K J :=
span_norm_mul_of_bot_or_top K eq_bot_or_top I J

variables [is_domain R] [is_domain S] [is_dedekind_domain R] [is_dedekind_domain S]
variables [module.finite R S] [module.free R S]

/-- Multiplicativity of `ideal.span_norm`. simp-normal form is `map_mul (ideal.rel_norm R)`. -/
lemma span_norm_mul (I J : ideal S) : span_norm R (I * J) = span_norm R I * span_norm R J :=
begin
  nontriviality R,
  casesI subsingleton_or_nontrivial S,
  { have : ∀ I : ideal S, I = ⊤ := λ I, subsingleton.elim I ⊤,
    simp [this I, this J, this (I * J)] },
  refine eq_of_localization_maximal _,
  unfreezingI { intros P hP },
  by_cases hP0 : P = ⊥,
  { unfreezingI { subst hP0 },
    rw span_norm_mul_of_bot_or_top,
    intros I,
    refine or_iff_not_imp_right.mpr (λ hI, _),
    exact (hP.eq_of_le hI bot_le).symm },
  let P' := algebra.algebra_map_submonoid S P.prime_compl,
  letI : algebra (localization.at_prime P) (localization P') :=
    localization_algebra P.prime_compl S,
  haveI : is_scalar_tower R (localization.at_prime P) (localization P') :=
    is_scalar_tower.of_algebra_map_eq (λ x, (is_localization.map_eq _ _).symm),
  have h : P' ≤ S⁰ :=
    map_le_non_zero_divisors_of_injective _ (no_zero_smul_divisors.algebra_map_injective _ _)
      P.prime_compl_le_non_zero_divisors,
  haveI : is_domain (localization P') := is_localization.is_domain_localization h,
  haveI : is_dedekind_domain (localization P') := is_localization.is_dedekind_domain S h _,
  letI := classical.dec_eq (ideal (localization P')),
  haveI : is_principal_ideal_ring (localization P') :=
    is_dedekind_domain.is_principal_ideal_ring_localization_over_prime S P hP0,
  rw [ideal.map_mul, ← span_norm_localization R I P.prime_compl (localization P'),
    ← span_norm_localization R J P.prime_compl (localization P'),
    ← span_norm_localization R (I * J) P.prime_compl (localization P'), ideal.map_mul,
    ← (I.map _).span_singleton_generator, ← (J.map _).span_singleton_generator,
    span_singleton_mul_span_singleton, span_norm_singleton, span_norm_singleton,
    span_norm_singleton, span_singleton_mul_span_singleton, _root_.map_mul],
  repeat { apply_instance },
  repeat { assumption },
end

/-- The relative norm `ideal.rel_norm R (I : ideal S)`, where `R` and `S` are Dedekind domains,
and `S` is an extension of `R` that is finite and free as a module. -/
def rel_norm : ideal S →*₀ ideal R :=
{ to_fun := span_norm R,
  map_zero' := span_norm_bot R,
  map_one' := by rw [one_eq_top, span_norm_top R, one_eq_top],
  map_mul' := span_norm_mul R }

lemma rel_norm_apply (I : ideal S) :
  rel_norm R I = span (algebra.norm R '' (I : set S) : set R) :=
rfl

@[simp] lemma span_norm_eq (I : ideal S) : span_norm R I = rel_norm R I := rfl

@[simp] lemma rel_norm_bot : rel_norm R (⊥ : ideal S) = ⊥ :=
by simpa only [zero_eq_bot] using map_zero (rel_norm R : ideal S →*₀ _)

@[simp] lemma rel_norm_top : rel_norm R (⊤ : ideal S) = ⊤ :=
by simpa only [one_eq_top] using map_one (rel_norm R : ideal S →*₀ _)

variables {R}

@[simp] lemma rel_norm_eq_bot_iff {I : ideal S} : rel_norm R I = ⊥ ↔ I = ⊥ :=
span_norm_eq_bot_iff

variables (R)

lemma norm_mem_rel_norm (I : ideal S) {x : S} (hx : x ∈ I) : algebra.norm R x ∈ rel_norm R I :=
norm_mem_span_norm R x hx

@[simp] lemma rel_norm_singleton (r : S) :
  rel_norm R (span ({r} : set S)) = span {algebra.norm R r} :=
span_norm_singleton R

lemma map_rel_norm (I : ideal S) {T : Type*} [comm_ring T] (f : R →+* T) :
  map f (rel_norm R I) = span ((f ∘ algebra.norm R) '' (I : set S)) :=
map_span_norm R I f

@[mono]
lemma rel_norm_mono {I J : ideal S} (h : I ≤ J) : rel_norm R I ≤ rel_norm R J :=
span_norm_mono R h

end ideal

end span_norm
