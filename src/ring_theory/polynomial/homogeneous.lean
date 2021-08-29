/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/

import data.mv_polynomial
import algebra.algebra.operations
import data.fintype.card
import algebra.direct_sum.algebra

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`.

## Main definitions/lemmas

* `is_homogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneous_submodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneous_component n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneous_component`: every polynomial is the sum of its homogeneous components

-/

open_locale big_operators

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

/-
TODO
* create definition for `∑ i in d.support, d i`
* show that `mv_polynomial σ R ≃ₐ[R] ⨁ i, homogeneous_submodule σ R i`
-/

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`. -/
def is_homogeneous [comm_semiring R] (φ : mv_polynomial σ R) (n : ℕ) :=
∀ ⦃d⦄, coeff d φ ≠ 0 → ∑ i in d.support, d i = n

variables (σ R)

/-- The submodule of homogeneous `mv_polynomial`s of degree `n`. -/
noncomputable def homogeneous_submodule [comm_semiring R] (n : ℕ) :
  submodule R (mv_polynomial σ R) :=
{ carrier := { x | x.is_homogeneous n },
  smul_mem' := λ r a ha c hc, begin
    rw coeff_smul at hc,
    apply ha,
    intro h,
    apply hc,
    rw h,
    exact smul_zero r,
  end,
  zero_mem' := λ d hd, false.elim (hd $ coeff_zero _),
  add_mem' := λ a b ha hb c hc, begin
    rw coeff_add at hc,
    obtain h|h : coeff c a ≠ 0 ∨ coeff c b ≠ 0,
    { contrapose! hc, simp only [hc, add_zero] },
    { exact ha h },
    { exact hb h }
  end }

variables {σ R}

@[simp] lemma mem_homogeneous_submodule [comm_semiring R] (n : ℕ) (p : mv_polynomial σ R) :
  p ∈ homogeneous_submodule σ R n ↔ p.is_homogeneous n := iff.rfl

variables (σ R)

/-- While equal, the former has a convenient definitional reduction. -/
lemma homogenous_submodule_eq_finsupp_supported [comm_semiring R] (n : ℕ) :
  homogeneous_submodule σ R n = finsupp.supported _ R {d | ∑ i in d.support, d i = n} :=
begin
  ext,
  rw [finsupp.mem_supported, set.subset_def],
  simp only [finsupp.mem_support_iff, finset.mem_coe],
  refl,
end

variables {σ R}

lemma homogenous_submodule_mul [comm_semiring R] (m n : ℕ) :
  homogeneous_submodule σ R m * homogeneous_submodule σ R n ≤ homogeneous_submodule σ R (m + n) :=
begin
  rw submodule.mul_le,
  intros φ hφ ψ hψ c hc,
  rw [coeff_mul] at hc,
  obtain ⟨⟨d, e⟩, hde, H⟩ := finset.exists_ne_zero_of_sum_ne_zero hc,
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0,
  { contrapose! H,
    by_cases h : coeff d φ = 0;
    simp only [*, ne.def, not_false_iff, zero_mul, mul_zero] at * },
  specialize hφ aux.1, specialize hψ aux.2,
  rw finsupp.mem_antidiagonal at hde,
  classical,
  have hd' : d.support ⊆ d.support ∪ e.support := finset.subset_union_left _ _,
  have he' : e.support ⊆ d.support ∪ e.support := finset.subset_union_right _ _,
  rw [← hde, ← hφ, ← hψ, finset.sum_subset (finsupp.support_add),
    finset.sum_subset hd', finset.sum_subset he', ← finset.sum_add_distrib],
  { congr },
  all_goals { intros i hi, apply finsupp.not_mem_support_iff.mp },
end

section
variables [comm_semiring R]

variables {σ R}

lemma is_homogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : ∑ i in d.support, d i = n) :
  is_homogeneous (monomial d r) n :=
begin
  intros c hc,
  classical,
  rw coeff_monomial at hc,
  split_ifs at hc with h,
  { subst c, exact hn },
  { contradiction }
end
variables (σ) {R}

@[simp] lemma is_homogeneous_C (r : R) :
  is_homogeneous (C r : mv_polynomial σ R) 0 :=
begin
  apply is_homogeneous_monomial,
  simp only [finsupp.zero_apply, finset.sum_const_zero],
end

variables (σ R)

@[simp] lemma is_homogeneous_zero (n : ℕ) : is_homogeneous (0 : mv_polynomial σ R) n :=
(homogeneous_submodule σ R n).zero_mem

lemma is_homogeneous_one : is_homogeneous (1 : mv_polynomial σ R) 0 :=
is_homogeneous_C _ _

lemma is_homogeneous_C_iff (r : R) (i : ℕ) :
  is_homogeneous (C r : mv_polynomial σ R) i ↔ i = 0 ∨ r = 0 :=
begin
  by_cases hi : i = 0,
  { simp [hi] },
  by_cases hr : r = 0,
  { simp [hi, hr] },
  simp only [iff_false, hi, hr, false_or],
  refine mt (λ hC, _) hi,
  have : coeff 0 (C r : mv_polynomial σ R) ≠ 0 := by rwa [coeff_zero_C],
  simpa [eq_comm] using hC this,
end

variables {σ} (R)

lemma is_homogeneous_X (i : σ) :
  is_homogeneous (X i : mv_polynomial σ R) 1 :=
begin
  apply is_homogeneous_monomial,
  simp only [finsupp.support_single_ne_zero one_ne_zero, finset.sum_singleton],
  exact finsupp.single_eq_same
end

end

namespace is_homogeneous
variables [comm_semiring R] {φ ψ : mv_polynomial σ R} {m n : ℕ}

lemma coeff_eq_zero (hφ : is_homogeneous φ n) (d : σ →₀ ℕ) (hd : ∑ i in d.support, d i ≠ n) :
  coeff d φ = 0 :=
by { have aux := mt (@hφ d) hd, classical, rwa not_not at aux }

lemma inj_right (hm : is_homogeneous φ m) (hn : is_homogeneous φ n) (hφ : φ ≠ 0) :
  m = n :=
begin
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ,
  rw [← hm hd, ← hn hd]
end

lemma add (hφ : is_homogeneous φ n) (hψ : is_homogeneous ψ n) :
  is_homogeneous (φ + ψ) n :=
(homogeneous_submodule σ R n).add_mem hφ hψ

lemma sum {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ℕ)
  (h : ∀ i ∈ s, is_homogeneous (φ i) n) :
  is_homogeneous (∑ i in s, φ i) n :=
(homogeneous_submodule σ R n).sum_mem h

lemma mul (hφ : is_homogeneous φ m) (hψ : is_homogeneous ψ n) :
  is_homogeneous (φ * ψ) (m + n) :=
homogenous_submodule_mul m n $ submodule.mul_mem_mul hφ hψ

lemma prod {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ι → ℕ)
  (h : ∀ i ∈ s, is_homogeneous (φ i) (n i)) :
  is_homogeneous (∏ i in s, φ i) (∑ i in s, n i) :=
begin
  classical,
  revert h,
  apply finset.induction_on s,
  { intro, simp only [is_homogeneous_one, finset.sum_empty, finset.prod_empty] },
  { intros i s his IH h,
    simp only [his, finset.prod_insert, finset.sum_insert, not_false_iff],
    apply (h i (finset.mem_insert_self _ _)).mul (IH _),
    intros j hjs,
    exact h j (finset.mem_insert_of_mem hjs) }
end

lemma total_degree (hφ : is_homogeneous φ n) (h : φ ≠ 0) :
  total_degree φ = n :=
begin
  rw total_degree,
  apply le_antisymm,
  { apply finset.sup_le,
    intros d hd,
    rw mem_support_iff at hd,
    rw [finsupp.sum, hφ hd], },
  { obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h,
    simp only [← hφ hd, finsupp.sum],
    replace hd := finsupp.mem_support_iff.mpr hd,
    exact finset.le_sup hd, }
end

/--
The homogenous submodules form a graded ring. This instance is used by `direct_sum.comm_semiring`
and `direct_sum.algebra`. -/
noncomputable instance homogeneous_submodule.gcomm_monoid :
  direct_sum.gcomm_monoid (λ i, homogeneous_submodule σ R i) :=
direct_sum.gcomm_monoid.of_submodules _
  (is_homogeneous_one σ R)
  (λ i j hi hj, is_homogeneous.mul hi.prop hj.prop)

open_locale direct_sum
noncomputable example : comm_semiring (⨁ i, homogeneous_submodule σ R i) := infer_instance
noncomputable example : algebra R (⨁ i, homogeneous_submodule σ R i) := infer_instance

end is_homogeneous

section
noncomputable theory
open_locale classical
open finset

open_locale direct_sum

/-- A version of `homogenous_component` that maps into `homogeneous_submodule σ R n`. -/
def homogeneous_component' [comm_semiring R] (n : ℕ) :
  mv_polynomial σ R →ₗ[R] homogeneous_submodule σ R n :=
let f := finsupp.restrict_dom R R {d : σ →₀ ℕ | ∑ i in d.support, d i = n} in
(submodule.of_le $ (homogenous_submodule_eq_finsupp_supported _ _ _).symm.le).comp f

/-- Split a polynomial into a direct sum of homogenous components.

TODO: Promote this to an `alg_equiv`. -/
def to_homogeneous_components [comm_semiring R] :
  mv_polynomial σ R →ₐ[R] (⨁ i, homogeneous_submodule σ R i) :=
begin
  refine add_monoid_algebra.lift _ _ _ _,
  exact {
    to_fun := λ d, direct_sum.of (λ i, homogeneous_submodule σ R i) (d.to_add.sum $ λ i x, x)
      ⟨monomial d.to_add 1, is_homogeneous_monomial _ _ _ rfl⟩,
    map_one' := rfl, --by simp,
    map_mul' := λ d₁ d₂, _, --by simp,
  },
  refine (dfinsupp.single_eq_of_sigma_eq (sigma.subtype_ext _ _)).trans
    (direct_sum.of_mul_of _ _).symm; dsimp,
  exact finsupp.sum_add_index (λ _, rfl) (λ _ _ _, rfl),
  rw [monomial_mul, mul_one],
end


@[simp]
lemma to_homogeneous_components_monomial_one [comm_semiring R] (d : σ →₀ ℕ) :
  to_homogeneous_components (monomial d (1 : R)) =
    direct_sum.of (λ i, homogeneous_submodule σ R i) (d.sum $ λ i x, x)
      ⟨monomial d 1, is_homogeneous_monomial _ _ _ rfl⟩ :=
(add_monoid_algebra.lift_single _ _ _).trans (one_smul _ _)

@[simp]
lemma to_homogeneous_components_X [comm_semiring R] (d : σ) :
  to_homogeneous_components (mv_polynomial.X d : mv_polynomial σ R) =
    direct_sum.of (λ i, homogeneous_submodule σ R i) 1 ⟨mv_polynomial.X d, is_homogeneous_X _ _⟩ :=
(to_homogeneous_components_monomial_one _).trans $
  dfinsupp.single_eq_of_sigma_eq $ sigma.subtype_ext (finsupp.sum_single_index rfl) rfl

#check submodule.span_induction


lemma is_homogeneous.induction [comm_semiring R]
  {x : mv_polynomial σ R} {i : ℕ} (hx : x.is_homogeneous i)
  {p : mv_polynomial σ R → Prop}
  (hmonomial : ∀ d r, p (monomial d r))
  (hadd : ∀ {i} (a b : mv_polynomial σ R), a.is_homogeneous i → b.is_homogeneous i → p a → p b → p (a + b))
  : p x :=
begin
  -- suffices : ∃ hx : x.is_homogeneous i, p x,
  -- { obtain ⟨_, _⟩ := this,
  --   assumption},
  -- clear hx,
  induction x using mv_polynomial.induction_on',
  apply hC,
  { rw [is_homogeneous_C_iff] at hx,
    cases hx with hi hr,
    { subst hi, apply hC, },
    { subst hr,
      simpa using hC 0,
      exact (direct_sum.of _ _).map_zero.symm} },
end

lemma is_homogeneous.induction2 [comm_semiring R] {p : ∀ {x : mv_polynomial σ R} {i : ℕ}, x.is_homogeneous i → Prop}
  (hC : ∀ r, p (is_homogeneous_C _ r))
  (hX : ∀ d, p (is_homogeneous_X _ d))
  (hadd : ∀ {i} (a b : mv_polynomial σ R) (ha : a.is_homogeneous i) (hb : b.is_homogeneous i), p ha → p hb → p (ha.add hb))
  (hmul : ∀ {i j} (a b : mv_polynomial σ R) (ha : a.is_homogeneous i) (hb : b.is_homogeneous j),
    p ha → p hb → p (ha.mul hb))
  : ∀ {x : mv_polynomial σ R} {i : ℕ} (hx : x.is_homogeneous i), p hx :=
begin
  rintros i ⟨x, hx⟩,
  induction x using mv_polynomial.induction_on,
end

lemma homogeneous_submodule.induction  [comm_semiring R] {p : ∀ {i : ℕ}, homogeneous_submodule σ R i → Prop}
  (hC : ∀ r, p ⟨C r, is_homogeneous_C _ r⟩)
  (hX : ∀ d, p ⟨X d, is_homogeneous_X _ _⟩)
  (hadd : ∀ {i} (a b : homogeneous_submodule σ R i), p a → p b → p (a + b))
  (hmul : ∀ {i j} (a : homogeneous_submodule σ R i) (b : homogeneous_submodule σ R j),
    p a → p b → p ⟨a * b, a.prop.mul b.prop⟩)
  : ∀ (i : ℕ) (x : homogeneous_submodule σ R i), p x :=
begin
  rintros i ⟨x, hx⟩,
  induction x using mv_polynomial.induction_on,
end

@[simp]
lemma to_homogeneous_components_monomial_coe [comm_semiring R] (i : ℕ) (x : homogeneous_submodule σ R i) :
  to_homogeneous_components ↑x =
    direct_sum.of (λ i, homogeneous_submodule σ R i) i x :=
begin
  cases x with x hx,
  revert i,
  suffices : ∃ (f : mv_polynomial σ R → ℕ) (hx' : x ∈ homogeneous_submodule σ R (f x)),
    to_homogeneous_components x = (direct_sum.of (λ (i : ℕ), ↥(homogeneous_submodule σ R i)) (f x)) ⟨x, hx'⟩,

  clear hx,
  induction x using mv_polynomial.induction_on,
  { refine (alg_hom.commutes _ _).trans _,
    rw [mem_homogeneous_submodule, is_homogeneous_C_iff] at hx,
    cases hx with hi hr,
    { subst hi, refl, },
    { subst hr,
      simp only [mv_polynomial.C_0, ring_hom.map_zero],
      exact (direct_sum.of _ _).map_zero.symm} },
  case h_add : xp xq hp hq hx { simp,
    sorry},
  sorry,
  -- dsimp,
  -- suffices : to_homogeneous_components.to_linear_map.dom_restrict (homogeneous_submodule σ R i) =
  --   direct_sum.lof _ _ (λ i, homogeneous_submodule σ R i) i,
  -- exact linear_map.congr_fun this x,
  -- ext : 1,
end

#print add_submonoid.closure_induction'

/-- Assemble a polynomial from a direct sum of homogenous components.

TODO: Promote this to the inverse of `to_homogeneous_components`. -/
def of_homogeneous_components [comm_semiring R] :
  (⨁ i, homogeneous_submodule σ R i) →ₐ[R] mv_polynomial σ R :=
direct_sum.to_algebra R _ (λ i, submodule.subtype _) rfl (λ _ _ _ _, rfl) (λ r, rfl)

@[simp]
lemma of_homogeneous_components_of [comm_semiring R] (i : ℕ) (x : homogeneous_submodule σ R i) :
  of_homogeneous_components (direct_sum.of (λ i, homogeneous_submodule σ R i) i x) = x :=
direct_sum.to_add_monoid_of _ _ _

/-- `of_*` is the left-inverse of `to_*` -/
lemma of_to_homogeneous_components [comm_semiring R] :
  of_homogeneous_components.comp to_homogeneous_components = alg_hom.id R (mv_polynomial σ R) :=
begin
  ext : 1,
  dsimp,
  rw [to_homogeneous_components_X, of_homogeneous_components_of, subtype.coe_mk],
end

/-- `of_*` is the left-inverse of `to_*` -/
lemma to_of_homogeneous_components [comm_semiring R] :
  to_homogeneous_components.comp of_homogeneous_components =
    alg_hom.id R (⨁ i, homogeneous_submodule σ R i) :=
begin
  ext : 2,
  dsimp [direct_sum.lof_eq_of],
  rw of_homogeneous_components_of,
  -- TODO: need an ext lemma
  -- dsimp [direct_sum.lift_ring_hom],
  -- -- multiple stages of simp is hopefully faster?
  -- simp,
  -- simp [to_homogeneous_components, of_homogeneous_components],
  -- simp [homogeneous_component', direct_sum.to_module,
  -- linear_map.finsupp_sum_apply],
  -- exact finsupp.filter_single_of_pos _ rfl,
end

/-- `homogeneous_component n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneous_component` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneous_component [comm_semiring R] (n : ℕ) :
  mv_polynomial σ R →ₗ[R] mv_polynomial σ R :=
(submodule.subtype _).comp $ finsupp.restrict_dom _ _ {d | ∑ i in d.support, d i = n}

section homogeneous_component
open finset
variables [comm_semiring R] (n : ℕ) (φ : mv_polynomial σ R)

lemma coeff_homogeneous_component (d : σ →₀ ℕ) :
  coeff d (homogeneous_component n φ) = if ∑ i in d.support, d i = n then coeff d φ else 0 :=
by convert finsupp.filter_apply (λ d : σ →₀ ℕ, ∑ i in d.support, d i = n) φ d

lemma homogeneous_component_apply :
  homogeneous_component n φ =
  ∑ d in φ.support.filter (λ d, ∑ i in d.support, d i = n), monomial d (coeff d φ) :=
by convert finsupp.filter_eq_sum (λ d : σ →₀ ℕ, ∑ i in d.support, d i = n) φ

lemma homogeneous_component_is_homogeneous :
  (homogeneous_component n φ).is_homogeneous n :=
begin
  intros d hd,
  contrapose! hd,
  rw [coeff_homogeneous_component, if_neg hd]
end

lemma homogeneous_component_zero : homogeneous_component 0 φ = C (coeff 0 φ) :=
begin
  ext1 d,
  rcases em (d = 0) with (rfl|hd),
  { simp only [coeff_homogeneous_component, sum_eq_zero_iff, finsupp.zero_apply, if_true, coeff_C,
      eq_self_iff_true, forall_true_iff] },
  { rw [coeff_homogeneous_component, if_neg, coeff_C, if_neg (ne.symm hd)],
    simp only [finsupp.ext_iff, finsupp.zero_apply] at hd,
    simp [hd] }
end

lemma homogeneous_component_eq_zero' (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → ∑ i in d.support, d i ≠ n) :
  homogeneous_component n φ = 0 :=
begin
  rw [homogeneous_component_apply, sum_eq_zero],
  intros d hd, rw mem_filter at hd,
  exfalso, exact h _ hd.1 hd.2
end

lemma homogeneous_component_eq_zero (h : φ.total_degree < n) :
  homogeneous_component n φ = 0 :=
begin
  apply homogeneous_component_eq_zero',
  rw [total_degree, finset.sup_lt_iff] at h,
  { intros d hd, exact ne_of_lt (h d hd), },
  { exact lt_of_le_of_lt (nat.zero_le _) h, }
end

lemma sum_homogeneous_component :
  ∑ i in range (φ.total_degree + 1), homogeneous_component i φ = φ :=
begin
  ext1 d,
  suffices : φ.total_degree < d.support.sum d → 0 = coeff d φ,
    by simpa [coeff_sum, coeff_homogeneous_component],
  exact λ h, (coeff_eq_zero_of_total_degree_lt h).symm
end

end homogeneous_component

end

end mv_polynomial
