/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.basic
import analysis.normed_space.indicator_function
import analysis.normed.group.hom
import analysis.mean_inequalities
import analysis.mean_inequalities_pow
import topology.continuous_function.compact

/-!
# ℓp space and Lp space

This file describes properties of almost everywhere measurable functions with finite seminorm,
defined for `p:ℝ≥0∞` as `if (f = 0) then 0 else ∞` if `p=0`, `(∑ a, ∥f a∥^p) ^ (1/p)` for
`0 < p < ∞` and `⨆ a, ∥f a∥` for `p=∞`.

The Prop-valued `mem_ℓp f p` states that a function `f : Π i, E i` has finite seminorm according
to the above definition; that is, `f = 0` if `p = 0`, `summable (λ a, ∥f a∥^p)` if `0 < p < ∞`, and
`bdd_above (norm '' (set.range f))` if `p = ∞`.

The space `Lp E p` is the subtype of elements of `Π i : α, E i` which satisfy `mem_ℓp f p`. For
`1 ≤ p`, the seminorm is genuinely a norm and `Lp` is a complete metric space.

## Main definitions

* `mem_ℓp f p` : property that the function `f` satisfies, as appropriate, `f = 0` if `p = 0`,
  `summable (λ a, ∥f a∥^p)` if `0 < p < ∞`, and `bdd_above (norm '' (set.range f))` if `p = ∞`
* `Lp E p` : elements of `Π i : α, E i` such that `mem_ℓp f p`. Defined as an `add_subgroup` of
  `Π i : α, E i`.

## Notations

* `α →₁[μ] E` : the type `Lp E 1 μ`.
* `α →₂[μ] E` : the type `Lp E 2 μ`.

## Implementation

Since `Lp` is defined as an `add_subgroup`, dot notation does not work. Use `Lp.norm_neg f` to
say that `∥-f∥ = ∥f∥`, instead of the non-working `f.norm_neg`.

-/

noncomputable theory
open topological_space filter
open_locale nnreal ennreal big_operators topological_space

lemma fact_one_le_one_ennreal : fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_refl _⟩

lemma fact_one_le_two_ennreal : fact ((1 : ℝ≥0∞) ≤ 2) :=
⟨ennreal.coe_le_coe.2 (show (1 : ℝ≥0) ≤ 2, by norm_num)⟩

lemma fact_one_le_top_ennreal : fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩

local attribute [instance] fact_one_le_one_ennreal fact_one_le_two_ennreal fact_one_le_top_ennreal

variables {α G : Type*} {E : α → Type*} {F : α → Type*} {p q : ℝ≥0∞}
  [Π i, normed_group (E i)]
  [Π i, normed_group (F i)] [normed_group G]

section p_facts
variables (p)

-- lemma p_trichotomy : p = 0 ∨ p = ∞ ∨ (0 < p ∧ p < ∞ ∧ 0 < p.to_real) :=
lemma p_trichotomy : p = 0 ∨ p = ∞ ∨ 0 < p.to_real :=
begin
  sorry
end

lemma p_dichotomy [fact (1 ≤ p)] : p = ∞ ∨ 0 < p.to_real :=
begin
  sorry
end

variables {p}

lemma p_trichotomy₂ (hpq : p ≤ q) :
  (p = 0 ∧ q = 0) ∨ (p = 0 ∧ q = ∞) ∨ (p = 0 ∧ 0 < q.to_real) ∨ (p = ∞ ∧ q = ∞)
  ∨ (0 < p.to_real ∧ q = ∞) ∨ (0 < p.to_real ∧ 0 < q.to_real ∧ p.to_real ≤ q.to_real) :=
begin
  sorry
end

end p_facts

section ℓp

/-!
### ℓp seminorm

We define the ℓp seminorm, denoted by `snorm f p μ`. For real `p`, it is given by an integral
formula (for which we use the notation `snorm' f p μ`), and for `p = ∞` it is the essential
supremum (for which we use the notation `snorm_ess_sup f μ`).

We also define a predicate `mem_ℓp f p μ`, requesting that a function is almost everywhere
measurable and has finite `snorm f p μ`.

This paragraph is devoted to the basic properties of these definitions. It is constructed as
follows: for a given property, we prove it for `snorm'` and `snorm_ess_sup` when it makes sense,
deduce it for `snorm`, and translate it in terms of `mem_ℓp`.
-/

section ℓp_space_definition

/-- The property that `f:α→E` is ae_measurable and `(∫ ∥f a∥^p ∂μ)^(1/p)` is finite if `p < ∞`, or
`ess_sup f < ∞` if `p = ∞`. -/
def mem_ℓp (f : Π i, E i) (p : ℝ≥0∞) : Prop :=
if p = 0 then (f = 0) else
  (if p = ∞ then bdd_above (set.range (λ i, ∥f i∥)) else summable (λ i, ∥f i∥ ^ p.to_real))

end ℓp_space_definition

lemma mem_ℓp_zero {f : Π i, E i} (hf : f = 0) : mem_ℓp f 0 := (if_pos rfl).mpr hf

lemma mem_ℓp_infty {f : Π i, E i} (hf : bdd_above (set.range (λ i, ∥f i∥))) : mem_ℓp f ∞ :=
(if_neg ennreal.top_ne_zero).mpr ((if_pos rfl).mpr hf)

lemma mem_ℓp_gen (hp : 0 < p.to_real) {f : Π i, E i} (hf : summable (λ i, ∥f i∥ ^ p.to_real)) :
  mem_ℓp f p :=
begin
  rw ennreal.to_real_pos_iff at hp,
  dsimp [mem_ℓp],
  rw [if_neg hp.1.ne', if_neg hp.2],
  exact hf,
end

lemma mem_ℓp.eq_zero {f : Π i, E i} (hf : mem_ℓp f 0) : f = 0 := (if_pos rfl).mp hf

lemma mem_ℓp.bdd_above {f : Π i, E i} (hf : mem_ℓp f ∞) : bdd_above (set.range (λ i, ∥f i∥)) :=
(if_pos rfl).mp ((if_neg ennreal.top_ne_zero).mp hf)

lemma mem_ℓp.summable (hp : 0 < p.to_real) {f : Π i, E i} (hf : mem_ℓp f p) :
  summable (λ i, ∥f i∥ ^ p.to_real) :=
begin
  rw ennreal.to_real_pos_iff at hp,
  exact (if_neg hp.2).mp ((if_neg hp.1.ne').mp hf)
end

-- lemma foo (hp : 0 < p.to_real) {f : Π i, E i}
--   (hf : bdd_above (set.range (λ s, ∑ i in s, ∥f i∥ ^ p.to_real))) :
--   summable (λ i, ∥f i∥ ^ p.to_real) :=
-- begin
--   refine (has_sum_of_is_lub_of_nonneg _ _ (is_lub_csupr hf)).summable,
--   intros b,
--   exact real.rpow_nonneg_of_nonneg (norm_nonneg (f b)) p.to_real
-- end

section zero

lemma zero_mem_ℓp : mem_ℓp (0 : Π i, E i) p :=
begin
  rcases p_trichotomy p with rfl | rfl | hp,
  { exact mem_ℓp_zero rfl },
  { apply mem_ℓp_infty,
    cases is_empty_or_nonempty α with _i _i; resetI,
    { convert bdd_above_empty,
      { simp [_i] },
      apply_instance },
    { convert bdd_above_singleton,
      simp } },
  { apply mem_ℓp_gen hp,
    convert summable_zero,
    simp [real.zero_rpow hp.ne'] }
end

lemma zero_mem_ℓp' : mem_ℓp (λ i : α, (0 : E i)) p :=
by convert zero_mem_ℓp

end zero

-- section const

-- lemma mem_ℓp_const [fintype α] (c : G) : mem_ℓp (λ a:α, c) p :=
-- begin
--   sorry
--   -- refine ⟨measurable_const.ae_measurable, _⟩,
--   -- by_cases h0 : p = 0,
--   -- { simp [h0], },
--   -- by_cases hμ : μ = 0,
--   -- { simp [hμ], },
--   -- rw snorm_const c h0 hμ,
--   -- refine ennreal.mul_lt_top ennreal.coe_ne_top _,
--   -- refine (ennreal.rpow_lt_top_of_nonneg _ (measure_ne_top μ set.univ)).ne,
--   -- simp,
-- end

-- lemma mem_ℓp_const_iff {p : ℝ≥0∞} {c : G} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
--   mem_ℓp (λ x : α, c) p ↔ c = 0 ∨ set.finite (set.univ : set α) :=
-- begin
--   sorry
--   -- rw ← snorm_const_lt_top_iff hp_ne_zero hp_ne_top,
--   -- exact ⟨λ h, h.2, λ h, ⟨ae_measurable_const, h⟩⟩,
-- end

-- end const



-- lemma mem_ℓp.of_le {f : Π i, E i} {g : Π i, F i}
--   (hg : mem_ℓp g p) (hfg : ∀ x, ∥f x∥ ≤ ∥g x∥) : mem_ℓp f p :=
-- sorry

-- alias mem_ℓp.of_le ← mem_ℓp.mono

-- lemma mem_ℓp.mono' {f : Π i, E i} {g : α → ℝ} (hg : mem_ℓp g p)
--   (h : ∀ a, ∥f a∥ ≤ g a) : mem_ℓp f p :=
-- -- hg.mono $ h.mono $ λ x hx, le_trans hx (le_abs_self _)
-- sorry

-- lemma mem_ℓp.congr_norm {f : Π i, E i} {g : Π i, F i} (hf : mem_ℓp f p)
--   (h : ∀ a, ∥f a∥ = ∥g a∥) :
--   mem_ℓp g p :=
-- -- hf.mono hg $ eventually_eq.le $ eventually_eq.symm h
-- sorry

-- lemma mem_ℓp_congr_norm {f : Π i, E i} {g : Π i, F i} (h : ∀ a, ∥f a∥ = ∥g a∥) :
--   mem_ℓp f p ↔ mem_ℓp g p :=
-- -- ⟨λ h2f, h2f.congr_norm hg h, λ h2g, h2g.congr_norm hf $ eventually_eq.symm h⟩
-- sorry

-- lemma mem_ℓp_top_of_bound {f : Π i, E i} (C : ℝ)
--   (hfC : ∀ x, ∥f x∥ ≤ C) :
--   mem_ℓp f ∞ :=
-- -- ⟨hf, by { rw snorm_exponent_top, exact snorm_ess_sup_lt_top_of_ae_bound hfC, }⟩
-- sorry

-- lemma mem_ℓp.of_bound [fintype α] {f : Π i, E i}
--   (C : ℝ) (hfC : ∀ x, ∥f x∥ ≤ C) :
--   mem_ℓp f p :=
-- -- (mem_ℓp_const C).of_le (hfC.mono (λ x hx, le_trans hx (le_abs_self _)))
-- sorry

-- section opens_measurable_space
-- -- variable [opens_measurable_space E]

-- lemma mem_ℓp.norm {f : Π i, E i} (h : mem_ℓp f p) : mem_ℓp (λ x, ∥f x∥) p :=
-- -- h.of_le h.ae_measurable.norm (eventually_of_forall (λ x, by simp))
-- sorry

-- lemma mem_ℓp_norm_iff {f : Π i, E i} :
--   mem_ℓp (λ x, ∥f x∥) p ↔ mem_ℓp f p :=
-- -- ⟨λ h, ⟨hf, by { rw ← snorm_norm, exact h.2, }⟩, λ h, h.norm⟩
-- sorry

-- end opens_measurable_space

lemma mem_ℓp.neg {f : Π i, E i} (hf : mem_ℓp f p) : mem_ℓp (-f) p :=
begin
  rcases p_trichotomy p with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    simp [hf.eq_zero] },
  { apply mem_ℓp_infty,
    simpa using hf.bdd_above },
  { apply mem_ℓp_gen hp,
    simpa using hf.summable hp },
end

lemma mem_ℓp_neg_iff {f : Π i, E i} : mem_ℓp (-f) p ↔ mem_ℓp f p :=
⟨λ h, neg_neg f ▸ h.neg, mem_ℓp.neg⟩

lemma mem_ℓp.mem_ℓp_of_exponent_ge {p q : ℝ≥0∞} {f : Π i, E i}
  (hfq : mem_ℓp f q) (hpq : q ≤ p) :
  mem_ℓp f p :=
begin
  rcases p_trichotomy₂ hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hp⟩ | ⟨rfl, rfl⟩ | ⟨hq, rfl⟩ | ⟨hp, hq, hpq'⟩, --rfl | rfl | hp,
  { exact mem_ℓp_zero hfq.eq_zero },
  { rw hfq.eq_zero,
    exact zero_mem_ℓp },
  { rw hfq.eq_zero,
    exact zero_mem_ℓp },
  { exact hfq },
  { apply mem_ℓp_infty,
    have := (hfq.summable hq).tendsto_cofinite_zero,
    sorry },
  { apply mem_ℓp_gen hq,
    -- rw finset.summable_compl_iff,
    have := hfq.summable hp,
    sorry
  }
end



lemma foo {f g : Π i, E i} {A B : ℝ} (hA : A ∈ upper_bounds (set.range (λ i, ∥f i∥)))
  (hB : B ∈ upper_bounds (set.range (λ i, ∥g i∥))) :
  A + B ∈ upper_bounds (set.range (λ i, ∥(f + g) i∥)) :=
begin
  rintros a ⟨i, rfl⟩,
  exact le_trans (norm_add_le _ _) (add_le_add (hA ⟨i, rfl⟩) (hB ⟨i, rfl⟩))
end

lemma mem_ℓp.add {f g : Π i, E i} (hf : mem_ℓp f p) (hg : mem_ℓp g p) : mem_ℓp (f + g) p :=
begin
  rcases p_trichotomy p with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    simp [hf.eq_zero, hg.eq_zero] },
  { apply mem_ℓp_infty,
    obtain ⟨A, hA⟩ := hf.bdd_above,
    obtain ⟨B, hB⟩ := hg.bdd_above,
    refine ⟨A + B, _⟩, -- or use `foo`
    rintros a ⟨i, rfl⟩,
    exact le_trans (norm_add_le _ _) (add_le_add (hA ⟨i, rfl⟩) (hB ⟨i, rfl⟩)) },
  apply mem_ℓp_gen hp,
  let C : ℝ := 2 ^ p.to_real,
  refine summable_of_nonneg_of_le _ _ (((hf.summable hp).add (hg.summable hp)).mul_left C),
  { exact λ b, real.rpow_nonneg_of_nonneg (norm_nonneg (f b + g b)) p.to_real },
  { intros i,
    refine (real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp.le).trans _,
    by_cases hp' : p.to_real < 1,
    { have : 1 ≤ C := sorry,
      --have := ennreal.rpow_add_le_add_rpow,
      sorry },
    { sorry

    }
  }
end

lemma mem_ℓp.sub {f g : Π i, E i} (hf : mem_ℓp f p) (hg : mem_ℓp g p) : mem_ℓp (f - g) p :=
by { rw sub_eq_add_neg, exact hf.add hg.neg }

lemma mem_ℓp_finset_sum {ι} (s : finset ι) {f : ι → Π i, E i} (hf : ∀ i ∈ s, mem_ℓp (f i) p) :
  mem_ℓp (λ a, ∑ i in s, f i a) p :=
begin
  haveI : decidable_eq ι := classical.dec_eq _,
  revert hf,
  refine finset.induction_on s _ _,
  { simp only [zero_mem_ℓp', finset.sum_empty, implies_true_iff], },
  { intros i s his ih hf,
    simp only [his, finset.sum_insert, not_false_iff],
    exact (hf i (s.mem_insert_self i)).add (ih (λ j hj, hf j (finset.mem_insert_of_mem hj))), },
end

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [Π i, normed_space 𝕜 (E i)]

lemma mem_ℓp.const_smul {f : Π i, E i} (hf : mem_ℓp f p) (c : 𝕜) : mem_ℓp (c • f) p :=
begin
  rcases p_trichotomy p with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    simp [hf.eq_zero] },
  { obtain ⟨A, hA⟩ := hf.bdd_above,
    refine mem_ℓp_infty ⟨∥c∥ * A, _⟩,
    rintros a ⟨i, rfl⟩,
    simpa [norm_smul] using mul_le_mul_of_nonneg_left (hA ⟨i, rfl⟩) (norm_nonneg c) },
  { apply mem_ℓp_gen hp,
    convert (hf.summable hp).mul_left (∥c∥ ^ p.to_real),
    ext i,
    simp [norm_smul, real.mul_rpow (norm_nonneg c) (norm_nonneg (f i))] },
end

lemma mem_ℓp.const_mul {f : α → 𝕜} (hf : mem_ℓp f p) (c : 𝕜) : mem_ℓp (λ x, c * f x) p :=
by convert hf.const_smul c

end normed_space

-- section monotonicity

-- lemma mem_ℓp.of_le_mul {f : Π i, E i} {g : Π i, F i} {c : ℝ}
--   (hg : mem_ℓp g p) (hfg : ∀ x, ∥f x∥ ≤ c * ∥g x∥) :
--   mem_ℓp f p :=
-- begin
--   sorry
--   -- simp only [mem_ℓp, hf, true_and],
--   -- apply lt_of_le_of_lt (snorm_le_mul_snorm_of_ae_le_mul hfg p),
--   -- simp [lt_top_iff_ne_top, hg.snorm_ne_top],
-- end

-- end monotonicity

-- section is_R_or_C
-- variables {𝕜 : Type*} [is_R_or_C 𝕜] {f : α → 𝕜}

-- lemma mem_ℓp.re (hf : mem_ℓp f p) : mem_ℓp (λ x, is_R_or_C.re (f x)) p :=
-- begin
--   sorry
--   -- have : ∀ x, ∥is_R_or_C.re (f x)∥ ≤ 1 * ∥f x∥,
--   --   by { intro x, rw one_mul, exact is_R_or_C.norm_re_le_norm (f x), },
--   -- exact hf.of_le_mul hf.1.re (eventually_of_forall this),
-- end

-- lemma mem_ℓp.im (hf : mem_ℓp f p) : mem_ℓp (λ x, is_R_or_C.im (f x)) p :=
-- begin
--   sorry
--   -- have : ∀ x, ∥is_R_or_C.im (f x)∥ ≤ 1 * ∥f x∥,
--   --   by { intro x, rw one_mul, exact is_R_or_C.norm_im_le_norm (f x), },
--   -- exact hf.of_le_mul hf.1.im (eventually_of_forall this),
-- end

-- end is_R_or_C

end ℓp

/-!
### Lp space

The space of equivalence classes of measurable functions for which `snorm f p < ∞`.
-/

/-- Lp space -/
def Lp (E : α → Type*) [Π i, normed_group (E i)]
  (p : ℝ≥0∞) : add_subgroup (Π i, E i) :=
{ carrier := {f | mem_ℓp f p},
  zero_mem' := zero_mem_ℓp,
  add_mem' := λ f g, mem_ℓp.add,
  neg_mem' := λ f, mem_ℓp.neg }

-- localized "notation α ` →₁[`:25 `] ` E := measure_theory.Lp E 1" in measure_theory
-- localized "notation α ` →₂[`:25 `] ` E := measure_theory.Lp E 2" in measure_theory

namespace Lp

instance : has_coe_to_fun (Lp E p) (λ _, Π i, E i) := ⟨λ f, ((f : Π i, E i) : Π i, E i)⟩

@[ext] lemma ext {f g : Lp E p} (h : (f : Π i, E i) = g) : f = g :=
subtype.ext h

lemma ext_iff {f g : Lp E p} : f = g ↔ (f : Π i, E i) = g :=
subtype.ext_iff

protected lemma monotone {p q : ℝ≥0∞} (hpq : q ≤ p) : Lp E q ≤ Lp E p :=
λ f hf, mem_ℓp.mem_ℓp_of_exponent_ge hf hpq

protected lemma mem_ℓp (f : Lp E p) : mem_ℓp f p := f.prop

variables (E p)
@[simp] lemma coe_fn_zero : ⇑(0 : Lp E p) = 0 := rfl
variables {E p}

@[simp] lemma coe_fn_neg (f : Lp E p) : ⇑(-f) = -f := rfl

@[simp] lemma coe_fn_add (f g : Lp E p) : ⇑(f + g) = f + g := rfl

@[simp] lemma coe_fn_sub (f g : Lp E p) : ⇑(f - g) = f - g := rfl

@[simp] lemma eq_zero (f : Lp E 0) : f = 0 := ext (Lp.mem_ℓp f).eq_zero

instance : has_norm (Lp E p) :=
{ norm := λ f, if p = 0 then 0 else
    (if p = ∞ then ⨆ i, ∥f i∥ else (∑' i, ∥f i∥ ^ p.to_real) ^ (1/p.to_real)) }

lemma norm_eq_zero (f : Lp E 0) : ∥f∥ = 0 := if_pos rfl

lemma norm_eq_supr (f : Lp E ∞) : ∥f∥ = ⨆ i, ∥f i∥ :=
begin
  dsimp [norm],
  rw [if_neg ennreal.top_ne_zero, if_pos rfl]
end

lemma is_lub_norm [nonempty α] (f : Lp E ∞) : is_lub (set.range (λ i, ∥f i∥)) ∥f∥ :=
begin
  rw Lp.norm_eq_supr,
  exact is_lub_csupr (Lp.mem_ℓp f)
end

lemma norm_eq_tsum_rpow (hp : 0 < p.to_real) (f : Lp E p) :
  ∥f∥ = (∑' i, ∥f i∥ ^ p.to_real) ^ (1/p.to_real) :=
begin
  dsimp [norm],
  rw ennreal.to_real_pos_iff at hp,
  rw [if_neg hp.1.ne', if_neg hp.2],
end

lemma norm_rpow_eq_tsum (hp : 0 < p.to_real) (f : Lp E p) :
  ∥f∥ ^ p.to_real = ∑' i, ∥f i∥ ^ p.to_real :=
begin
  rw [norm_eq_tsum_rpow hp, ← real.rpow_mul],
  { field_simp [hp.ne'] },
  apply tsum_nonneg,
  intros i,
  calc (0:ℝ) = 0 ^ p.to_real : by rw real.zero_rpow hp.ne'
  ... ≤ _ : real.rpow_le_rpow rfl.le (norm_nonneg (f i)) hp.le
end

lemma has_sum_norm (hp : 0 < p.to_real) (f : Lp E p) :
  has_sum (λ i, ∥f i∥ ^ p.to_real) (∥f∥ ^ p.to_real) :=
begin
  rw norm_rpow_eq_tsum hp,
  exact ((Lp.mem_ℓp f).summable hp).has_sum
end

-- move this
lemma real.supr_empty {α : Type*} [is_empty α] (f : α → ℝ) : (⨆ i, f i) = 0 :=
begin
  dsimp [supr],
  convert real.Sup_empty,
  rw set.range_eq_empty_iff,
  apply_instance
end

@[simp] lemma norm_zero : ∥(0 : Lp E p)∥ = 0 :=
begin
  rcases p_trichotomy p with rfl | rfl | hp,
  { exact Lp.norm_eq_zero 0 },
  { rw Lp.norm_eq_supr,
    cases is_empty_or_nonempty α; resetI,
    { exact real.supr_empty _ },
    { simp } },
  { rw Lp.norm_eq_tsum_rpow hp,
    have hp' : 1 / p.to_real ≠ 0 := one_div_ne_zero hp.ne',
    simpa [real.zero_rpow hp.ne'] using real.zero_rpow hp' }
end

lemma norm_eq_zero_iff {f : Lp E p} (hp : 0 < p) : ∥f∥ = 0 ↔ f = 0 :=
begin
  refine ⟨λ h, _, by { rintros rfl, exact norm_zero }⟩,
  rcases p_trichotomy p with rfl | rfl | hp, --⟨hp', h⟩ | ⟨hp', h | ⟨_i, h⟩⟩ | ⟨hp', hp', h⟩,
  { exact Lp.eq_zero f },
  { cases is_empty_or_nonempty α with _i _i; resetI,
    { ext i,
      apply is_empty.elim _i i },
    have H : is_lub (set.range (λ i, ∥f i∥)) 0,
    { simpa [h] using Lp.is_lub_norm f },
    ext i,
    have : ∥f i∥ = 0 := le_antisymm (H.1 ⟨i, rfl⟩) (norm_nonneg _),
    simpa using this },
  { sorry }
  -- have := (Lp.has_sum_norm)

  -- refine ⟨_, _norm_zero⟩,
  -- refine ⟨λ hf, _, λ hf, by simp [hf]⟩,
  -- rw [norm_def, ennreal.to_real_eq_zero_iff] at hf,
  -- cases hf,
  -- { rw snorm_eq_zero_iff (Lp.ae_measurable f) hp.ne.symm at hf,
  --   exact subtype.eq (ae_eq_fun.ext (hf.trans ae_eq_fun.coe_fn_zero.symm)), },
  -- { exact absurd hf (snorm_ne_top f), },
end

lemma eq_zero_iff_ae_eq_zero {f : Lp E p} : f = 0 ↔ ⇑f = 0 :=
by rw [ext_iff, coe_fn_zero]

@[simp] lemma norm_neg {f : Lp E p} : ∥-f∥ = ∥f∥ :=
begin
  rcases p_trichotomy p with rfl | rfl | hp,
  { simp [Lp.norm_eq_zero] },
  { rw (Lp.is).unique,
    convert h₂,
    ext i,
    simp },
  { rw h₁.unique,
    convert h₂,
    ext i,
    simp }
end
-- by rw [norm_def, norm_def, snorm_congr_ae (coe_fn_neg _), snorm_neg]
-- sorry

-- lemma norm_le_mul_norm_of_ae_le_mul
--   -- [Π i, second_countable_topology (F i)]
--   {c : ℝ} {f : Lp E p} {g : Lp F p} (h : ∀ x, ∥f x∥ ≤ c * ∥g x∥) : ∥f∥ ≤ c * ∥g∥ :=
-- begin
--   -- by_cases pzero : p = 0,
--   -- { simp [pzero, norm_def] },
--   -- cases le_or_lt 0 c with hc hc,
--   -- { have := snorm_le_mul_snorm_aux_of_nonneg h hc p,
--   --   rw [← ennreal.to_real_le_to_real, ennreal.to_real_mul, ennreal.to_real_of_real hc] at this,
--   --   { exact this },
--   --   { exact (Lp.mem_ℓp _).snorm_ne_top },
--   --   { simp [(Lp.mem_ℓp _).snorm_ne_top] } },
--   -- { have := snorm_le_mul_snorm_aux_of_neg h hc p,
--   --   simp only [snorm_eq_zero_iff (Lp.ae_measurable _) pzero, ← eq_zero_iff_ae_eq_zero] at this,
--   --   simp [this] }
-- end

-- lemma norm_le_norm_of_ae_le --[Π i, second_countable_topology (F i)]
--   {f : Lp E p} {g : Lp F p} (h : ∀ x, ∥f x∥ ≤ ∥g x∥) : ∥f∥ ≤ ∥g∥ :=
-- begin
--   -- rw [norm_def, norm_def, ennreal.to_real_le_to_real (snorm_ne_top _) (snorm_ne_top _)],
--   -- exact snorm_mono_ae h
-- end

-- lemma mem_Lp_of_ae_le_mul --[Π i, second_countable_topology (F i)]
--   {c : ℝ} {f : Π i, E i} {g : Lp F p} (h : ∀ x, ∥f x∥ ≤ c * ∥g x∥) : f ∈ Lp E p :=
-- -- mem_Lp_iff_mem_ℓp.2 $ mem_ℓp.of_le_mul (Lp.mem_ℓp g) f.ae_measurable h
-- sorry

-- lemma mem_Lp_of_ae_le --[second_countable_topology F] [measurable_space F] [borel_space F]
--   {f : Π i, E i} {g : Lp F p} (h : ∀ x, ∥f x∥ ≤ ∥g x∥) : f ∈ Lp E p :=
-- -- mem_Lp_iff_mem_ℓp.2 $ mem_ℓp.of_le (Lp.mem_ℓp g) f.ae_measurable h
-- sorry

-- lemma mem_Lp_of_ae_bound [is_finite_measure] {f : α →ₘ[μ] E} (C : ℝ) (hfC : ∀ᵐ x ∂μ, ∥f x∥ ≤ C) :
--   f ∈ Lp E p :=
-- mem_Lp_iff_mem_ℓp.2 $ mem_ℓp.of_bound f.ae_measurable _ hfC

-- lemma norm_le_of_ae_bound [is_finite_measure] {f : Lp E p} {C : ℝ} (hC : 0 ≤ C)
--   (hfC : ∀ᵐ x ∂μ, ∥f x∥ ≤ C) :
--   ∥f∥ ≤ (measure_univ_nnreal) ^ (p.to_real)⁻¹ * C :=
-- begin
--   by_cases hμ : = 0,
--   { by_cases hp : p.to_real⁻¹ = 0,
--     { simpa [hp, hμ, norm_def] using hC },
--     { simp [hμ, norm_def, real.zero_rpow hp] } },
--   let A : ℝ≥0 := (measure_univ_nnreal) ^ (p.to_real)⁻¹ * ⟨C, hC⟩,
--   suffices : snorm f p ≤ A,
--   { exact ennreal.to_real_le_coe_of_le_coe this },
--   convert snorm_le_of_ae_bound hfC,
--   rw [← coe_measure_univ_nnreal, ennreal.coe_rpow_of_ne_zero (measure_univ_nnreal_pos hμ).ne',
--     ennreal.coe_mul],
--   congr,
--   rw max_eq_left hC
-- end

instance [hp : fact (1 ≤ p)] : normed_group (Lp E p) :=
normed_group.of_core _
{ norm_eq_zero_iff := λ f, norm_eq_zero_iff (ennreal.zero_lt_one.trans_le hp.1),
  triangle := λ f g, begin
    tactic.unfreeze_local_instances,
    rcases p_dichotomy p with rfl | hp',
    { cases is_empty_or_nonempty α; resetI,
      { sorry },
      have := Lp.is_lub_norm f,
      have := Lp.is_lub_norm g,
      have := Lp.is_lub_norm (f + g),

       },
    -- rcases Lp_trichotomy₃ f g (f + g) with ⟨hp, h₁, h₂, h₃⟩ | ⟨hp, h | ⟨_i, h₁, h₂, h₃⟩⟩ | ⟨hp, hp', h₁, h₂, h₃⟩,
    { simp [h₁, h₂, h₃] },
    { sorry },
    { sorry },
    { sorry }
    -- have := Lp_trichotomy₃ f g (f + g),
    -- rw ← ennreal.to_real_add (snorm_ne_top f) (snorm_ne_top g),
    -- suffices h_snorm : snorm ⇑(f + g) p ≤ snorm ⇑f p + snorm ⇑g p,
    -- { rwa ennreal.to_real_le_to_real (snorm_ne_top (f + g)),
    --   exact ennreal.add_ne_top.mpr ⟨snorm_ne_top f, snorm_ne_top g⟩, },
    -- rw [snorm_congr_ae (coe_fn_add _ _)],
    -- exact snorm_add_le (Lp.ae_measurable f) (Lp.ae_measurable g) hp.1,
  end,
  norm_neg := by simp }

instance normed_group_L1 : normed_group (Lp E 1) := by apply_instance
instance normed_group_L2 : normed_group (Lp E 2) := by apply_instance
instance normed_group_Ltop : normed_group (Lp E ∞) := by apply_instance

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [Π i, normed_space 𝕜 (E i)]

lemma mem_Lp_const_smul (c : 𝕜) (f : Lp E p) : c • ↑f ∈ Lp E p := (Lp.mem_ℓp f).const_smul c

variables (E p 𝕜)

/-- The `𝕜`-submodule of elements of `α →ₘ[μ] E` whose `Lp` norm is finite.  This is `Lp E p`,
with extra structure. -/
def Lp_submodule : submodule 𝕜 (Π i, E i) :=
{ smul_mem' := λ c f hf, by simpa using mem_Lp_const_smul c ⟨f, hf⟩,
  .. Lp E p }

variables {E p 𝕜}

lemma coe_Lp_submodule : (Lp_submodule E p 𝕜).to_add_subgroup = Lp E p := rfl

instance : module 𝕜 (Lp E p) :=
{ .. (Lp_submodule E p 𝕜).module }

lemma coe_fn_smul (c : 𝕜) (f : Lp E p) : ⇑(c • f) = c • f := rfl

lemma norm_const_smul (c : 𝕜) (f : Lp E p) : ∥c • f∥ = ∥c∥ * ∥f∥ :=
by rw [norm_def, snorm_congr_ae (coe_fn_smul _ _), snorm_const_smul c,
  ennreal.to_real_mul, ennreal.coe_to_real, coe_nnnorm, norm_def]

instance [fact (1 ≤ p)] : normed_space 𝕜 (Lp E p) :=
{ norm_smul_le := λ _ _, by simp [norm_const_smul] }

instance normed_space_L1 : normed_space 𝕜 (Lp E 1) := by apply_instance
instance normed_space_L2 : normed_space 𝕜 (Lp E 2) := by apply_instance
instance normed_space_Ltop : normed_space 𝕜 (Lp E ∞) := by apply_instance

instance [Π i, normed_space ℝ (E i)] [has_scalar ℝ 𝕜] [Π i, is_scalar_tower ℝ 𝕜 (E i)] :
  is_scalar_tower ℝ 𝕜 (Lp E p) :=
begin
  refine ⟨λ r c f, _⟩,
  ext1,
  refine (Lp.coe_fn_smul _ _).trans _,
  rw smul_assoc,
  refine eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm,
  refine (Lp.coe_fn_smul c f).mono (λ x hx, _),
  rw [pi.smul_apply, pi.smul_apply, pi.smul_apply, hx, pi.smul_apply],
end

end normed_space

end Lp



/-!
## `L^p` is a complete space

We show that `L^p` is a complete space for `1 ≤ p`.
-/

section complete_space

-- variables [Π i, second_countable_topology (E i)]

namespace measure_theory
namespace Lp

/-! ### Prove that controlled Cauchy sequences of `ℓp` have limits in `ℓp` -/

private lemma lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum {f : ℕ → Π i, E i}
  {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
  (h : ∀ n, ∑' a, (∑ i in finset.range (n + 1), nnnorm (f (i + 1) a - f i a) : ℝ≥0∞)^p
    ≤ (∑' i, B i) ^ p) :
  (∑' a, (∑' i, nnnorm (f (i + 1) a - f i a) : ℝ≥0∞)^p) ^ (1/p) ≤ ∑' i, B i :=
begin
  -- have hp_pos : 0 < p := zero_lt_one.trans_le hp1,
  -- suffices h_pow : ∫⁻ a, (∑' i, nnnorm (f (i + 1) a - f i a) : ℝ≥0∞)^p ∂μ ≤ (∑' i, B i) ^ p,
  --   by rwa [←ennreal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div],
  -- have h_tsum_1 : ∀ g : ℕ → ℝ≥0∞,
  --     ∑' i, g i = at_top.liminf (λ n, ∑ i in finset.range (n + 1), g i),
  --   by { intro g, rw [ennreal.tsum_eq_liminf_sum_nat, ← liminf_nat_add _ 1], },
  -- simp_rw h_tsum_1 _,
  -- rw ← h_tsum_1,
  -- have h_liminf_pow : ∫⁻ a, at_top.liminf (λ n, ∑ i in finset.range (n + 1),
  --     (nnnorm (f (i + 1) a - f i a)))^p ∂μ
  --   = ∫⁻ a, at_top.liminf (λ n, (∑ i in finset.range (n + 1), (nnnorm (f (i + 1) a - f i a)))^p) ∂μ,
  -- { refine lintegral_congr (λ x, _),
  --   have h_rpow_mono := ennreal.rpow_left_strict_mono_of_pos (zero_lt_one.trans_le hp1),
  --   have h_rpow_surj := (ennreal.rpow_left_bijective hp_pos.ne.symm).2,
  --   refine (h_rpow_mono.order_iso_of_surjective _ h_rpow_surj).liminf_apply _ _ _ _,
  --   all_goals { is_bounded_default }, },
  -- rw h_liminf_pow,
  -- refine (lintegral_liminf_le' _).trans _,
  -- { exact λ n, (finset.ae_measurable_sum (finset.range (n+1))
  --     (λ i _, ((hf (i+1)).sub (hf i)).ennnorm)).pow_const _, },
  -- { exact liminf_le_of_frequently_le' (frequently_of_forall h), },
end

private lemma tsum_nnnorm_sub_ae_lt_top
  {f : ℕ → Π i, E i} {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
  (hB : ∑' i, B i ≠ ∞)
  (h : (∑' a, (∑' i, nnnorm (f (i + 1) a - f i a) : ℝ≥0∞)^p) ^ (1/p) ≤ ∑' i, B i) :
  ∀ x, (∑' i, nnnorm (f (i + 1) x - f i x) : ℝ≥0∞) < ∞ :=
begin
  -- have hp_pos : 0 < p := zero_lt_one.trans_le hp1,
  -- have h_integral : ∫⁻ a, (∑' i, ∥f (i + 1) a - f i a∥₊ : ℝ≥0∞)^p ∂μ < ∞,
  -- { have h_tsum_lt_top : (∑' i, B i) ^ p < ∞,
  --     from ennreal.rpow_lt_top_of_nonneg hp_pos.le hB,
  --   refine lt_of_le_of_lt _ h_tsum_lt_top,
  --   rwa [←ennreal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div] at h, },
  -- have rpow_ae_lt_top : ∀ᵐ x ∂μ, (∑' i, nnnorm (f (i + 1) x - f i x) : ℝ≥0∞)^p < ∞,
  -- { refine ae_lt_top' (ae_measurable.pow_const _ _) h_integral.ne,
  --   exact ae_measurable.ennreal_tsum (λ n, ((hf (n+1)).sub (hf n)).ennnorm), },
  -- refine rpow_ae_lt_top.mono (λ x hx, _),
  -- rwa [←ennreal.lt_rpow_one_div_iff hp_pos,
  --   ennreal.top_rpow_of_pos (by simp [hp_pos] : 0 < 1 / p)] at hx,
end

-- lemma ae_tendsto_of_cauchy_snorm' [complete_space E] {f : ℕ → Π i, E i} {p : ℝ}
--   (hf : ∀ n, ae_measurable (f n) μ) (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
--   (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) :
--   ∀ᵐ x ∂μ, ∃ l : E, at_top.tendsto (λ n, f n x) (𝓝 l) :=
-- begin
--   have h_summable : ∀ᵐ x ∂μ, summable (λ (i : ℕ), f (i + 1) x - f i x),
--   { have h1 : ∀ n, snorm' (λ x, ∑ i in finset.range (n + 1), norm (f (i + 1) x - f i x)) p μ
--         ≤ ∑' i, B i,
--       from snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' hf hp1 h_cau,
--     have h2 : ∀ n, ∫⁻ a, (∑ i in finset.range (n + 1), nnnorm (f (i + 1) a - f i a) : ℝ≥0∞)^p ∂μ
--         ≤ (∑' i, B i) ^ p,
--       from λ n, lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum hf hp1 n (h1 n),
--     have h3 : (∫⁻ a, (∑' i, nnnorm (f (i + 1) a - f i a) : ℝ≥0∞)^p ∂μ) ^ (1/p) ≤ ∑' i, B i,
--       from lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum hf hp1 h2,
--     have h4 : ∀ᵐ x ∂μ, (∑' i, nnnorm (f (i + 1) x - f i x) : ℝ≥0∞) < ∞,
--       from tsum_nnnorm_sub_ae_lt_top hf hp1 hB h3,
--     exact h4.mono (λ x hx, summable_of_summable_nnnorm
--       (ennreal.tsum_coe_ne_top_iff_summable.mp (lt_top_iff_ne_top.mp hx))), },
--   have h : ∀ᵐ x ∂μ, ∃ l : E,
--     at_top.tendsto (λ n, ∑ i in finset.range n, (f (i + 1) x - f i x)) (𝓝 l),
--   { refine h_summable.mono (λ x hx, _),
--     let hx_sum := hx.has_sum.tendsto_sum_nat,
--     exact ⟨∑' i, (f (i + 1) x - f i x), hx_sum⟩, },
--   refine h.mono (λ x hx, _),
--   cases hx with l hx,
--   have h_rw_sum : (λ n, ∑ i in finset.range n, (f (i + 1) x - f i x)) = λ n, f n x - f 0 x,
--   { ext1 n,
--     change ∑ (i : ℕ) in finset.range n, ((λ m, f m x) (i + 1) - (λ m, f m x) i) = f n x - f 0 x,
--     rw finset.sum_range_sub, },
--   rw h_rw_sum at hx,
--   have hf_rw : (λ n, f n x) = λ n, f n x - f 0 x + f 0 x, by { ext1 n, abel, },
--   rw hf_rw,
--   exact ⟨l + f 0 x, tendsto.add_const _ hx⟩,
-- end

-- lemma ae_tendsto_of_cauchy_snorm [complete_space E] {f : ℕ → Π i, E i}
--   (hf : ∀ n, ae_measurable (f n) μ) (hp : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
--   (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
--   ∀ᵐ x ∂μ, ∃ l : E, at_top.tendsto (λ n, f n x) (𝓝 l) :=
-- begin
--   by_cases hp_top : p = ∞,
--   { simp_rw [hp_top] at *,
--     have h_cau_ae : ∀ᵐ x ∂μ, ∀ N n m, N ≤ n → N ≤ m → (nnnorm ((f n - f m) x) : ℝ≥0∞) < B N,
--     { simp_rw [ae_all_iff, ae_imp_iff],
--       exact λ N n m hnN hmN, ae_lt_of_ess_sup_lt (h_cau N n m hnN hmN), },
--     simp_rw [snorm_exponent_top, snorm_ess_sup] at h_cau,
--     refine h_cau_ae.mono (λ x hx, cauchy_seq_tendsto_of_complete _),
--     refine cauchy_seq_of_le_tendsto_0 (λ n, (B n).to_real) _ _,
--     { intros n m N hnN hmN,
--       specialize hx N n m hnN hmN,
--       rw [dist_eq_norm, ←ennreal.to_real_of_real (norm_nonneg _),
--         ennreal.to_real_le_to_real ennreal.of_real_ne_top
--         (ennreal.ne_top_of_tsum_ne_top hB N)],
--       rw ←of_real_norm_eq_coe_nnnorm at hx,
--       exact hx.le, },
--     { rw ← ennreal.zero_to_real,
--       exact tendsto.comp (ennreal.tendsto_to_real ennreal.zero_ne_top)
--         (ennreal.tendsto_at_top_zero_of_tsum_ne_top hB), }, },
--   have hp1 : 1 ≤ p.to_real,
--   { rw [← ennreal.of_real_le_iff_le_to_real hp_top, ennreal.of_real_one],
--     exact hp, },
--   have h_cau' : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) (p.to_real) μ < B N,
--   { intros N n m hn hm,
--     specialize h_cau N n m hn hm,
--     rwa snorm_eq_snorm' (ennreal.zero_lt_one.trans_le hp).ne.symm hp_top at h_cau, },
--   exact ae_tendsto_of_cauchy_snorm' hf hp1 hB h_cau',
-- end

-- lemma cauchy_tendsto_of_tendsto {f : ℕ → Π i, E i} (hf : ∀ n, ae_measurable (f n) μ)
--   (f_lim : Π i, E i) {B : ℕ → ℝ≥0∞}
--   (hB : ∑' i, B i ≠ ∞) (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N)
--   (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
--   at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
-- begin
--   rw ennreal.tendsto_at_top_zero,
--   intros ε hε,
--   have h_B : ∃ (N : ℕ), B N ≤ ε,
--   { suffices h_tendsto_zero : ∃ (N : ℕ), ∀ n : ℕ, N ≤ n → B n ≤ ε,
--       from ⟨h_tendsto_zero.some, h_tendsto_zero.some_spec _ (le_refl _)⟩,
--     exact (ennreal.tendsto_at_top_zero.mp (ennreal.tendsto_at_top_zero_of_tsum_ne_top hB))
--       ε hε, },
--   cases h_B with N h_B,
--   refine ⟨N, λ n hn, _⟩,
--   have h_sub : snorm (f n - f_lim) p μ ≤ at_top.liminf (λ m, snorm (f n - f m) p μ),
--   { refine snorm_lim_le_liminf_snorm (λ m, (hf n).sub (hf m)) (f n - f_lim) _,
--     refine h_lim.mono (λ x hx, _),
--     simp_rw sub_eq_add_neg,
--     exact tendsto.add tendsto_const_nhds (tendsto.neg hx), },
--   refine h_sub.trans _,
--   refine liminf_le_of_frequently_le' (frequently_at_top.mpr _),
--   refine λ N1, ⟨max N N1, le_max_right _ _, _⟩,
--   exact (h_cau N n (max N N1) hn (le_max_left _ _)).le.trans h_B,
-- end

-- lemma mem_ℓp_of_cauchy_tendsto (hp : 1 ≤ p) {f : ℕ → Π i, E i} (hf : ∀ n, mem_ℓp (f n) p μ)
--   (f_lim : Π i, E i) (h_lim_meas : ae_measurable f_lim μ)
--   (h_tendsto : at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0)) :
--   mem_ℓp f_lim p μ :=
-- begin
--   refine ⟨h_lim_meas, _⟩,
--   rw ennreal.tendsto_at_top_zero at h_tendsto,
--   cases (h_tendsto 1 ennreal.zero_lt_one) with N h_tendsto_1,
--   specialize h_tendsto_1 N (le_refl N),
--   have h_add : f_lim = f_lim - f N + f N, by abel,
--   rw h_add,
--   refine lt_of_le_of_lt (snorm_add_le (h_lim_meas.sub (hf N).1) (hf N).1 hp) _,
--   rw ennreal.add_lt_top,
--   split,
--   { refine lt_of_le_of_lt _ ennreal.one_lt_top,
--     have h_neg : f_lim - f N = -(f N - f_lim), by simp,
--     rwa [h_neg, snorm_neg], },
--   { exact (hf N).2, },
-- end

-- lemma cauchy_complete_ℓp [complete_space E] (hp : 1 ≤ p)
--   {f : ℕ → Π i, E i} (hf : ∀ n, mem_ℓp (f n) p μ) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
--   (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
--   ∃ (f_lim : Π i, E i) (hf_lim_meas : mem_ℓp f_lim p μ),
--     at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
-- begin
--   obtain ⟨f_lim, h_f_lim_meas, h_lim⟩ : ∃ (f_lim : Π i, E i) (hf_lim_meas : measurable f_lim),
--       ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (nhds (f_lim x)),
--     from measurable_limit_of_tendsto_metric_ae (λ n, (hf n).1)
--       (ae_tendsto_of_cauchy_snorm (λ n, (hf n).1) hp hB h_cau),
--   have h_tendsto' : at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0),
--     from cauchy_tendsto_of_tendsto (λ m, (hf m).1) f_lim hB h_cau h_lim,
--   have h_ℓp_lim : mem_ℓp f_lim p μ,
--     from mem_ℓp_of_cauchy_tendsto hp hf f_lim h_f_lim_meas.ae_measurable h_tendsto',
--   exact ⟨f_lim, h_ℓp_lim, h_tendsto'⟩,
-- end

/-! ### `Lp` is complete for `1 ≤ p` -/

instance [Π i, complete_space (E i)] [hp : fact (1 ≤ p)] : complete_space (Lp E p) :=
sorry
-- complete_space_Lp_of_cauchy_complete_ℓp $
--   λ f hf B hB h_cau, cauchy_complete_ℓp hp.elim hf hB.ne h_cau

end Lp
end measure_theory

end complete_space
