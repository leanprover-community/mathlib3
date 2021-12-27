/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.mean_inequalities
import analysis.mean_inequalities_pow
import topology.algebra.ordered.liminf_limsup

/-!
# ℓp space

This file describes properties of elements `f` of a pi-type `Π i, E i` with finite "norm",
defined for `p:ℝ≥0∞` as the size of the support of `f` if `p=0`, `(∑' a, ∥f a∥^p) ^ (1/p)` for
`0 < p < ∞` and `⨆ a, ∥f a∥` for `p=∞`.

The Prop-valued `mem_ℓp f p` states that a function `f : Π i, E i` has finite norm according
to the above definition; that is, `f` has finite support if `p = 0`, `summable (λ a, ∥f a∥^p)` if
`0 < p < ∞`, and `bdd_above (norm '' (set.range f))` if `p = ∞`.

The space `lp E p` is the subtype of elements of `Π i : α, E i` which satisfy `mem_ℓp f p`. For
`1 ≤ p`, the "norm" is genuinely a norm and (TODO) `lp` is a complete metric space.

## Main definitions

* `mem_ℓp f p` : property that the function `f` satisfies, as appropriate, `f` finitely supported
  if `p = 0`, `summable (λ a, ∥f a∥^p)` if `0 < p < ∞`, and `bdd_above (norm '' (set.range f))` if
  `p = ∞`
* `lp E p` : elements of `Π i : α, E i` such that `mem_ℓp f p`. Defined as an `add_subgroup` of
  `Π i : α, E i`.

## Implementation

Since `lp` is defined as an `add_subgroup`, dot notation does not work. Use `lp.norm_neg f` to
say that `∥-f∥ = ∥f∥`, instead of the non-working `f.norm_neg`.

## TODO

* Hölder's inequality
* Completeness of `lp`
* Equivalence with `pi_Lp`, for `α` finite
* Equivalence with `measure_theory.Lp`, for `f : α → E` (i.e., functions rather than pi-types) and
  the counting measure on `α`
* Equivalence with `bounded_continuous_function`, for `f : α → E` (i.e., functions rather than
  pi-types) and `p = ∞`, and the discrete topology on `α`

-/

noncomputable theory
open_locale nnreal ennreal big_operators

variables {α : Type*} {E : α → Type*} {p q : ℝ≥0∞} [Π i, normed_group (E i)]

/-!
### `mem_ℓp` predicate

-/

/-- The property that `f : Π i : α, E i`
* is finitely supported, if `p = 0`, or
* admits an upper bound for `set.range (λ i, ∥f i∥)`, if `p = ∞`, or
* has the series `∑' i, ∥f i∥ ^ p` be summable, if `0 < p < ∞`. -/
def mem_ℓp (f : Π i, E i) (p : ℝ≥0∞) : Prop :=
if p = 0 then (set.finite {i | f i ≠ 0}) else
  (if p = ∞ then bdd_above (set.range (λ i, ∥f i∥)) else summable (λ i, ∥f i∥ ^ p.to_real))

lemma mem_ℓp_zero {f : Π i, E i} (hf : set.finite {i | f i ≠ 0}) : mem_ℓp f 0 :=
(if_pos rfl).mpr hf

lemma mem_ℓp_infty {f : Π i, E i} (hf : bdd_above (set.range (λ i, ∥f i∥))) : mem_ℓp f ∞ :=
(if_neg ennreal.top_ne_zero).mpr ((if_pos rfl).mpr hf)

lemma mem_ℓp_gen (hp : 0 < p.to_real) {f : Π i, E i} (hf : summable (λ i, ∥f i∥ ^ p.to_real)) :
  mem_ℓp f p :=
begin
  rw ennreal.to_real_pos_iff at hp,
  dsimp [mem_ℓp],
  rw [if_neg hp.1.ne', if_neg hp.2.ne],
  exact hf,
end

lemma zero_mem_ℓp : mem_ℓp (0 : Π i, E i) p :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    simp },
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

lemma zero_mem_ℓp' : mem_ℓp (λ i : α, (0 : E i)) p := zero_mem_ℓp

namespace mem_ℓp

lemma finite_dsupport {f : Π i, E i} (hf : mem_ℓp f 0) : set.finite {i | f i ≠ 0} :=
(if_pos rfl).mp hf

lemma bdd_above {f : Π i, E i} (hf : mem_ℓp f ∞) : bdd_above (set.range (λ i, ∥f i∥)) :=
(if_pos rfl).mp ((if_neg ennreal.top_ne_zero).mp hf)

lemma summable (hp : 0 < p.to_real) {f : Π i, E i} (hf : mem_ℓp f p) :
  summable (λ i, ∥f i∥ ^ p.to_real) :=
begin
  rw ennreal.to_real_pos_iff at hp,
  exact (if_neg hp.2.ne).mp ((if_neg hp.1.ne').mp hf)
end

lemma neg {f : Π i, E i} (hf : mem_ℓp f p) : mem_ℓp (-f) p :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    simp [hf.finite_dsupport] },
  { apply mem_ℓp_infty,
    simpa using hf.bdd_above },
  { apply mem_ℓp_gen hp,
    simpa using hf.summable hp },
end

lemma neg_iff {f : Π i, E i} : mem_ℓp (-f) p ↔ mem_ℓp f p :=
⟨λ h, neg_neg f ▸ h.neg, mem_ℓp.neg⟩

lemma of_exponent_ge {p q : ℝ≥0∞} {f : Π i, E i}
  (hfq : mem_ℓp f q) (hpq : q ≤ p) :
  mem_ℓp f p :=
begin
  rcases ennreal.trichotomy₂ hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hp⟩ | ⟨rfl, rfl⟩ | ⟨hq, rfl⟩
    | ⟨hq, hp, hpq'⟩,
  { apply mem_ℓp_zero,
    exact hfq.finite_dsupport },
  { apply mem_ℓp_infty,
    obtain ⟨C, hC⟩ := hfq.finite_dsupport.bdd_above_image (λ i, ∥f i∥),
    use max 0 C,
    rintros x ⟨i, rfl⟩,
    by_cases hi : f i = 0,
    { simp [hi] },
    { exact (hC ⟨i, hi, rfl⟩).trans (le_max_right _ _) } },
  { apply mem_ℓp_gen hp,
    have : ∀ i ∉ hfq.finite_dsupport.to_finset, ∥f i∥ ^ p.to_real = 0,
    { intros i hi,
      have : f i = 0 := by simpa using hi,
      simp [this, real.zero_rpow hp.ne'] },
    exact summable_of_ne_finset_zero this },
  { exact hfq },
  { apply mem_ℓp_infty,
    obtain ⟨A, hA⟩ := (hfq.summable hq).tendsto_cofinite_zero.bdd_above_range_of_cofinite,
    use A ^ (q.to_real⁻¹),
    rintros x ⟨i, rfl⟩,
    have : 0 ≤ ∥f i∥ ^ q.to_real := real.rpow_nonneg_of_nonneg (norm_nonneg _) _,
    simpa [← real.rpow_mul, mul_inv_cancel hq.ne'] using
      real.rpow_le_rpow this (hA ⟨i, rfl⟩) (inv_nonneg.mpr hq.le) },
  { apply mem_ℓp_gen hp,
    have hf' := hfq.summable hq,
    refine summable_of_norm_bounded_eventually _ hf' (@set.finite.subset _ {i | 1 ≤ ∥f i∥} _ _ _),
    { have H : {x : α | 1 ≤ ∥f x∥ ^ q.to_real}.finite,
      { simpa using eventually_lt_of_tendsto_lt (by norm_num : (0:ℝ) < 1)
          hf'.tendsto_cofinite_zero },
      exact H.subset (λ i hi, real.one_le_rpow hi hq.le) },
    { show ∀ i, ¬ (|∥f i∥ ^ p.to_real| ≤ ∥f i∥ ^ q.to_real) → 1 ≤ ∥f i∥,
      intros i hi,
      have : 0 ≤ ∥f i∥ ^ p.to_real := real.rpow_nonneg_of_nonneg (norm_nonneg _) p.to_real,
      simp only [abs_of_nonneg, this] at hi,
      contrapose! hi,
      exact real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hi.le hq.le hpq' } }
end

lemma add {f g : Π i, E i} (hf : mem_ℓp f p) (hg : mem_ℓp g p) : mem_ℓp (f + g) p :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    refine (hf.finite_dsupport.union hg.finite_dsupport).subset _,
    intros i,
    simp only [pi.add_apply, ne.def, set.mem_union_eq, set.mem_set_of_eq],
    contrapose!,
    rintros ⟨hf', hg'⟩,
    simp [hf', hg'] },
  { apply mem_ℓp_infty,
    obtain ⟨A, hA⟩ := hf.bdd_above,
    obtain ⟨B, hB⟩ := hg.bdd_above,
    refine ⟨A + B, _⟩,
    rintros a ⟨i, rfl⟩,
    exact le_trans (norm_add_le _ _) (add_le_add (hA ⟨i, rfl⟩) (hB ⟨i, rfl⟩)) },
  apply mem_ℓp_gen hp,
  let C : ℝ := if p.to_real < 1 then 1 else 2 ^ (p.to_real - 1),
  refine summable_of_nonneg_of_le _ _ (((hf.summable hp).add (hg.summable hp)).mul_left C),
  { exact λ b, real.rpow_nonneg_of_nonneg (norm_nonneg (f b + g b)) p.to_real },
  { intros i,
    refine (real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp.le).trans _,
    dsimp [C],
    split_ifs,
    { simpa using nnreal.coe_le_coe.2 (nnreal.rpow_add_le_add_rpow (∥f i∥₊) (∥g i∥₊) hp h.le) },
    { let F : fin 2 → ℝ≥0 := ![∥f i∥₊, ∥g i∥₊],
      have : ∀ i, (0:ℝ) ≤ F i := λ i, (F i).coe_nonneg,
      simp only [not_lt] at h,
      simpa [F, fin.sum_univ_succ] using
        real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (finset.univ : finset (fin 2)) h
        (λ i _, (F i).coe_nonneg) } }
end

lemma sub {f g : Π i, E i} (hf : mem_ℓp f p) (hg : mem_ℓp g p) : mem_ℓp (f - g) p :=
by { rw sub_eq_add_neg, exact hf.add hg.neg }

lemma finset_sum {ι} (s : finset ι) {f : ι → Π i, E i} (hf : ∀ i ∈ s, mem_ℓp (f i) p) :
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

lemma const_smul {f : Π i, E i} (hf : mem_ℓp f p) (c : 𝕜) : mem_ℓp (c • f) p :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    refine hf.finite_dsupport.subset _,
    intros i,
    simp only [ne.def, set.mem_set_of_eq, pi.smul_apply],
    contrapose!,
    intros hf',
    simp [hf'] },
  { obtain ⟨A, hA⟩ := hf.bdd_above,
    refine mem_ℓp_infty ⟨∥c∥ * A, _⟩,
    rintros a ⟨i, rfl⟩,
    simpa [norm_smul] using mul_le_mul_of_nonneg_left (hA ⟨i, rfl⟩) (norm_nonneg c) },
  { apply mem_ℓp_gen hp,
    convert (hf.summable hp).mul_left (∥c∥ ^ p.to_real),
    ext i,
    simp [norm_smul, real.mul_rpow (norm_nonneg c) (norm_nonneg (f i))] },
end

lemma const_mul {f : α → 𝕜} (hf : mem_ℓp f p) (c : 𝕜) : mem_ℓp (λ x, c * f x) p :=
by convert hf.const_smul c

end normed_space

end mem_ℓp

/-!
### lp space

The space of elements of `Π i, E i` satisfying the predicate `mem_ℓp`.
-/

/-- We define `pre_lp E` to be a type synonym for `Π i, E i` which, importantly, does not inherit
the `pi` topology on `Π i, E i` (otherwise this topology would descent to `lp E p` and conflict
with the normed group topology we will later equip it with.)

We choose to deal with this issue by making a type synonym for `Π i, E i` rather than for the `lp`
subgroup itself, because this allows all the spaces `lp E p` (for varying `p`) to be subgroups of
the same ambient group, which permits lemma statements like `lp.monotone` (below). -/
@[derive add_comm_group, nolint unused_arguments]
def pre_lp (E : α → Type*) [Π i, normed_group (E i)] : Type* := Π i, E i

instance pre_lp.unique [is_empty α] : unique (pre_lp E) := pi.unique_of_is_empty E

/-- lp space -/
def lp (E : α → Type*) [Π i, normed_group (E i)]
  (p : ℝ≥0∞) : add_subgroup (pre_lp E) :=
{ carrier := {f | mem_ℓp f p},
  zero_mem' := zero_mem_ℓp,
  add_mem' := λ f g, mem_ℓp.add,
  neg_mem' := λ f, mem_ℓp.neg }

namespace lp

instance : has_coe (lp E p) (Π i, E i) := coe_subtype
instance : has_coe_to_fun (lp E p) (λ _, Π i, E i) := ⟨λ f, ((f : Π i, E i) : Π i, E i)⟩

@[ext] lemma ext {f g : lp E p} (h : (f : Π i, E i) = g) : f = g :=
subtype.ext h

protected lemma ext_iff {f g : lp E p} : f = g ↔ (f : Π i, E i) = g :=
subtype.ext_iff

lemma eq_zero' [is_empty α] (f : lp E p) : f = 0 := subsingleton.elim f 0

protected lemma monotone {p q : ℝ≥0∞} (hpq : q ≤ p) : lp E q ≤ lp E p :=
λ f hf, mem_ℓp.of_exponent_ge hf hpq

protected lemma mem_ℓp (f : lp E p) : mem_ℓp f p := f.prop

variables (E p)
@[simp] lemma coe_fn_zero : ⇑(0 : lp E p) = 0 := rfl
variables {E p}

@[simp] lemma coe_fn_neg (f : lp E p) : ⇑(-f) = -f := rfl

@[simp] lemma coe_fn_add (f g : lp E p) : ⇑(f + g) = f + g := rfl

@[simp] lemma coe_fn_sub (f g : lp E p) : ⇑(f - g) = f - g := rfl

instance : has_norm (lp E p) :=
{ norm := λ f, if hp : p = 0 then by subst hp; exact (lp.mem_ℓp f).finite_dsupport.to_finset.card
   else (if p = ∞ then ⨆ i, ∥f i∥ else (∑' i, ∥f i∥ ^ p.to_real) ^ (1/p.to_real)) }

lemma norm_eq_card_dsupport (f : lp E 0) : ∥f∥ = (lp.mem_ℓp f).finite_dsupport.to_finset.card :=
dif_pos rfl

lemma norm_eq_csupr (f : lp E ∞) : ∥f∥ = ⨆ i, ∥f i∥ :=
begin
  dsimp [norm],
  rw [dif_neg ennreal.top_ne_zero, if_pos rfl]
end

lemma is_lub_norm [nonempty α] (f : lp E ∞) : is_lub (set.range (λ i, ∥f i∥)) ∥f∥ :=
begin
  rw lp.norm_eq_csupr,
  exact is_lub_csupr (lp.mem_ℓp f)
end

lemma norm_eq_tsum_rpow (hp : 0 < p.to_real) (f : lp E p) :
  ∥f∥ = (∑' i, ∥f i∥ ^ p.to_real) ^ (1/p.to_real) :=
begin
  dsimp [norm],
  rw ennreal.to_real_pos_iff at hp,
  rw [dif_neg hp.1.ne', if_neg hp.2.ne],
end

lemma norm_rpow_eq_tsum (hp : 0 < p.to_real) (f : lp E p) :
  ∥f∥ ^ p.to_real = ∑' i, ∥f i∥ ^ p.to_real :=
begin
  rw [norm_eq_tsum_rpow hp, ← real.rpow_mul],
  { field_simp [hp.ne'] },
  apply tsum_nonneg,
  intros i,
  calc (0:ℝ) = 0 ^ p.to_real : by rw real.zero_rpow hp.ne'
  ... ≤ _ : real.rpow_le_rpow rfl.le (norm_nonneg (f i)) hp.le
end

lemma has_sum_norm (hp : 0 < p.to_real) (f : lp E p) :
  has_sum (λ i, ∥f i∥ ^ p.to_real) (∥f∥ ^ p.to_real) :=
begin
  rw norm_rpow_eq_tsum hp,
  exact ((lp.mem_ℓp f).summable hp).has_sum
end

lemma norm_nonneg' (f : lp E p) : 0 ≤ ∥f∥ :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { simp [lp.norm_eq_card_dsupport f] },
  { cases is_empty_or_nonempty α with _i _i; resetI,
    { rw lp.norm_eq_csupr,
      simp [real.csupr_empty] },
    inhabit α,
    exact (norm_nonneg (f (default α))).trans ((lp.is_lub_norm f).1 ⟨default α, rfl⟩) },
  { rw lp.norm_eq_tsum_rpow hp f,
    refine real.rpow_nonneg_of_nonneg (tsum_nonneg _) _,
    exact λ i, real.rpow_nonneg_of_nonneg (norm_nonneg _) _ },
end

@[simp] lemma norm_zero : ∥(0 : lp E p)∥ = 0 :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { simp [lp.norm_eq_card_dsupport] },
  { simp [lp.norm_eq_csupr] },
  { rw lp.norm_eq_tsum_rpow hp,
    have hp' : 1 / p.to_real ≠ 0 := one_div_ne_zero hp.ne',
    simpa [real.zero_rpow hp.ne'] using real.zero_rpow hp' }
end

lemma norm_eq_zero_iff ⦃f : lp E p⦄ : ∥f∥ = 0 ↔ f = 0 :=
begin
  classical,
  refine ⟨λ h, _, by { rintros rfl, exact norm_zero }⟩,
  rcases p.trichotomy with rfl | rfl | hp,
  { ext i,
    have : {i : α | ¬f i = 0} = ∅ := by simpa [lp.norm_eq_card_dsupport f] using h,
    have : (¬ (f i = 0)) = false := congr_fun this i,
    tauto },
  { cases is_empty_or_nonempty α with _i _i; resetI,
    { simp },
    have H : is_lub (set.range (λ i, ∥f i∥)) 0,
    { simpa [h] using lp.is_lub_norm f },
    ext i,
    have : ∥f i∥ = 0 := le_antisymm (H.1 ⟨i, rfl⟩) (norm_nonneg _),
    simpa using this },
  { have hf : has_sum (λ (i : α), ∥f i∥ ^ p.to_real) 0,
    { have := lp.has_sum_norm hp f ,
      rw h at this,
      simpa [real.zero_rpow hp.ne'] using this }, -- why can't the `simp` and `rw` be combined?
    have : ∀ i, 0 ≤ ∥f i∥ ^ p.to_real := λ i, real.rpow_nonneg_of_nonneg (norm_nonneg _) _,
    rw has_sum_zero_iff_of_nonneg this at hf,
    ext i,
    have : f i = 0 ∧ p.to_real ≠ 0,
    { simpa [real.rpow_eq_zero_iff_of_nonneg (norm_nonneg (f i))] using congr_fun hf i },
    exact this.1 },
end

lemma eq_zero_iff_ae_eq_zero {f : lp E p} : f = 0 ↔ ⇑f = 0 :=
by rw [lp.ext_iff, coe_fn_zero]

@[simp] lemma norm_neg ⦃f : lp E p⦄ : ∥-f∥ = ∥f∥ :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { simp [lp.norm_eq_card_dsupport] },
  { cases is_empty_or_nonempty α; resetI,
    { simp [lp.eq_zero' f], },
    apply (lp.is_lub_norm (-f)).unique,
    simpa using lp.is_lub_norm f },
  { suffices : ∥-f∥ ^ p.to_real = ∥f∥ ^ p.to_real,
    { exact real.rpow_left_inj_on hp.ne' (norm_nonneg' _) (norm_nonneg' _) this },
    apply (lp.has_sum_norm hp (-f)).unique,
    simpa using lp.has_sum_norm hp f }
end

instance [hp : fact (1 ≤ p)] : normed_group (lp E p) :=
normed_group.of_core _
{ norm_eq_zero_iff := norm_eq_zero_iff,
  triangle := λ f g, begin
    tactic.unfreeze_local_instances,
    rcases p.dichotomy with rfl | hp',
    { cases is_empty_or_nonempty α; resetI,
      { simp [lp.eq_zero' f] },
      refine (lp.is_lub_norm (f + g)).2 _,
      rintros x ⟨i, rfl⟩,
      refine le_trans _ (add_mem_upper_bounds_add (lp.is_lub_norm f).1 (lp.is_lub_norm g).1
        ⟨_, _, ⟨i, rfl⟩, ⟨i, rfl⟩, rfl⟩),
      exact norm_add_le (f i) (g i) },
    { have hp'' : 0 < p.to_real := zero_lt_one.trans_le hp',
      have hf₁ : ∀ i, 0 ≤ ∥f i∥ := λ i, norm_nonneg _,
      have hg₁ : ∀ i, 0 ≤ ∥g i∥ := λ i, norm_nonneg _,
      have hf₂ := lp.has_sum_norm hp'' f,
      have hg₂ := lp.has_sum_norm hp'' g,
      -- apply Minkowski's inequality
      obtain ⟨C, hC₁, hC₂, hCfg⟩ :=
        real.Lp_add_le_has_sum_of_nonneg hp' hf₁ hg₁ (norm_nonneg' _) (norm_nonneg' _) hf₂ hg₂,
      refine le_trans _ hC₂,
      rw ← real.rpow_le_rpow_iff (norm_nonneg' (f + g)) hC₁ hp'',
      refine has_sum_le _ (lp.has_sum_norm hp'' (f + g)) hCfg,
      intros i,
      exact real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp''.le },
  end,
  norm_neg := norm_neg }

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [Π i, normed_space 𝕜 (E i)]

instance : module 𝕜 (pre_lp E) := pi.module α E 𝕜

lemma mem_lp_const_smul (c : 𝕜) (f : lp E p) : c • (f : pre_lp E) ∈ lp E p :=
(lp.mem_ℓp f).const_smul c

variables (E p 𝕜)

/-- The `𝕜`-submodule of elements of `Π i : α, E i` whose `lp` norm is finite.  This is `lp E p`,
with extra structure. -/
def lp_submodule : submodule 𝕜 (pre_lp E) :=
{ smul_mem' := λ c f hf, by simpa using mem_lp_const_smul c ⟨f, hf⟩,
  .. lp E p }

variables {E p 𝕜}

lemma coe_lp_submodule : (lp_submodule E p 𝕜).to_add_subgroup = lp E p := rfl

instance : module 𝕜 (lp E p) :=
{ .. (lp_submodule E p 𝕜).module }

lemma coe_fn_smul (c : 𝕜) (f : lp E p) : ⇑(c • f) = c • f := rfl

lemma norm_const_smul (hp : p ≠ 0) {c : 𝕜} (f : lp E p) : ∥c • f∥ = ∥c∥ * ∥f∥ :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { exact absurd rfl hp },
  { cases is_empty_or_nonempty α; resetI,
    { simp [lp.eq_zero' f], },
    apply (lp.is_lub_norm (c • f)).unique,
    convert (lp.is_lub_norm f).mul_left (norm_nonneg c),
    ext a,
    simp [coe_fn_smul, norm_smul] },
  { suffices : ∥c • f∥ ^ p.to_real = (∥c∥ * ∥f∥) ^ p.to_real,
    { refine real.rpow_left_inj_on hp.ne' _ _ this,
      { exact norm_nonneg' _ },
      { exact mul_nonneg (norm_nonneg _) (norm_nonneg' _) } },
    apply (lp.has_sum_norm hp (c • f)).unique,
    convert (lp.has_sum_norm hp f).mul_left (∥c∥ ^ p.to_real),
    { simp [coe_fn_smul, norm_smul, real.mul_rpow (norm_nonneg c) (norm_nonneg _)] },
    have hf : 0 ≤ ∥f∥ := lp.norm_nonneg' f,
    simp [coe_fn_smul, norm_smul, real.mul_rpow (norm_nonneg c) hf] }
end

instance [fact (1 ≤ p)] : normed_space 𝕜 (lp E p) :=
{ norm_smul_le := λ c f, begin
    have hp : 0 < p := ennreal.zero_lt_one.trans_le (fact.out _),
    simp [norm_const_smul hp.ne']
  end }

variables {𝕜' : Type*} [normed_field 𝕜']

instance [Π i, normed_space 𝕜' (E i)] [has_scalar 𝕜' 𝕜] [Π i, is_scalar_tower 𝕜' 𝕜 (E i)] :
  is_scalar_tower 𝕜' 𝕜 (lp E p) :=
begin
  refine ⟨λ r c f, _⟩,
  ext1,
  exact (lp.coe_fn_smul _ _).trans (smul_assoc _ _ _)
end

end normed_space

end lp
