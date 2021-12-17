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

This file describes properties of elements `f` of a pi-type `Π i, E i` with finite seminorm,
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

## Implementation

Since `Lp` is defined as an `add_subgroup`, dot notation does not work. Use `Lp.norm_neg f` to
say that `∥-f∥ = ∥f∥`, instead of the non-working `f.norm_neg`.

-/

noncomputable theory
open_locale nnreal ennreal big_operators

variables {α : Type*} {E : α → Type*} {p q : ℝ≥0∞} [Π i, normed_group (E i)]

section p_facts
variables (p)

lemma p_trichotomy : p = 0 ∨ p = ∞ ∨ 0 < p.to_real :=
begin
  rcases eq_or_lt_of_le (bot_le : 0 ≤ p) with (rfl : 0 = p) | (hp : 0 < p),
  { simp },
  rcases eq_or_lt_of_le (le_top : p ≤ ⊤) with rfl | hp',
  { simp },
  simp [ennreal.to_real_pos_iff, hp, hp'.ne],
end

variables {p}

lemma p_trichotomy₂ (hpq : p ≤ q) :
  (p = 0 ∧ q = 0) ∨ (p = 0 ∧ q = ∞) ∨ (p = 0 ∧ 0 < q.to_real) ∨ (p = ∞ ∧ q = ∞)
  ∨ (0 < p.to_real ∧ q = ∞) ∨ (0 < p.to_real ∧ 0 < q.to_real ∧ p.to_real ≤ q.to_real) :=
begin
  rcases eq_or_lt_of_le (bot_le : 0 ≤ p) with (rfl : 0 = p) | (hp : 0 < p),
  { simpa using p_trichotomy q },
  rcases eq_or_lt_of_le (le_top : q ≤ ⊤) with rfl | hq,
  { simpa using p_trichotomy p },
  repeat { right },
  have hq' : 0 < q := lt_of_lt_of_le hp hpq,
  have hp' : p < ⊤ := lt_of_le_of_lt hpq hq,
  simp [ennreal.to_real_le_to_real, ennreal.to_real_pos_iff, hpq, hp, hp'.ne, hq', hq.ne],
end

variables (p)

lemma p_dichotomy [fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.to_real :=
begin
  tactic.unfreeze_local_instances,
  have :  p = ⊤ ∨ 0 < p.to_real ∧ 1 ≤ p.to_real,
  { simpa using p_trichotomy₂ (fact.out _ : 1 ≤ p) },
  exact this.imp_right (λ h, h.2)
end

end p_facts

section ℓp

/-!
### `mem_ℓp` predicate

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
  rcases p_trichotomy₂ hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hp⟩ | ⟨rfl, rfl⟩ | ⟨hq, rfl⟩
    | ⟨hp, hq, hpq'⟩,
  { exact mem_ℓp_zero hfq.eq_zero },
  { rw hfq.eq_zero,
    exact zero_mem_ℓp },
  { rw hfq.eq_zero,
    exact zero_mem_ℓp },
  { exact hfq },
  { apply mem_ℓp_infty,
    obtain ⟨A, hA⟩ := (hfq.summable hq).tendsto_cofinite_zero.bdd_above_range_of_cofinite,
    use A ^ (q.to_real⁻¹),
    rintros x ⟨i, rfl⟩,
    have : 0 ≤ ∥f i∥ ^ q.to_real := real.rpow_nonneg_of_nonneg (norm_nonneg _) _,
    simpa [← real.rpow_mul, mul_inv_cancel hq.ne'] using
      real.rpow_le_rpow this (hA ⟨i, rfl⟩) (inv_nonneg.mpr hq.le) },
  { apply mem_ℓp_gen hq,
    -- rw finset.summable_compl_iff,
    have := hfq.summable hp,
    sorry
  }
end

-- lemma foo {f g : Π i, E i} {A B : ℝ} (hA : A ∈ upper_bounds (set.range (λ i, ∥f i∥)))
--   (hB : B ∈ upper_bounds (set.range (λ i, ∥g i∥))) :
--   A + B ∈ upper_bounds (set.range (λ i, ∥(f + g) i∥)) :=
-- begin
--   rintros a ⟨i, rfl⟩,
--   exact le_trans (norm_add_le _ _) (add_le_add (hA ⟨i, rfl⟩) (hB ⟨i, rfl⟩))
-- end

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

end ℓp

/-!
### Lp space

The space of elements of `Π i, E i` satisfying the predicate `mem_ℓp`.
-/

/-- Lp space -/
def Lp (E : α → Type*) [Π i, normed_group (E i)]
  (p : ℝ≥0∞) : add_subgroup (Π i, E i) :=
{ carrier := {f | mem_ℓp f p},
  zero_mem' := zero_mem_ℓp,
  add_mem' := λ f g, mem_ℓp.add,
  neg_mem' := λ f, mem_ℓp.neg }

namespace Lp

instance : has_coe_to_fun (Lp E p) (λ _, Π i, E i) := ⟨λ f, ((f : Π i, E i) : Π i, E i)⟩

@[ext] lemma ext {f g : Lp E p} (h : (f : Π i, E i) = g) : f = g :=
subtype.ext h

lemma ext_iff {f g : Lp E p} : f = g ↔ (f : Π i, E i) = g :=
subtype.ext_iff

-- move to `group_theory.subgroup.basic`
@[to_additive]
instance _root_.subgroup.subsingleton {G : Type*} [group G] [subsingleton G] (H : set G) :
  subsingleton H :=
⟨ λ a b, subtype.ext (subsingleton.elim (a:G) b)⟩

lemma eq_zero' [is_empty α] (f : Lp E p) : f = 0 := subsingleton.elim f 0

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

lemma norm_nonneg' (f : Lp E p) : 0 ≤ ∥f∥ :=
begin
  rcases p_trichotomy p with rfl | rfl | hp,
  { simp [Lp.norm_eq_zero f] },
  { cases is_empty_or_nonempty α with _i _i; resetI,
    { rw Lp.norm_eq_supr,
      simp [real.supr_empty] },
    inhabit α,
    exact (norm_nonneg (f (default α))).trans ((Lp.is_lub_norm f).1 ⟨default α, rfl⟩) },
  { rw Lp.norm_eq_tsum_rpow hp f,
    refine real.rpow_nonneg_of_nonneg (tsum_nonneg _) _,
    exact λ i, real.rpow_nonneg_of_nonneg (norm_nonneg _) _ },
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

-- move to `topology.algebra.infinite_sum`
lemma _root_.has_sum_zero_iff_of_nonneg {ι α : Type*} [ordered_add_comm_group α]
  [topological_space α] [topological_add_group α] [order_closed_topology α]
  {f : ι → α} (hf : ∀ i, 0 ≤ f i) :
  has_sum f 0 ↔ f = 0 :=
begin
  split,
  { intros hf',
    ext i,
    by_contra hi',
    have hi : 0 < f i := lt_of_le_of_ne (hf i) (ne.symm hi'),
    simpa using has_sum_lt hf hi has_sum_zero hf' },
  { rintros rfl,
    exact has_sum_zero },
end

lemma norm_eq_zero_iff {f : Lp E p} (hp : 0 < p) : ∥f∥ = 0 ↔ f = 0 :=
begin
  classical,
  refine ⟨λ h, _, by { rintros rfl, exact norm_zero }⟩,
  rcases p_trichotomy p with rfl | rfl | hp,
  { exact Lp.eq_zero f },
  { cases is_empty_or_nonempty α with _i _i; resetI,
    { simp },
    have H : is_lub (set.range (λ i, ∥f i∥)) 0,
    { simpa [h] using Lp.is_lub_norm f },
    ext i,
    have : ∥f i∥ = 0 := le_antisymm (H.1 ⟨i, rfl⟩) (norm_nonneg _),
    simpa using this },
  { have hf : has_sum (λ (i : α), ∥f i∥ ^ p.to_real) 0,
    { have := Lp.has_sum_norm hp f ,
      rw h at this,
      simpa [real.zero_rpow hp.ne'] using this }, -- why can't the `simp` and `rw` be combined?
    have : ∀ i, 0 ≤ ∥f i∥ ^ p.to_real := λ i, real.rpow_nonneg_of_nonneg (norm_nonneg _) _,
    rw has_sum_zero_iff_of_nonneg this at hf,
    ext i,
    have : f i = 0 ∧ p.to_real ≠ 0,
    { simpa [real.rpow_eq_zero_iff_of_nonneg (norm_nonneg (f i))] using congr_fun hf i },
    exact this.1 },
end

lemma eq_zero_iff_ae_eq_zero {f : Lp E p} : f = 0 ↔ ⇑f = 0 :=
by rw [ext_iff, coe_fn_zero]

@[simp] lemma norm_neg {f : Lp E p} : ∥-f∥ = ∥f∥ :=
begin
  rcases p_trichotomy p with rfl | rfl | hp,
  { simp [Lp.norm_eq_zero] },
  { cases is_empty_or_nonempty α; resetI,
    { simp [Lp.eq_zero' f], },
    apply (Lp.is_lub_norm (-f)).unique,
    simpa using Lp.is_lub_norm f },
  { suffices : ∥-f∥ ^ p.to_real = ∥f∥ ^ p.to_real, by sorry,
    apply (Lp.has_sum_norm hp (-f)).unique,
    simpa using Lp.has_sum_norm hp f }
end

instance [hp : fact (1 ≤ p)] : normed_group (Lp E p) :=
normed_group.of_core _
{ norm_eq_zero_iff := λ f, norm_eq_zero_iff (ennreal.zero_lt_one.trans_le hp.1),
  triangle := λ f g, begin
    tactic.unfreeze_local_instances,
    rcases p_dichotomy p with rfl | hp',
    { cases is_empty_or_nonempty α; resetI,
      { simp [Lp.eq_zero' f] },
      refine (Lp.is_lub_norm (f + g)).2 _,
      rintros x ⟨i, rfl⟩,
      refine le_trans _ (add_mem_upper_bounds_add (Lp.is_lub_norm f).1 (Lp.is_lub_norm g).1
        ⟨_, _, ⟨i, rfl⟩, ⟨i, rfl⟩, rfl⟩),
      exact norm_add_le (f i) (g i) },
    { -- Minkowski's inequality
      sorry },
  end,
  norm_neg := by simp }

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
begin
  rcases p_trichotomy p with rfl | rfl | hp,
  { simp [Lp.norm_eq_zero] },
  { cases is_empty_or_nonempty α; resetI,
    { simp [Lp.eq_zero' f], },
    apply (Lp.is_lub_norm (c • f)).unique,
    have := Lp.is_lub_norm f,
    simp [coe_fn_smul, norm_smul],
    sorry },
  { suffices : ∥c • f∥ ^ p.to_real = (∥c∥ * ∥f∥) ^ p.to_real, by sorry,
    apply (Lp.has_sum_norm hp (c • f)).unique,
    convert (Lp.has_sum_norm hp f).mul_left (∥c∥ ^ p.to_real),
    { simp [coe_fn_smul, norm_smul, real.mul_rpow (norm_nonneg c) (norm_nonneg _)] },
    have hf : 0 ≤ ∥f∥ := Lp.norm_nonneg' f,
    simp [coe_fn_smul, norm_smul, real.mul_rpow (norm_nonneg c) hf] }
end

instance [fact (1 ≤ p)] : normed_space 𝕜 (Lp E p) :=
{ norm_smul_le := λ _ _, by simp [norm_const_smul] }

instance [Π i, normed_space ℝ (E i)] [has_scalar ℝ 𝕜] [Π i, is_scalar_tower ℝ 𝕜 (E i)] :
  is_scalar_tower ℝ 𝕜 (Lp E p) :=
begin
  refine ⟨λ r c f, _⟩,
  ext1,
  exact (Lp.coe_fn_smul _ _).trans (smul_assoc _ _ _)
end

end normed_space

end Lp
