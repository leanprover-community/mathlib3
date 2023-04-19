/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.mean_inequalities
import analysis.mean_inequalities_pow
import topology.algebra.order.liminf_limsup

/-!
# ℓp space

This file describes properties of elements `f` of a pi-type `Π i, E i` with finite "norm",
defined for `p:ℝ≥0∞` as the size of the support of `f` if `p=0`, `(∑' a, ‖f a‖^p) ^ (1/p)` for
`0 < p < ∞` and `⨆ a, ‖f a‖` for `p=∞`.

The Prop-valued `mem_ℓp f p` states that a function `f : Π i, E i` has finite norm according
to the above definition; that is, `f` has finite support if `p = 0`, `summable (λ a, ‖f a‖^p)` if
`0 < p < ∞`, and `bdd_above (norm '' (set.range f))` if `p = ∞`.

The space `lp E p` is the subtype of elements of `Π i : α, E i` which satisfy `mem_ℓp f p`. For
`1 ≤ p`, the "norm" is genuinely a norm and `lp` is a complete metric space.

## Main definitions

* `mem_ℓp f p` : property that the function `f` satisfies, as appropriate, `f` finitely supported
  if `p = 0`, `summable (λ a, ‖f a‖^p)` if `0 < p < ∞`, and `bdd_above (norm '' (set.range f))` if
  `p = ∞`.
* `lp E p` : elements of `Π i : α, E i` such that `mem_ℓp f p`. Defined as an `add_subgroup` of
  a type synonym `pre_lp` for `Π i : α, E i`, and equipped with a `normed_add_comm_group` structure.
  Under appropriate conditions, this is also equipped with the instances `lp.normed_space`,
  `lp.complete_space`. For `p=∞`, there is also `lp.infty_normed_ring`,
  `lp.infty_normed_algebra`, `lp.infty_star_ring` and `lp.infty_cstar_ring`.

## Main results

* `mem_ℓp.of_exponent_ge`: For `q ≤ p`, a function which is `mem_ℓp` for `q` is also `mem_ℓp` for
  `p`
* `lp.mem_ℓp_of_tendsto`, `lp.norm_le_of_tendsto`: A pointwise limit of functions in `lp`, all with
  `lp` norm `≤ C`, is itself in `lp` and has `lp` norm `≤ C`.
* `lp.tsum_mul_le_mul_norm`: basic form of Hölder's inequality

## Implementation

Since `lp` is defined as an `add_subgroup`, dot notation does not work. Use `lp.norm_neg f` to
say that `‖-f‖ = ‖f‖`, instead of the non-working `f.norm_neg`.

## TODO

* More versions of Hölder's inequality (for example: the case `p = 1`, `q = ∞`; a version for normed
  rings which has `‖∑' i, f i * g i‖` rather than `∑' i, ‖f i‖ * g i‖` on the RHS; a version for
  three exponents satisfying `1 / r = 1 / p + 1 / q`)

-/

noncomputable theory
open_locale nnreal ennreal big_operators

variables {α : Type*} {E : α → Type*} {p q : ℝ≥0∞} [Π i, normed_add_comm_group (E i)]

/-!
### `mem_ℓp` predicate

-/

/-- The property that `f : Π i : α, E i`
* is finitely supported, if `p = 0`, or
* admits an upper bound for `set.range (λ i, ‖f i‖)`, if `p = ∞`, or
* has the series `∑' i, ‖f i‖ ^ p` be summable, if `0 < p < ∞`. -/
def mem_ℓp (f : Π i, E i) (p : ℝ≥0∞) : Prop :=
if p = 0 then (set.finite {i | f i ≠ 0}) else
  (if p = ∞ then bdd_above (set.range (λ i, ‖f i‖)) else summable (λ i, ‖f i‖ ^ p.to_real))

lemma mem_ℓp_zero_iff {f : Π i, E i} : mem_ℓp f 0 ↔ set.finite {i | f i ≠ 0} :=
by dsimp [mem_ℓp]; rw [if_pos rfl]

lemma mem_ℓp_zero {f : Π i, E i} (hf : set.finite {i | f i ≠ 0}) : mem_ℓp f 0 :=
mem_ℓp_zero_iff.2 hf

lemma mem_ℓp_infty_iff {f : Π i, E i} : mem_ℓp f ∞ ↔ bdd_above (set.range (λ i, ‖f i‖)) :=
by dsimp [mem_ℓp]; rw [if_neg ennreal.top_ne_zero, if_pos rfl]

lemma mem_ℓp_infty {f : Π i, E i} (hf : bdd_above (set.range (λ i, ‖f i‖))) : mem_ℓp f ∞ :=
mem_ℓp_infty_iff.2 hf

lemma mem_ℓp_gen_iff (hp : 0 < p.to_real) {f : Π i, E i} :
  mem_ℓp f p ↔ summable (λ i, ‖f i‖ ^ p.to_real) :=
begin
  rw ennreal.to_real_pos_iff at hp,
  dsimp [mem_ℓp],
  rw [if_neg hp.1.ne', if_neg hp.2.ne],
end

lemma mem_ℓp_gen {f : Π i, E i} (hf : summable (λ i, ‖f i‖ ^ p.to_real)) :
  mem_ℓp f p :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    have H : summable (λ i : α, (1:ℝ)) := by simpa using hf,
    exact (finite_of_summable_const (by norm_num) H).subset (set.subset_univ _) },
  { apply mem_ℓp_infty,
    have H : summable (λ i : α, (1:ℝ)) := by simpa using hf,
    simpa using ((finite_of_summable_const (by norm_num) H).image (λ i, ‖f i‖)).bdd_above },
  exact (mem_ℓp_gen_iff hp).2 hf
end

lemma mem_ℓp_gen' {C : ℝ} {f : Π i, E i} (hf : ∀ s : finset α, ∑ i in s, ‖f i‖ ^ p.to_real ≤ C) :
  mem_ℓp f p :=
begin
  apply mem_ℓp_gen,
  use ⨆ s : finset α, ∑ i in s, ‖f i‖ ^ p.to_real,
  apply has_sum_of_is_lub_of_nonneg,
  { intros b,
    exact real.rpow_nonneg_of_nonneg (norm_nonneg _) _ },
  apply is_lub_csupr,
  use C,
  rintros - ⟨s, rfl⟩,
  exact hf s
end

lemma zero_mem_ℓp : mem_ℓp (0 : Π i, E i) p :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    simp },
  { apply mem_ℓp_infty,
    simp only [norm_zero, pi.zero_apply],
    exact bdd_above_singleton.mono set.range_const_subset, },
  { apply mem_ℓp_gen,
    simp [real.zero_rpow hp.ne', summable_zero], }
end

lemma zero_mem_ℓp' : mem_ℓp (λ i : α, (0 : E i)) p := zero_mem_ℓp

namespace mem_ℓp

lemma finite_dsupport {f : Π i, E i} (hf : mem_ℓp f 0) : set.finite {i | f i ≠ 0} :=
mem_ℓp_zero_iff.1 hf

lemma bdd_above {f : Π i, E i} (hf : mem_ℓp f ∞) : bdd_above (set.range (λ i, ‖f i‖)) :=
mem_ℓp_infty_iff.1 hf

lemma summable (hp : 0 < p.to_real) {f : Π i, E i} (hf : mem_ℓp f p) :
  summable (λ i, ‖f i‖ ^ p.to_real) :=
(mem_ℓp_gen_iff hp).1 hf

lemma neg {f : Π i, E i} (hf : mem_ℓp f p) : mem_ℓp (-f) p :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    simp [hf.finite_dsupport] },
  { apply mem_ℓp_infty,
    simpa using hf.bdd_above },
  { apply mem_ℓp_gen,
    simpa using hf.summable hp },
end

@[simp] lemma neg_iff {f : Π i, E i} : mem_ℓp (-f) p ↔ mem_ℓp f p :=
⟨λ h, neg_neg f ▸ h.neg, mem_ℓp.neg⟩

lemma of_exponent_ge {p q : ℝ≥0∞} {f : Π i, E i}
  (hfq : mem_ℓp f q) (hpq : q ≤ p) :
  mem_ℓp f p :=
begin
  rcases ennreal.trichotomy₂ hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hp⟩ | ⟨rfl, rfl⟩ | ⟨hq, rfl⟩
    | ⟨hq, hp, hpq'⟩,
  { exact hfq },
  { apply mem_ℓp_infty,
    obtain ⟨C, hC⟩ := (hfq.finite_dsupport.image (λ i, ‖f i‖)).bdd_above,
    use max 0 C,
    rintros x ⟨i, rfl⟩,
    by_cases hi : f i = 0,
    { simp [hi] },
    { exact (hC ⟨i, hi, rfl⟩).trans (le_max_right _ _) } },
  { apply mem_ℓp_gen,
    have : ∀ i ∉ hfq.finite_dsupport.to_finset, ‖f i‖ ^ p.to_real = 0,
    { intros i hi,
      have : f i = 0 := by simpa using hi,
      simp [this, real.zero_rpow hp.ne'] },
    exact summable_of_ne_finset_zero this },
  { exact hfq },
  { apply mem_ℓp_infty,
    obtain ⟨A, hA⟩ := (hfq.summable hq).tendsto_cofinite_zero.bdd_above_range_of_cofinite,
    use A ^ (q.to_real⁻¹),
    rintros x ⟨i, rfl⟩,
    have : 0 ≤ ‖f i‖ ^ q.to_real := real.rpow_nonneg_of_nonneg (norm_nonneg _) _,
    simpa [← real.rpow_mul, mul_inv_cancel hq.ne'] using
      real.rpow_le_rpow this (hA ⟨i, rfl⟩) (inv_nonneg.mpr hq.le) },
  { apply mem_ℓp_gen,
    have hf' := hfq.summable hq,
    refine summable_of_norm_bounded_eventually _ hf' (@set.finite.subset _ {i | 1 ≤ ‖f i‖} _ _ _),
    { have H : {x : α | 1 ≤ ‖f x‖ ^ q.to_real}.finite,
      { simpa using eventually_lt_of_tendsto_lt (by norm_num : (0:ℝ) < 1)
          hf'.tendsto_cofinite_zero },
      exact H.subset (λ i hi, real.one_le_rpow hi hq.le) },
    { show ∀ i, ¬ (|‖f i‖ ^ p.to_real| ≤ ‖f i‖ ^ q.to_real) → 1 ≤ ‖f i‖,
      intros i hi,
      have : 0 ≤ ‖f i‖ ^ p.to_real := real.rpow_nonneg_of_nonneg (norm_nonneg _) p.to_real,
      simp only [abs_of_nonneg, this] at hi,
      contrapose! hi,
      exact real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hi.le hq.le hpq' } }
end

lemma add {f g : Π i, E i} (hf : mem_ℓp f p) (hg : mem_ℓp g p) : mem_ℓp (f + g) p :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    refine (hf.finite_dsupport.union hg.finite_dsupport).subset (λ i, _),
    simp only [pi.add_apply, ne.def, set.mem_union, set.mem_set_of_eq],
    contrapose!,
    rintros ⟨hf', hg'⟩,
    simp [hf', hg'] },
  { apply mem_ℓp_infty,
    obtain ⟨A, hA⟩ := hf.bdd_above,
    obtain ⟨B, hB⟩ := hg.bdd_above,
    refine ⟨A + B, _⟩,
    rintros a ⟨i, rfl⟩,
    exact le_trans (norm_add_le _ _) (add_le_add (hA ⟨i, rfl⟩) (hB ⟨i, rfl⟩)) },
  apply mem_ℓp_gen,
  let C : ℝ := if p.to_real < 1 then 1 else 2 ^ (p.to_real - 1),
  refine summable_of_nonneg_of_le _ (λ i, _) (((hf.summable hp).add (hg.summable hp)).mul_left C),
  { exact λ b, real.rpow_nonneg_of_nonneg (norm_nonneg (f b + g b)) p.to_real },
  { refine (real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp.le).trans _,
    dsimp [C],
    split_ifs with h h,
    { simpa using nnreal.coe_le_coe.2 (nnreal.rpow_add_le_add_rpow (‖f i‖₊) (‖g i‖₊) hp.le h.le) },
    { let F : fin 2 → ℝ≥0 := ![‖f i‖₊, ‖g i‖₊],
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
    refine hf.finite_dsupport.subset (λ i, (_ : ¬c • f i = 0 → ¬f i = 0)),
    exact not_imp_not.mpr (λ hf', hf'.symm ▸ (smul_zero c)) },
  { obtain ⟨A, hA⟩ := hf.bdd_above,
    refine mem_ℓp_infty ⟨‖c‖ * A, _⟩,
    rintros a ⟨i, rfl⟩,
    simpa [norm_smul] using mul_le_mul_of_nonneg_left (hA ⟨i, rfl⟩) (norm_nonneg c) },
  { apply mem_ℓp_gen,
    convert (hf.summable hp).mul_left (‖c‖ ^ p.to_real),
    ext i,
    simp [norm_smul, real.mul_rpow (norm_nonneg c) (norm_nonneg (f i))] },
end

lemma const_mul {f : α → 𝕜} (hf : mem_ℓp f p) (c : 𝕜) : mem_ℓp (λ x, c * f x) p :=
@mem_ℓp.const_smul α (λ i, 𝕜) _ _ 𝕜 _ _ _ hf c

end normed_space

end mem_ℓp

/-!
### lp space

The space of elements of `Π i, E i` satisfying the predicate `mem_ℓp`.
-/

/-- We define `pre_lp E` to be a type synonym for `Π i, E i` which, importantly, does not inherit
the `pi` topology on `Π i, E i` (otherwise this topology would descend to `lp E p` and conflict
with the normed group topology we will later equip it with.)

We choose to deal with this issue by making a type synonym for `Π i, E i` rather than for the `lp`
subgroup itself, because this allows all the spaces `lp E p` (for varying `p`) to be subgroups of
the same ambient group, which permits lemma statements like `lp.monotone` (below). -/
@[derive add_comm_group, nolint unused_arguments]
def pre_lp (E : α → Type*) [Π i, normed_add_comm_group (E i)] : Type* := Π i, E i

instance pre_lp.unique [is_empty α] : unique (pre_lp E) := pi.unique_of_is_empty E

/-- lp space -/
def lp (E : α → Type*) [Π i, normed_add_comm_group (E i)]
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

@[simp] lemma coe_fn_sum {ι : Type*} (f : ι → lp E p) (s : finset ι) :
  ⇑(∑ i in s, f i) = ∑ i in s, ⇑(f i) :=
begin
  classical,
  refine finset.induction _ _ s,
  { simp },
  intros i s his,
  simp [finset.sum_insert his],
end

@[simp] lemma coe_fn_sub (f g : lp E p) : ⇑(f - g) = f - g := rfl

instance : has_norm (lp E p) :=
{ norm := λ f, if hp : p = 0 then by subst hp; exact (lp.mem_ℓp f).finite_dsupport.to_finset.card
   else (if p = ∞ then ⨆ i, ‖f i‖ else (∑' i, ‖f i‖ ^ p.to_real) ^ (1/p.to_real)) }

lemma norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp.mem_ℓp f).finite_dsupport.to_finset.card :=
dif_pos rfl

lemma norm_eq_csupr (f : lp E ∞) : ‖f‖ = ⨆ i, ‖f i‖ :=
begin
  dsimp [norm],
  rw [dif_neg ennreal.top_ne_zero, if_pos rfl]
end

lemma is_lub_norm [nonempty α] (f : lp E ∞) : is_lub (set.range (λ i, ‖f i‖)) ‖f‖ :=
begin
  rw lp.norm_eq_csupr,
  exact is_lub_csupr (lp.mem_ℓp f)
end

lemma norm_eq_tsum_rpow (hp : 0 < p.to_real) (f : lp E p) :
  ‖f‖ = (∑' i, ‖f i‖ ^ p.to_real) ^ (1/p.to_real) :=
begin
  dsimp [norm],
  rw ennreal.to_real_pos_iff at hp,
  rw [dif_neg hp.1.ne', if_neg hp.2.ne],
end

lemma norm_rpow_eq_tsum (hp : 0 < p.to_real) (f : lp E p) :
  ‖f‖ ^ p.to_real = ∑' i, ‖f i‖ ^ p.to_real :=
begin
  rw [norm_eq_tsum_rpow hp, ← real.rpow_mul],
  { field_simp [hp.ne'] },
  apply tsum_nonneg,
  intros i,
  calc (0:ℝ) = 0 ^ p.to_real : by rw real.zero_rpow hp.ne'
  ... ≤ _ : real.rpow_le_rpow rfl.le (norm_nonneg (f i)) hp.le
end

lemma has_sum_norm (hp : 0 < p.to_real) (f : lp E p) :
  has_sum (λ i, ‖f i‖ ^ p.to_real) (‖f‖ ^ p.to_real) :=
begin
  rw norm_rpow_eq_tsum hp,
  exact ((lp.mem_ℓp f).summable hp).has_sum
end

lemma norm_nonneg' (f : lp E p) : 0 ≤ ‖f‖ :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { simp [lp.norm_eq_card_dsupport f] },
  { cases is_empty_or_nonempty α with _i _i; resetI,
    { rw lp.norm_eq_csupr,
      simp [real.csupr_empty] },
    inhabit α,
    exact (norm_nonneg (f default)).trans ((lp.is_lub_norm f).1 ⟨default, rfl⟩) },
  { rw lp.norm_eq_tsum_rpow hp f,
    refine real.rpow_nonneg_of_nonneg (tsum_nonneg _) _,
    exact λ i, real.rpow_nonneg_of_nonneg (norm_nonneg _) _ },
end

@[simp] lemma norm_zero : ‖(0 : lp E p)‖ = 0 :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { simp [lp.norm_eq_card_dsupport] },
  { simp [lp.norm_eq_csupr] },
  { rw lp.norm_eq_tsum_rpow hp,
    have hp' : 1 / p.to_real ≠ 0 := one_div_ne_zero hp.ne',
    simpa [real.zero_rpow hp.ne'] using real.zero_rpow hp' }
end

lemma norm_eq_zero_iff {f : lp E p} : ‖f‖ = 0 ↔ f = 0 :=
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
    have H : is_lub (set.range (λ i, ‖f i‖)) 0,
    { simpa [h] using lp.is_lub_norm f },
    ext i,
    have : ‖f i‖ = 0 := le_antisymm (H.1 ⟨i, rfl⟩) (norm_nonneg _),
    simpa using this },
  { have hf : has_sum (λ (i : α), ‖f i‖ ^ p.to_real) 0,
    { have := lp.has_sum_norm hp f,
      rwa [h, real.zero_rpow hp.ne'] at this },
    have : ∀ i, 0 ≤ ‖f i‖ ^ p.to_real := λ i, real.rpow_nonneg_of_nonneg (norm_nonneg _) _,
    rw has_sum_zero_iff_of_nonneg this at hf,
    ext i,
    have : f i = 0 ∧ p.to_real ≠ 0,
    { simpa [real.rpow_eq_zero_iff_of_nonneg (norm_nonneg (f i))] using congr_fun hf i },
    exact this.1 },
end

lemma eq_zero_iff_coe_fn_eq_zero {f : lp E p} : f = 0 ↔ ⇑f = 0 :=
by rw [lp.ext_iff, coe_fn_zero]

@[simp] lemma norm_neg ⦃f : lp E p⦄ : ‖-f‖ = ‖f‖ :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { simp [lp.norm_eq_card_dsupport] },
  { cases is_empty_or_nonempty α; resetI,
    { simp [lp.eq_zero' f], },
    apply (lp.is_lub_norm (-f)).unique,
    simpa using lp.is_lub_norm f },
  { suffices : ‖-f‖ ^ p.to_real = ‖f‖ ^ p.to_real,
    { exact real.rpow_left_inj_on hp.ne' (norm_nonneg' _) (norm_nonneg' _) this },
    apply (lp.has_sum_norm hp (-f)).unique,
    simpa using lp.has_sum_norm hp f }
end

instance [hp : fact (1 ≤ p)] : normed_add_comm_group (lp E p) :=
add_group_norm.to_normed_add_comm_group
{ to_fun := norm,
  map_zero' := norm_zero,
  neg' := norm_neg,
  add_le' := λ f g, begin
    unfreezingI { rcases p.dichotomy with rfl | hp' },
    { casesI is_empty_or_nonempty α,
      { simp [lp.eq_zero' f] },
      refine (lp.is_lub_norm (f + g)).2 _,
      rintros x ⟨i, rfl⟩,
      refine le_trans _ (add_mem_upper_bounds_add (lp.is_lub_norm f).1 (lp.is_lub_norm g).1
        ⟨_, _, ⟨i, rfl⟩, ⟨i, rfl⟩, rfl⟩),
      exact norm_add_le (f i) (g i) },
    { have hp'' : 0 < p.to_real := zero_lt_one.trans_le hp',
      have hf₁ : ∀ i, 0 ≤ ‖f i‖ := λ i, norm_nonneg _,
      have hg₁ : ∀ i, 0 ≤ ‖g i‖ := λ i, norm_nonneg _,
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
  eq_zero_of_map_eq_zero' := λ f, norm_eq_zero_iff.1 }

-- TODO: define an `ennreal` version of `is_conjugate_exponent`, and then express this inequality
-- in a better version which also covers the case `p = 1, q = ∞`.
/-- Hölder inequality -/
protected lemma tsum_mul_le_mul_norm {p q : ℝ≥0∞}
  (hpq : p.to_real.is_conjugate_exponent q.to_real) (f : lp E p) (g : lp E q) :
  summable (λ i, ‖f i‖ * ‖g i‖) ∧ ∑' i, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ :=
begin
  have hf₁ : ∀ i, 0 ≤ ‖f i‖ := λ i, norm_nonneg _,
  have hg₁ : ∀ i, 0 ≤ ‖g i‖ := λ i, norm_nonneg _,
  have hf₂ := lp.has_sum_norm hpq.pos f,
  have hg₂ := lp.has_sum_norm hpq.symm.pos g,
  obtain ⟨C, -, hC', hC⟩ :=
    real.inner_le_Lp_mul_Lq_has_sum_of_nonneg hpq (norm_nonneg' _) (norm_nonneg' _) hf₁ hg₁ hf₂ hg₂,
  rw ← hC.tsum_eq at hC',
  exact ⟨hC.summable, hC'⟩
end

protected lemma summable_mul {p q : ℝ≥0∞}
  (hpq : p.to_real.is_conjugate_exponent q.to_real) (f : lp E p) (g : lp E q) :
  summable (λ i, ‖f i‖ * ‖g i‖) :=
(lp.tsum_mul_le_mul_norm hpq f g).1

protected lemma tsum_mul_le_mul_norm' {p q : ℝ≥0∞}
  (hpq : p.to_real.is_conjugate_exponent q.to_real) (f : lp E p) (g : lp E q) :
  ∑' i, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ :=
(lp.tsum_mul_le_mul_norm hpq f g).2

section compare_pointwise

lemma norm_apply_le_norm (hp : p ≠ 0) (f : lp E p) (i : α) : ‖f i‖ ≤ ‖f‖ :=
begin
  rcases eq_or_ne p ∞ with rfl | hp',
  { haveI : nonempty α := ⟨i⟩,
    exact (is_lub_norm f).1 ⟨i, rfl⟩ },
  have hp'' : 0 < p.to_real := ennreal.to_real_pos hp hp',
  have : ∀ i, 0 ≤ ‖f i‖ ^ p.to_real,
  { exact λ i, real.rpow_nonneg_of_nonneg (norm_nonneg _) _ },
  rw ← real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg' _) hp'',
  convert le_has_sum (has_sum_norm hp'' f) i (λ i hi, this i),
end

lemma sum_rpow_le_norm_rpow (hp : 0 < p.to_real) (f : lp E p) (s : finset α) :
  ∑ i in s, ‖f i‖ ^ p.to_real ≤ ‖f‖ ^ p.to_real :=
begin
  rw lp.norm_rpow_eq_tsum hp f,
  have : ∀ i, 0 ≤ ‖f i‖ ^ p.to_real,
  { exact λ i, real.rpow_nonneg_of_nonneg (norm_nonneg _) _ },
  refine sum_le_tsum _ (λ i hi, this i) _,
  exact (lp.mem_ℓp f).summable hp
end

lemma norm_le_of_forall_le' [nonempty α] {f : lp E ∞} (C : ℝ) (hCf : ∀ i, ‖f i‖ ≤ C) : ‖f‖ ≤ C :=
begin
  refine (is_lub_norm f).2 _,
  rintros - ⟨i, rfl⟩,
  exact hCf i,
end

lemma norm_le_of_forall_le {f : lp E ∞} {C : ℝ} (hC : 0 ≤ C) (hCf : ∀ i, ‖f i‖ ≤ C) : ‖f‖ ≤ C :=
begin
  casesI is_empty_or_nonempty α,
  { simpa [eq_zero' f] using hC, },
  { exact norm_le_of_forall_le' C hCf },
end

lemma norm_le_of_tsum_le (hp : 0 < p.to_real) {C : ℝ} (hC : 0 ≤ C) {f : lp E p}
  (hf : ∑' i, ‖f i‖ ^ p.to_real ≤ C ^ p.to_real) :
  ‖f‖ ≤ C :=
begin
  rw [← real.rpow_le_rpow_iff (norm_nonneg' _) hC hp, norm_rpow_eq_tsum hp],
  exact hf,
end

lemma norm_le_of_forall_sum_le (hp : 0 < p.to_real) {C : ℝ} (hC : 0 ≤ C) {f : lp E p}
  (hf : ∀ s : finset α, ∑ i in s, ‖f i‖ ^ p.to_real ≤ C ^ p.to_real) :
  ‖f‖ ≤ C :=
norm_le_of_tsum_le hp hC (tsum_le_of_sum_le ((lp.mem_ℓp f).summable hp) hf)

end compare_pointwise

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [Π i, normed_space 𝕜 (E i)]

instance : module 𝕜 (pre_lp E) := pi.module α E 𝕜

lemma mem_lp_const_smul (c : 𝕜) (f : lp E p) : c • (f : pre_lp E) ∈ lp E p :=
(lp.mem_ℓp f).const_smul c

variables (E p 𝕜)

/-- The `𝕜`-submodule of elements of `Π i : α, E i` whose `lp` norm is finite.  This is `lp E p`,
with extra structure. -/
def _root_.lp_submodule : submodule 𝕜 (pre_lp E) :=
{ smul_mem' := λ c f hf, by simpa using mem_lp_const_smul c ⟨f, hf⟩,
  .. lp E p }

variables {E p 𝕜}

lemma coe_lp_submodule : (lp_submodule E p 𝕜).to_add_subgroup = lp E p := rfl

instance : module 𝕜 (lp E p) :=
{ .. (lp_submodule E p 𝕜).module }

@[simp] lemma coe_fn_smul (c : 𝕜) (f : lp E p) : ⇑(c • f) = c • f := rfl

lemma norm_const_smul (hp : p ≠ 0) {c : 𝕜} (f : lp E p) : ‖c • f‖ = ‖c‖ * ‖f‖ :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { exact absurd rfl hp },
  { cases is_empty_or_nonempty α; resetI,
    { simp [lp.eq_zero' f], },
    apply (lp.is_lub_norm (c • f)).unique,
    convert (lp.is_lub_norm f).mul_left (norm_nonneg c),
    ext a,
    simp [coe_fn_smul, norm_smul] },
  { suffices : ‖c • f‖ ^ p.to_real = (‖c‖ * ‖f‖) ^ p.to_real,
    { refine real.rpow_left_inj_on hp.ne' _ _ this,
      { exact norm_nonneg' _ },
      { exact mul_nonneg (norm_nonneg _) (norm_nonneg' _) } },
    apply (lp.has_sum_norm hp (c • f)).unique,
    convert (lp.has_sum_norm hp f).mul_left (‖c‖ ^ p.to_real),
    { simp [coe_fn_smul, norm_smul, real.mul_rpow (norm_nonneg c) (norm_nonneg _)] },
    have hf : 0 ≤ ‖f‖ := lp.norm_nonneg' f,
    simp [coe_fn_smul, norm_smul, real.mul_rpow (norm_nonneg c) hf] }
end

instance [fact (1 ≤ p)] : normed_space 𝕜 (lp E p) :=
{ norm_smul_le := λ c f, begin
    have hp : 0 < p := zero_lt_one.trans_le (fact.out _),
    simp [norm_const_smul hp.ne']
  end }

variables {𝕜' : Type*} [normed_field 𝕜']

instance [Π i, normed_space 𝕜' (E i)] [has_smul 𝕜' 𝕜] [Π i, is_scalar_tower 𝕜' 𝕜 (E i)] :
  is_scalar_tower 𝕜' 𝕜 (lp E p) :=
begin
  refine ⟨λ r c f, _⟩,
  ext1,
  exact (lp.coe_fn_smul _ _).trans (smul_assoc _ _ _)
end

end normed_space

section normed_star_group

variables [Π i, star_add_monoid (E i)] [Π i, normed_star_group (E i)]

lemma _root_.mem_ℓp.star_mem {f : Π i, E i}
  (hf : mem_ℓp f p) : mem_ℓp (star f) p :=
begin
  rcases p.trichotomy with rfl | rfl | hp,
  { apply mem_ℓp_zero,
    simp [hf.finite_dsupport] },
  { apply mem_ℓp_infty,
    simpa using hf.bdd_above },
  { apply mem_ℓp_gen,
    simpa using hf.summable hp },
end

@[simp] lemma _root_.mem_ℓp.star_iff {f : Π i, E i} : mem_ℓp (star f) p ↔ mem_ℓp f p :=
⟨λ h, star_star f ▸ mem_ℓp.star_mem h ,mem_ℓp.star_mem⟩

instance : has_star (lp E p) :=
{ star := λ f, ⟨(star f : Π i, E i), f.property.star_mem⟩}

@[simp] lemma coe_fn_star (f : lp E p) : ⇑(star f) = star f := rfl
@[simp] protected theorem star_apply (f : lp E p) (i : α) : star f i = star (f i) := rfl

instance : has_involutive_star (lp E p) := { star_involutive := λ x, by {ext, simp} }

instance : star_add_monoid (lp E p) := { star_add := λ f g, ext $ star_add _ _ }

instance [hp : fact (1 ≤ p)] : normed_star_group (lp E p) :=
{ norm_star := λ f,
  begin
    unfreezingI { rcases p.trichotomy with rfl | rfl | h },
    { exfalso,
      have := ennreal.to_real_mono ennreal.zero_ne_top hp.elim,
      norm_num at this,},
    { simp only [lp.norm_eq_csupr, lp.star_apply, norm_star] },
    { simp only [lp.norm_eq_tsum_rpow h, lp.star_apply, norm_star] }
  end }

variables {𝕜 : Type*} [has_star 𝕜] [normed_field 𝕜]
variables [Π i, normed_space 𝕜 (E i)] [Π i, star_module 𝕜 (E i)]

instance : star_module 𝕜 (lp E p) := { star_smul := λ r f, ext $ star_smul _ _ }

end normed_star_group

section non_unital_normed_ring

variables {I : Type*} {B : I → Type*} [Π i, non_unital_normed_ring (B i)]

lemma _root_.mem_ℓp.infty_mul {f g : Π i, B i} (hf : mem_ℓp f ∞) (hg : mem_ℓp g ∞) :
  mem_ℓp (f * g) ∞ :=
begin
  rw mem_ℓp_infty_iff,
  obtain ⟨⟨Cf, hCf⟩, ⟨Cg, hCg⟩⟩ := ⟨hf.bdd_above, hg.bdd_above⟩,
  refine ⟨Cf * Cg, _⟩,
  rintros _ ⟨i, rfl⟩,
  calc ‖(f * g) i‖ ≤ ‖f i‖ * ‖g i‖ : norm_mul_le (f i) (g i)
  ...             ≤ Cf * Cg       : mul_le_mul (hCf ⟨i, rfl⟩) (hCg ⟨i, rfl⟩) (norm_nonneg _)
                                      ((norm_nonneg _).trans (hCf ⟨i, rfl⟩))
end

instance : has_mul (lp B ∞) :=
{ mul := λ f g, ⟨(f  * g : Π i, B i) , f.property.infty_mul g.property⟩}

@[simp] lemma infty_coe_fn_mul (f g : lp B ∞) : ⇑(f * g) = f * g := rfl

instance : non_unital_ring (lp B ∞) :=
function.injective.non_unital_ring lp.has_coe_to_fun.coe (subtype.coe_injective)
  (lp.coe_fn_zero B ∞) lp.coe_fn_add infty_coe_fn_mul lp.coe_fn_neg lp.coe_fn_sub
  (λ _ _, rfl) (λ _ _,rfl)

instance : non_unital_normed_ring (lp B ∞) :=
{ norm_mul := λ f g, lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg f) (norm_nonneg g))
    (λ i, calc ‖(f * g) i‖ ≤ ‖f i‖ * ‖g i‖ : norm_mul_le _ _
    ...                    ≤ ‖f‖ * ‖g‖
    : mul_le_mul (lp.norm_apply_le_norm ennreal.top_ne_zero f i)
        (lp.norm_apply_le_norm ennreal.top_ne_zero g i) (norm_nonneg _) (norm_nonneg _)),
  .. lp.normed_add_comm_group }

-- we also want a `non_unital_normed_comm_ring` instance, but this has to wait for #13719

instance infty_is_scalar_tower {𝕜} [normed_field 𝕜] [Π i, normed_space 𝕜 (B i)]
  [Π i, is_scalar_tower 𝕜 (B i) (B i)] :
  is_scalar_tower 𝕜 (lp B ∞) (lp B ∞) :=
⟨λ r f g, lp.ext $ smul_assoc r ⇑f ⇑g⟩

instance infty_smul_comm_class {𝕜} [normed_field 𝕜] [Π i, normed_space 𝕜 (B i)]
  [Π i, smul_comm_class 𝕜 (B i) (B i)] :
  smul_comm_class 𝕜 (lp B ∞) (lp B ∞) :=
⟨λ r f g, lp.ext $ smul_comm r ⇑f ⇑g⟩

section star_ring

variables [Π i, star_ring (B i)] [Π i, normed_star_group (B i)]

instance infty_star_ring : star_ring (lp B ∞) :=
{ star_mul := λ f g, ext $ star_mul (_ : Π i, B i) _,
  .. (show star_add_monoid (lp B ∞),
      by { letI : Π i, star_add_monoid (B i) := λ i, infer_instance, apply_instance }) }

instance infty_cstar_ring [∀ i, cstar_ring (B i)] : cstar_ring (lp B ∞) :=
{ norm_star_mul_self := λ f,
  begin
    apply le_antisymm,
    { rw ←sq,
      refine lp.norm_le_of_forall_le (sq_nonneg ‖ f ‖) (λ i, _),
      simp only [lp.star_apply, cstar_ring.norm_star_mul_self, ←sq, infty_coe_fn_mul, pi.mul_apply],
      refine sq_le_sq' _ (lp.norm_apply_le_norm ennreal.top_ne_zero _ _),
      linarith [norm_nonneg (f i), norm_nonneg f] },
    { rw [←sq, ←real.le_sqrt (norm_nonneg _) (norm_nonneg _)],
      refine lp.norm_le_of_forall_le (‖star f * f‖.sqrt_nonneg) (λ i, _),
      rw [real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ←cstar_ring.norm_star_mul_self],
      exact lp.norm_apply_le_norm ennreal.top_ne_zero (star f * f) i, }
  end }

end star_ring

end non_unital_normed_ring

section normed_ring

variables {I : Type*} {B : I → Type*} [Π i, normed_ring (B i)]

instance _root_.pre_lp.ring : ring (pre_lp B) := pi.ring

variables [Π i, norm_one_class (B i)]

lemma _root_.one_mem_ℓp_infty : mem_ℓp (1 : Π i, B i) ∞ :=
⟨1, by { rintros i ⟨i, rfl⟩, exact norm_one.le,}⟩

variables (B)

/-- The `𝕜`-subring of elements of `Π i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
with extra structure. -/
def _root_.lp_infty_subring : subring (pre_lp B) :=
{ carrier := {f | mem_ℓp f ∞},
  one_mem' := one_mem_ℓp_infty,
  mul_mem' := λ f g hf hg, hf.infty_mul hg,
  .. lp B ∞ }

variables {B}

instance infty_ring : ring (lp B ∞) := (lp_infty_subring B).to_ring

lemma _root_.mem_ℓp.infty_pow {f : Π i, B i} (hf : mem_ℓp f ∞) (n : ℕ) : mem_ℓp (f ^ n) ∞ :=
(lp_infty_subring B).pow_mem hf n

lemma _root_.nat_cast_mem_ℓp_infty (n : ℕ) : mem_ℓp (n : Π i, B i) ∞ :=
nat_cast_mem (lp_infty_subring B) n

lemma _root_.int_cast_mem_ℓp_infty (z : ℤ) : mem_ℓp (z : Π i, B i) ∞ :=
coe_int_mem (lp_infty_subring B) z

@[simp] lemma infty_coe_fn_one : ⇑(1 : lp B ∞) = 1 := rfl

@[simp] lemma infty_coe_fn_pow (f : lp B ∞) (n : ℕ) : ⇑(f ^ n) = f ^ n := rfl

@[simp] lemma infty_coe_fn_nat_cast (n : ℕ) : ⇑(n : lp B ∞) = n := rfl

@[simp] lemma infty_coe_fn_int_cast (z : ℤ) : ⇑(z : lp B ∞) = z := rfl

instance [nonempty I] : norm_one_class (lp B ∞) :=
{ norm_one := by simp_rw [lp.norm_eq_csupr, infty_coe_fn_one, pi.one_apply, norm_one, csupr_const]}

instance infty_normed_ring : normed_ring (lp B ∞) :=
{ .. lp.infty_ring, .. lp.non_unital_normed_ring }

end normed_ring

section normed_comm_ring

variables {I : Type*} {B : I → Type*} [Π i, normed_comm_ring (B i)] [∀ i, norm_one_class (B i)]

instance infty_comm_ring : comm_ring (lp B ∞) :=
{ mul_comm := λ f g, by { ext, simp only [lp.infty_coe_fn_mul, pi.mul_apply, mul_comm] },
  .. lp.infty_ring }

instance infty_normed_comm_ring : normed_comm_ring (lp B ∞) :=
{ .. lp.infty_comm_ring, .. lp.infty_normed_ring }

end normed_comm_ring

section algebra
variables {I : Type*} {𝕜 : Type*} {B : I → Type*}
variables [normed_field 𝕜] [Π i, normed_ring (B i)] [Π i, normed_algebra 𝕜 (B i)]

/-- A variant of `pi.algebra` that lean can't find otherwise. -/
instance _root_.pi.algebra_of_normed_algebra : algebra 𝕜 (Π i, B i) :=
@pi.algebra I 𝕜 B _ _ $ λ i, normed_algebra.to_algebra

instance _root_.pre_lp.algebra : algebra 𝕜 (pre_lp B) := _root_.pi.algebra_of_normed_algebra

variables [∀ i, norm_one_class (B i)]

lemma _root_.algebra_map_mem_ℓp_infty (k : 𝕜) : mem_ℓp (algebra_map 𝕜 (Π i, B i) k) ∞ :=
begin
  rw algebra.algebra_map_eq_smul_one,
  exact (one_mem_ℓp_infty.const_smul k : mem_ℓp (k • 1 : Π i, B i) ∞)
end

variables (𝕜 B)

/-- The `𝕜`-subalgebra of elements of `Π i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
with extra structure. -/
def _root_.lp_infty_subalgebra : subalgebra 𝕜 (pre_lp B) :=
{ carrier := {f | mem_ℓp f ∞},
  algebra_map_mem' := algebra_map_mem_ℓp_infty,
  .. lp_infty_subring B }

variables {𝕜 B}

instance infty_normed_algebra : normed_algebra 𝕜 (lp B ∞) :=
{ ..(lp_infty_subalgebra 𝕜 B).algebra,
  ..(lp.normed_space : normed_space 𝕜 (lp B ∞)) }

end algebra

section single
variables {𝕜 : Type*} [normed_field 𝕜] [Π i, normed_space 𝕜 (E i)]
variables [decidable_eq α]

/-- The element of `lp E p` which is `a : E i` at the index `i`, and zero elsewhere. -/
protected def single (p) (i : α) (a : E i) : lp E p :=
⟨ λ j, if h : j = i then eq.rec a h.symm else 0,
  begin
    refine (mem_ℓp_zero _).of_exponent_ge (zero_le p),
    refine (set.finite_singleton i).subset _,
    intros j,
    simp only [forall_exists_index, set.mem_singleton_iff, ne.def, dite_eq_right_iff,
      set.mem_set_of_eq, not_forall],
    rintros rfl,
    simp,
  end ⟩

protected lemma single_apply (p) (i : α) (a : E i) (j : α) :
  lp.single p i a j = if h : j = i then eq.rec a h.symm else 0 :=
rfl

protected lemma single_apply_self (p) (i : α) (a : E i) :
  lp.single p i a i = a :=
by rw [lp.single_apply, dif_pos rfl]

protected lemma single_apply_ne (p) (i : α) (a : E i) {j : α} (hij : j ≠ i) :
  lp.single p i a j = 0 :=
by rw [lp.single_apply, dif_neg hij]

@[simp] protected lemma single_neg (p) (i : α) (a : E i) :
  lp.single p i (- a) = - lp.single p i a :=
begin
  ext j,
  by_cases hi : j = i,
  { subst hi,
    simp [lp.single_apply_self] },
  { simp [lp.single_apply_ne p i _ hi] }
end

@[simp] protected lemma single_smul (p) (i : α) (a : E i) (c : 𝕜) :
  lp.single p i (c • a) = c • lp.single p i a :=
begin
  ext j,
  by_cases hi : j = i,
  { subst hi,
    simp [lp.single_apply_self] },
  { simp [lp.single_apply_ne p i _ hi] }
end

protected lemma norm_sum_single (hp : 0 < p.to_real) (f : Π i, E i) (s : finset α) :
  ‖∑ i in s, lp.single p i (f i)‖ ^ p.to_real = ∑ i in s, ‖f i‖ ^ p.to_real :=
begin
  refine (has_sum_norm hp (∑ i in s, lp.single p i (f i))).unique _,
  simp only [lp.single_apply, coe_fn_sum, finset.sum_apply, finset.sum_dite_eq],
  have h : ∀ i ∉ s, ‖ite (i ∈ s) (f i) 0‖ ^ p.to_real = 0,
  { intros i hi,
    simp [if_neg hi, real.zero_rpow hp.ne'], },
  have h' : ∀ i ∈ s, ‖f i‖ ^ p.to_real = ‖ite (i ∈ s) (f i) 0‖ ^ p.to_real,
  { intros i hi,
    rw if_pos hi },
  simpa [finset.sum_congr rfl h'] using has_sum_sum_of_ne_finset_zero h,
end

protected lemma norm_single (hp : 0 < p.to_real) (f : Π i, E i) (i : α) :
  ‖lp.single p i (f i)‖ = ‖f i‖ :=
begin
  refine real.rpow_left_inj_on hp.ne' (norm_nonneg' _) (norm_nonneg _) _,
  simpa using lp.norm_sum_single hp f {i},
end

protected lemma norm_sub_norm_compl_sub_single (hp : 0 < p.to_real) (f : lp E p) (s : finset α) :
  ‖f‖ ^ p.to_real - ‖f - ∑ i in s, lp.single p i (f i)‖ ^ p.to_real = ∑ i in s, ‖f i‖ ^ p.to_real :=
begin
  refine ((has_sum_norm hp f).sub (has_sum_norm hp (f - ∑ i in s, lp.single p i (f i)))).unique _,
  let F : α → ℝ := λ i, ‖f i‖ ^ p.to_real - ‖(f - ∑ i in s, lp.single p i (f i)) i‖ ^ p.to_real,
  have hF : ∀ i ∉ s, F i = 0,
  { intros i hi,
    suffices : ‖f i‖ ^ p.to_real - ‖f i - ite (i ∈ s) (f i) 0‖ ^ p.to_real = 0,
    { simpa only [F, coe_fn_sum, lp.single_apply, coe_fn_sub, pi.sub_apply, finset.sum_apply,
        finset.sum_dite_eq] using this, },
    simp only [if_neg hi, sub_zero, sub_self] },
  have hF' : ∀ i ∈ s, F i = ‖f i‖ ^ p.to_real,
  { intros i hi,
    simp only [F, coe_fn_sum, lp.single_apply, if_pos hi, sub_self, eq_self_iff_true,
      coe_fn_sub, pi.sub_apply, finset.sum_apply, finset.sum_dite_eq, sub_eq_self],
    simp [real.zero_rpow hp.ne'], },
  have : has_sum F (∑ i in s, F i) := has_sum_sum_of_ne_finset_zero hF,
  rwa [finset.sum_congr rfl hF'] at this,
end

protected lemma norm_compl_sum_single (hp : 0 < p.to_real) (f : lp E p) (s : finset α) :
  ‖f - ∑ i in s, lp.single p i (f i)‖ ^ p.to_real = ‖f‖ ^ p.to_real - ∑ i in s, ‖f i‖ ^ p.to_real :=
by linarith [lp.norm_sub_norm_compl_sub_single hp f s]

/-- The canonical finitely-supported approximations to an element `f` of `lp` converge to it, in the
`lp` topology. -/
protected lemma has_sum_single [fact (1 ≤ p)] (hp : p ≠ ⊤) (f : lp E p) :
  has_sum (λ i : α, lp.single p i (f i : E i)) f :=
begin
  have hp₀ : 0 < p := zero_lt_one.trans_le (fact.out _),
  have hp' : 0 < p.to_real := ennreal.to_real_pos hp₀.ne' hp,
  have := lp.has_sum_norm hp' f,
  rw [has_sum, metric.tendsto_nhds] at this ⊢,
  intros ε hε,
  refine (this _ (real.rpow_pos_of_pos hε p.to_real)).mono _,
  intros s hs,
  rw ← real.rpow_lt_rpow_iff dist_nonneg (le_of_lt hε) hp',
  rw dist_comm at hs,
  simp only [dist_eq_norm, real.norm_eq_abs] at hs ⊢,
  have H : ‖∑ i in s, lp.single p i (f i : E i) - f‖ ^ p.to_real
    = ‖f‖ ^ p.to_real - ∑ i in s, ‖f i‖ ^ p.to_real,
  { simpa only [coe_fn_neg, pi.neg_apply, lp.single_neg, finset.sum_neg_distrib,
      neg_sub_neg, norm_neg, _root_.norm_neg] using lp.norm_compl_sum_single hp' (-f) s },
  rw ← H at hs,
  have : |‖∑ i in s, lp.single p i (f i : E i) - f‖ ^ p.to_real|
    = ‖∑ i in s, lp.single p i (f i : E i) - f‖ ^ p.to_real,
  { simp only [real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm_eq_norm] },
  linarith
end

end single

section topology

open filter
open_locale topology uniformity

/-- The coercion from `lp E p` to `Π i, E i` is uniformly continuous. -/
lemma uniform_continuous_coe [_i : fact (1 ≤ p)] : uniform_continuous (coe : lp E p → Π i, E i) :=
begin
  have hp : p ≠ 0 := (zero_lt_one.trans_le _i.elim).ne',
  rw uniform_continuous_pi,
  intros i,
  rw normed_add_comm_group.uniformity_basis_dist.uniform_continuous_iff
    normed_add_comm_group.uniformity_basis_dist,
  intros ε hε,
  refine ⟨ε, hε, _⟩,
  rintros f g (hfg : ‖f - g‖ < ε),
  have : ‖f i - g i‖ ≤ ‖f - g‖ := norm_apply_le_norm hp (f - g) i,
  exact this.trans_lt hfg,
end

variables {ι : Type*} {l : filter ι} [filter.ne_bot l]

lemma norm_apply_le_of_tendsto {C : ℝ} {F : ι → lp E ∞} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C)
  {f : Π a, E a} (hf : tendsto (id (λ i, F i) : ι → Π a, E a) l (𝓝 f)) (a : α) :
  ‖f a‖ ≤ C :=
begin
  have : tendsto (λ k, ‖F k a‖) l (𝓝 ‖f a‖) :=
    (tendsto.comp (continuous_apply a).continuous_at hf).norm,
  refine le_of_tendsto this (hCF.mono _),
  intros k hCFk,
  exact (norm_apply_le_norm ennreal.top_ne_zero (F k) a).trans hCFk,
end

variables [_i : fact (1 ≤ p)]

include _i

lemma sum_rpow_le_of_tendsto (hp : p ≠ ∞) {C : ℝ} {F : ι → lp E p} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C)
  {f : Π a, E a} (hf : tendsto (id (λ i, F i) : ι → Π a, E a) l (𝓝 f)) (s : finset α) :
  ∑ (i : α) in s, ‖f i‖ ^ p.to_real ≤ C ^ p.to_real :=
begin
  have hp' : p ≠ 0 := (zero_lt_one.trans_le _i.elim).ne',
  have hp'' : 0 < p.to_real := ennreal.to_real_pos hp' hp,
  let G : (Π a, E a) → ℝ := λ f, ∑ a in s, ‖f a‖ ^ p.to_real,
  have hG : continuous G,
  { refine continuous_finset_sum s _,
    intros a ha,
    have : continuous (λ f : Π a, E a, f a):= continuous_apply a,
    exact this.norm.rpow_const (λ _, or.inr hp''.le) },
  refine le_of_tendsto (hG.continuous_at.tendsto.comp hf) _,
  refine hCF.mono _,
  intros k hCFk,
  refine (lp.sum_rpow_le_norm_rpow hp'' (F k) s).trans _,
  exact real.rpow_le_rpow (norm_nonneg _) hCFk hp''.le,
end

/-- "Semicontinuity of the `lp` norm": If all sufficiently large elements of a sequence in `lp E p`
 have `lp` norm `≤ C`, then the pointwise limit, if it exists, also has `lp` norm `≤ C`. -/
lemma norm_le_of_tendsto {C : ℝ} {F : ι → lp E p} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C) {f : lp E p}
  (hf : tendsto (id (λ i, F i) : ι → Π a, E a) l (𝓝 f)) :
  ‖f‖ ≤ C :=
begin
  obtain ⟨i, hi⟩ := hCF.exists,
  have hC : 0 ≤ C := (norm_nonneg _).trans hi,
  unfreezingI { rcases eq_top_or_lt_top p with rfl | hp },
  { apply norm_le_of_forall_le hC,
    exact norm_apply_le_of_tendsto hCF hf, },
  { have : 0 < p := zero_lt_one.trans_le _i.elim,
    have hp' : 0 < p.to_real := ennreal.to_real_pos this.ne' hp.ne,
    apply norm_le_of_forall_sum_le hp' hC,
    exact sum_rpow_le_of_tendsto hp.ne hCF hf, }
end

/-- If `f` is the pointwise limit of a bounded sequence in `lp E p`, then `f` is in `lp E p`. -/
lemma mem_ℓp_of_tendsto {F : ι → lp E p} (hF : metric.bounded (set.range F)) {f : Π a, E a}
  (hf : tendsto (id (λ i, F i) : ι → Π a, E a) l (𝓝 f)) :
  mem_ℓp f p :=
begin
  obtain ⟨C, hC, hCF'⟩ := hF.exists_pos_norm_le,
  have hCF : ∀ k, ‖F k‖ ≤ C := λ k, hCF' _ ⟨k, rfl⟩,
  unfreezingI { rcases eq_top_or_lt_top p with rfl | hp },
  { apply mem_ℓp_infty,
    use C,
    rintros _ ⟨a, rfl⟩,
    refine norm_apply_le_of_tendsto (eventually_of_forall hCF) hf a, },
  { apply mem_ℓp_gen',
    exact sum_rpow_le_of_tendsto hp.ne (eventually_of_forall hCF) hf },
end

/-- If a sequence is Cauchy in the `lp E p` topology and pointwise convergent to a element `f` of
`lp E p`, then it converges to `f` in the `lp E p` topology. -/
lemma tendsto_lp_of_tendsto_pi {F : ℕ → lp E p} (hF : cauchy_seq F) {f : lp E p}
  (hf : tendsto (id (λ i, F i) : ℕ → Π a, E a) at_top (𝓝 f)) :
  tendsto F at_top (𝓝 f) :=
begin
  rw metric.nhds_basis_closed_ball.tendsto_right_iff,
  intros ε hε,
  have hε' : {p : (lp E p) × (lp E p) | ‖p.1 - p.2‖ < ε} ∈ 𝓤 (lp E p),
  { exact normed_add_comm_group.uniformity_basis_dist.mem_of_mem hε },
  refine (hF.eventually_eventually hε').mono _,
  rintros n (hn : ∀ᶠ l in at_top, ‖(λ f, F n - f) (F l)‖ < ε),
  refine norm_le_of_tendsto (hn.mono (λ k hk, hk.le)) _,
  rw tendsto_pi_nhds,
  intros a,
  exact (hf.apply a).const_sub (F n a),
end

variables [Π a, complete_space (E a)]

instance : complete_space (lp E p) :=
metric.complete_of_cauchy_seq_tendsto
begin
  intros F hF,
  -- A Cauchy sequence in `lp E p` is pointwise convergent; let `f` be the pointwise limit.
  obtain ⟨f, hf⟩ := cauchy_seq_tendsto_of_complete (uniform_continuous_coe.comp_cauchy_seq hF),
  -- Since the Cauchy sequence is bounded, its pointwise limit `f` is in `lp E p`.
  have hf' : mem_ℓp f p := mem_ℓp_of_tendsto hF.bounded_range hf,
  -- And therefore `f` is its limit in the `lp E p` topology as well as pointwise.
  exact ⟨⟨f, hf'⟩, tendsto_lp_of_tendsto_pi hF hf⟩
end

end topology

end lp
