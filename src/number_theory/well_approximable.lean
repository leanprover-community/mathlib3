/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import dynamics.ergodic.add_circle
import measure_theory.covering.liminf_limsup
import data.nat.totient

/-!
# Well-approximable numbers and Gallagher's ergodic theorem

Gallagher's ergodic theorem is a result in metric number theory. It thus belongs to that branch of
mathematics concerning arithmetic properties of real numbers which hold almost eveywhere with
respect to the Lebesgue measure.

Gallagher's theorem concerns the approximation of real numbers by rational numbers. The input is a
sequence of distances `δ₁, δ₂, ...`, and the theorem concerns the set of real numbers `x` for which
there is an infinity of solutions to:
$$
  |x - m/n| < δₙ,
$$
where the rational number `m/n` is in lowest terms. The result is that for any `δ`, this set is
either almost all `x` or almost no `x`.

This result was proved by Gallagher in 1959
[P. Gallagher, *Approximation by reduced fractions*](Gallagher1961). It is formalised here as
`add_circle.add_well_approximable_ae_empty_or_univ` except with `x` belonging to the circle `ℝ ⧸ ℤ`
since this turns out to be more natural.

Given a particular `δ`, the Duffin-Schaeffer conjecture (now a theorem) gives a criterion for
deciding which of the two cases in the conclusion of Gallagher's theorem actually occurs. It was
proved by Koukoulopoulos and Maynard in 2019
[D. Koukoulopoulos, J. Maynard, *On the Duffin-Schaeffer conjecture*](KoukoulopoulosMaynard2020).
We do *not* include a formalisation of the Koukoulopoulos-Maynard result here.

## Main definitions and results:

 * `approx_order_of`: in a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approx_order_of A n δ`
   is the set of elements within a distance `δ` of a point of order `n`.
 * `well_approximable`: in a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`,
   `well_approximable A δ` is the limsup as `n → ∞` of the sets `approx_order_of A n δₙ`. Thus, it
   is the set of points that lie in infinitely many of the sets `approx_order_of A n δₙ`.
 * `add_circle.add_well_approximable_ae_empty_or_univ`: *Gallagher's ergodic theorem* says that for
   for the (additive) circle `𝕊`, for any sequence of distances `δ`, the set
   `add_well_approximable 𝕊 δ` is almost empty or almost full.

## TODO:

The hypothesis `hδ` in `add_circle.add_well_approximable_ae_empty_or_univ` can be dropped.
An elementary (non-measure-theoretic) argument shows that if `¬ hδ` holds then
`add_well_approximable 𝕊 δ = univ` (provided `δ` is non-negative).
-/

open set filter function metric measure_theory
open_locale measure_theory topology pointwise

/-- In a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approx_order_of A n δ` is the set of
elements within a distance `δ` of a point of order `n`. -/
@[to_additive approx_add_order_of "In a seminormed additive group `A`, given `n : ℕ` and `δ : ℝ`,
`approx_add_order_of A n δ` is the set of elements within a distance `δ` of a point of order `n`."]
def approx_order_of (A : Type*) [seminormed_group A] (n : ℕ) (δ : ℝ) : set A :=
thickening δ {y | order_of y = n}

@[to_additive mem_approx_add_order_of_iff]
lemma mem_approx_order_of_iff {A : Type*} [seminormed_group A] {n : ℕ} {δ : ℝ} {a : A} :
  a ∈ approx_order_of A n δ ↔ ∃ (b : A), order_of b = n ∧ a ∈ ball b δ :=
by simp only [approx_order_of, thickening_eq_bUnion_ball, mem_Union₂, mem_set_of_eq, exists_prop]

/-- In a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`, `well_approximable A δ`
is the limsup as `n → ∞` of the sets `approx_order_of A n δₙ`. Thus, it is the set of points that
lie in infinitely many of the sets `approx_order_of A n δₙ`. -/
@[to_additive add_well_approximable "In a seminormed additive group `A`, given a sequence of
distances `δ₁, δ₂, ...`, `add_well_approximable A δ` is the limsup as `n → ∞` of the sets
`approx_add_order_of A n δₙ`. Thus, it is the set of points that lie in infinitely many of the sets
`approx_add_order_of A n δₙ`."]
def well_approximable (A : Type*) [seminormed_group A] (δ : ℕ → ℝ) : set A :=
blimsup (λ n, approx_order_of A n (δ n)) at_top (λ n, 0 < n)

@[to_additive mem_add_well_approximable_iff]
lemma mem_well_approximable_iff {A : Type*} [seminormed_group A] {δ : ℕ → ℝ} {a : A} :
  a ∈ well_approximable A δ ↔ a ∈ blimsup (λ n, approx_order_of A n (δ n)) at_top (λ n, 0 < n) :=
iff.rfl

namespace approx_order_of

variables {A : Type*} [seminormed_comm_group A] {a : A} {m n : ℕ} (δ : ℝ)

@[to_additive]
lemma image_pow_subset_of_coprime (hm : 0 < m) (hmn : n.coprime m) :
  (λ y, y^m) '' (approx_order_of A n δ) ⊆ approx_order_of A n (m * δ) :=
begin
  rintros - ⟨a, ha, rfl⟩,
  obtain ⟨b, hb, hab⟩ := mem_approx_order_of_iff.mp ha,
  replace hb : b^m ∈ {u : A | order_of u = n}, { rw ← hb at hmn ⊢, exact order_of_pow_coprime hmn },
  apply ball_subset_thickening hb ((m : ℝ) • δ),
  convert pow_mem_ball hm hab using 1,
  simp only [nsmul_eq_mul, algebra.id.smul_eq_mul],
end

@[to_additive]
lemma image_pow_subset (n : ℕ) (hm : 0 < m) :
  (λ y, y^m) '' (approx_order_of A (n * m) δ) ⊆ approx_order_of A n (m * δ) :=
begin
  rintros - ⟨a, ha, rfl⟩,
  obtain ⟨b, hb : order_of b = n * m, hab : a ∈ ball b δ⟩ := mem_approx_order_of_iff.mp ha,
  replace hb : b^m ∈ {y : A | order_of y = n},
  { rw [mem_set_of_eq, order_of_pow' b hm.ne', hb, nat.gcd_mul_left_left, n.mul_div_cancel hm], },
  apply ball_subset_thickening hb (m * δ),
  convert pow_mem_ball hm hab,
  simp only [nsmul_eq_mul],
end

@[to_additive]
lemma smul_subset_of_coprime (han : (order_of a).coprime n) :
  a • approx_order_of A n δ ⊆ approx_order_of A ((order_of a) * n) δ :=
begin
  simp_rw [approx_order_of, thickening_eq_bUnion_ball, ← image_smul, image_Union₂,
    image_smul, smul_ball'', smul_eq_mul, mem_set_of_eq],
  refine Union₂_subset_iff.mpr (λ b hb c hc, _),
  simp only [mem_Union, exists_prop],
  refine ⟨a * b, _, hc⟩,
  rw ← hb at ⊢ han,
  exact (commute.all a b).order_of_mul_eq_mul_order_of_of_coprime han,
end

@[to_additive vadd_eq_of_mul_dvd]
lemma smul_eq_of_mul_dvd (hn : 0 < n) (han : (order_of a)^2 ∣ n) :
  a • approx_order_of A n δ = approx_order_of A n δ :=
begin
  simp_rw [approx_order_of, thickening_eq_bUnion_ball, ← image_smul, image_Union₂,
    image_smul, smul_ball'', smul_eq_mul, mem_set_of_eq],
  replace han : ∀ {b : A}, order_of b = n → order_of (a * b) = n,
  { intros b hb,
    rw ← hb at han hn,
    rw sq at han,
    rwa [(commute.all a b).order_of_mul_eq_right_of_forall_prime_mul_dvd (order_of_pos_iff.mp hn)
      (λ p hp hp', dvd_trans (mul_dvd_mul_right hp' $ order_of a) han)], },
  let f : {b : A | order_of b = n} → {b : A | order_of b = n} := λ b, ⟨a * b, han b.property⟩,
  have hf : surjective f,
  { rintros ⟨b, hb⟩,
    refine ⟨⟨a⁻¹ * b, _⟩, _⟩,
    { rw [mem_set_of_eq, ← order_of_inv, mul_inv_rev, inv_inv, mul_comm],
      apply han,
      simpa, },
    { simp only [subtype.mk_eq_mk, subtype.coe_mk, mul_inv_cancel_left], }, },
  simpa only [f, mem_set_of_eq, subtype.coe_mk, Union_coe_set] using
    hf.Union_comp (λ b, ball (b : A) δ),
end

end approx_order_of

namespace unit_add_circle

lemma mem_approx_add_order_of_iff {δ : ℝ} {x : unit_add_circle} {n : ℕ} (hn : 0 < n) :
  x ∈ approx_add_order_of unit_add_circle n δ ↔
  ∃ m < n, gcd m n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < δ :=
begin
  haveI := real.fact_zero_lt_one,
  simp only [mem_approx_add_order_of_iff, mem_set_of_eq, ball, exists_prop, dist_eq_norm,
    add_circle.add_order_of_eq_pos_iff hn, mul_one],
  split,
  { rintros ⟨y, ⟨m, hm₁, hm₂, rfl⟩, hx⟩, exact ⟨m, hm₁, hm₂, hx⟩, },
  { rintros ⟨m, hm₁, hm₂, hx⟩, exact ⟨↑((m : ℝ) / n), ⟨m, hm₁, hm₂, rfl⟩, hx⟩, },
end

lemma mem_add_well_approximable_iff (δ : ℕ → ℝ) (x : unit_add_circle) :
  x ∈ add_well_approximable unit_add_circle δ ↔
  {n : ℕ | ∃ m < n, gcd m n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < δ n}.infinite :=
begin
  simp only [mem_add_well_approximable_iff, ← nat.cofinite_eq_at_top, cofinite.blimsup_set_eq,
    mem_set_of_eq],
  refine iff_of_eq (congr_arg set.infinite $ ext (λ n, ⟨λ hn, _, λ hn, _⟩)),
  { exact (mem_approx_add_order_of_iff hn.1).mp hn.2, },
  { have h : 0 < n := by { obtain ⟨m, hm₁, hm₂, hm₃⟩ := hn, exact pos_of_gt hm₁, },
    exact ⟨h, (mem_approx_add_order_of_iff h).mpr hn⟩, },
end

end unit_add_circle

namespace add_circle

variables {T : ℝ} [hT : fact (0 < T)]
include hT

local notation a `∤` b := ¬ a ∣ b
local notation a `∣∣` b := (a ∣ b) ∧ (a*a ∤ b)
local notation `𝕊` := add_circle T

/-- *Gallagher's ergodic theorem* on Diophantine approximation. -/
theorem add_well_approximable_ae_empty_or_univ (δ : ℕ → ℝ) (hδ : tendsto δ at_top (𝓝 0)) :
  (∀ᵐ x, ¬ add_well_approximable 𝕊 δ x) ∨ ∀ᵐ x, add_well_approximable 𝕊 δ x :=
begin
  /- Sketch of proof:

  Let `E := add_well_approximable 𝕊 δ`. For each prime `p : ℕ`, we can partition `E` into three
  pieces `E = (A p) ∪ (B p) ∪ (C p)` where:
    `A p = blimsup (approx_add_order_of 𝕊 n (δ n)) at_top (λ n, 0 < n ∧ (p ∤ n))`
    `B p = blimsup (approx_add_order_of 𝕊 n (δ n)) at_top (λ n, 0 < n ∧ (p ∣∣ n))`
    `C p = blimsup (approx_add_order_of 𝕊 n (δ n)) at_top (λ n, 0 < n ∧ (p*p ∣ n))`.
  (In other words, `A p` is the set of points `x` for which there exist infinitely-many `n` such
  that `x` is within a distance `δ n` of a point of order `n` and `p ∤ n`. Similarly for `B`, `C`.)

  These sets have the following key properties:
    1. `A p` is almost invariant under the ergodic map `y ↦ p • y`
    2. `B p` is almost invariant under the ergodic map `y ↦ p • y + 1/p`
    3. `C p` is invariant under the map `y ↦ y + 1/p`
  To prove 1 and 2 we need the key result `blimsup_thickening_mul_ae_eq` but 3 is elementary.

  It follows from `add_circle.ergodic_nsmul_add` and `ergodic.ae_empty_or_univ_of_image_ae_le` that
  if either `A p` or `B p` is not almost empty for any `p`, then it is almost full and thus so is
  `E`. We may therefore assume that both `A p` and `B p` are almost empty for all `p`. We thus have
  `E` is almost equal to `C p` for every prime. Combining this with 3 we find that `E` is almost
  invariant under the map `y ↦ y + 1/p` for every prime `p`. The required result then follows from
  `add_circle.ae_empty_or_univ_of_forall_vadd_ae_eq_self`. -/
  letI : semilattice_sup nat.primes := nat.subtype.semilattice_sup _,
  set μ : measure 𝕊 := volume,
  set u : nat.primes → 𝕊 := λ p, ↑(((↑(1 : ℕ) : ℝ) / p) * T),
  have hu₀ : ∀ (p : nat.primes), add_order_of (u p) = (p : ℕ),
  { rintros ⟨p, hp⟩, exact add_order_of_div_of_gcd_eq_one hp.pos (gcd_one_left p), },
  have hu : tendsto (add_order_of ∘ u) at_top at_top,
  { rw (funext hu₀ : add_order_of ∘ u = coe),
    have h_mono : monotone (coe : nat.primes → ℕ) := λ p q hpq, hpq,
    refine h_mono.tendsto_at_top_at_top (λ n, _),
    obtain ⟨p, hp, hp'⟩ := n.exists_infinite_primes,
    exact ⟨⟨p, hp'⟩, hp⟩, },
  set E := add_well_approximable 𝕊 δ,
  set X : ℕ → set 𝕊 := λ n, approx_add_order_of 𝕊 n (δ n),
  set A : ℕ → set 𝕊 := λ p, blimsup X at_top (λ n, 0 < n ∧ (p ∤ n)),
  set B : ℕ → set 𝕊 := λ p, blimsup X at_top (λ n, 0 < n ∧ (p ∣∣ n)),
  set C : ℕ → set 𝕊 := λ p, blimsup X at_top (λ n, 0 < n ∧ (p^2 ∣ n)),
  have hA₀ : ∀ p, measurable_set (A p) :=
    λ p, measurable_set.measurable_set_blimsup (λ n hn, is_open_thickening.measurable_set),
  have hB₀ : ∀ p, measurable_set (B p) :=
    λ p, measurable_set.measurable_set_blimsup (λ n hn, is_open_thickening.measurable_set),
  have hE₀ : null_measurable_set E μ,
  { refine (measurable_set.measurable_set_blimsup
      (λ n hn, is_open.measurable_set _)).null_measurable_set,
    exact is_open_thickening, },
  have hE₁ : ∀ p, E = (A p) ∪ (B p) ∪ (C p),
  { intros p,
    simp only [E, add_well_approximable, ← blimsup_or_eq_sup, ← and_or_distrib_left, ← sup_eq_union,
      sq],
    congr,
    refine funext (λ n, propext $ iff_self_and.mpr (λ hn, _)),
    -- `tauto` can finish from here but unfortunately it's very slow.
    simp only [(em (p ∣ n)).symm, (em (p*p ∣ n)).symm, or_and_distrib_left, or_true, true_and,
      or_assoc], },
  have hE₂ : ∀ (p : nat.primes), A p =ᵐ[μ] (∅ : set 𝕊) ∧ B p =ᵐ[μ] (∅ : set 𝕊) → E =ᵐ[μ] C p,
  { rintros p ⟨hA, hB⟩,
    rw hE₁ p,
    exact union_ae_eq_right_of_ae_eq_empty ((union_ae_eq_right_of_ae_eq_empty hA).trans hB), },
  have hA : ∀ (p : nat.primes), A p =ᵐ[μ] (∅ : set 𝕊) ∨ A p =ᵐ[μ] univ,
  { rintros ⟨p, hp⟩,
    let f : 𝕊 → 𝕊 := λ y, (p : ℕ) • y,
    suffices : f '' (A p) ⊆
      blimsup (λ n, approx_add_order_of 𝕊 n (p * δ n)) at_top (λ n, 0 < n ∧ (p ∤ n)),
    { apply (ergodic_nsmul hp.one_lt).ae_empty_or_univ_of_image_ae_le (hA₀ p),
      apply (has_subset.subset.eventually_le this).congr eventually_eq.rfl,
      exact blimsup_thickening_mul_ae_eq μ
        (λ n, 0 < n ∧ (p ∤ n)) (λ n, {y | add_order_of y = n}) (nat.cast_pos.mpr hp.pos) _ hδ, },
    refine (Sup_hom.set_image f).apply_blimsup_le.trans (mono_blimsup $ λ n hn, _),
    replace hn := nat.coprime_comm.mp (hp.coprime_iff_not_dvd.2 hn.2),
    exact approx_add_order_of.image_nsmul_subset_of_coprime (δ n) hp.pos hn, },
  have hB : ∀ (p : nat.primes), B p =ᵐ[μ] (∅ : set 𝕊) ∨ B p =ᵐ[μ] univ,
  { rintros ⟨p, hp⟩,
    let x := u ⟨p, hp⟩,
    let f : 𝕊 → 𝕊 := λ y, p • y + x,
    suffices : f '' (B p) ⊆
      blimsup (λ n, approx_add_order_of 𝕊 n (p * δ n)) at_top (λ n, 0 < n ∧ (p ∣∣ n)),
    { apply (ergodic_nsmul_add x hp.one_lt).ae_empty_or_univ_of_image_ae_le (hB₀ p),
      apply (has_subset.subset.eventually_le this).congr eventually_eq.rfl,
      exact blimsup_thickening_mul_ae_eq μ
        (λ n, 0 < n ∧ (p ∣∣ n)) (λ n, {y | add_order_of y = n}) (nat.cast_pos.mpr hp.pos) _ hδ, },
    refine (Sup_hom.set_image f).apply_blimsup_le.trans (mono_blimsup _),
    rintros n ⟨hn, h_div, h_ndiv⟩,
    have h_cop : (add_order_of x).coprime (n/p),
    { obtain ⟨q, rfl⟩ := h_div,
      rw [hu₀, subtype.coe_mk, hp.coprime_iff_not_dvd, q.mul_div_cancel_left hp.pos],
      exact λ contra, h_ndiv (mul_dvd_mul_left p contra), },
    replace h_div : n / p * p = n := nat.div_mul_cancel h_div,
    have hf : f = (λ y, x + y) ∘ (λ y, p • y), { ext, simp [add_comm x], },
    simp_rw [comp_app],
    rw [le_eq_subset, Sup_hom.set_image_to_fun, hf, image_comp],
    have := @monotone_image 𝕊 𝕊 (λ y, x + y),
    specialize this (approx_add_order_of.image_nsmul_subset (δ n) (n/p) hp.pos),
    simp only [h_div] at this ⊢,
    refine this.trans _,
    convert approx_add_order_of.vadd_subset_of_coprime (p * δ n) h_cop,
    simp only [hu₀, subtype.coe_mk, h_div, mul_comm p], },
  change (∀ᵐ x, x ∉ E) ∨ E ∈ volume.ae,
  rw [← eventually_eq_empty, ← eventually_eq_univ],
  have hC : ∀ (p : nat.primes), (u p) +ᵥ C p = C p,
  { intros p,
    let e := (add_action.to_perm (u p) : equiv.perm 𝕊).to_order_iso_set,
    change e (C p) = C p,
    rw [e.apply_blimsup, ← hu₀ p],
    exact blimsup_congr (eventually_of_forall $ λ n hn,
      approx_add_order_of.vadd_eq_of_mul_dvd (δ n) hn.1 hn.2), },
  by_cases h : ∀ (p : nat.primes), A p =ᵐ[μ] (∅ : set 𝕊) ∧ B p =ᵐ[μ] (∅ : set 𝕊),
  { replace h : ∀ (p : nat.primes), ((u p) +ᵥ E : set _) =ᵐ[μ] E,
    { intros p,
      replace hE₂ : E =ᵐ[μ] C p := hE₂ p (h p),
      have h_qmp : measure_theory.measure.quasi_measure_preserving ((+ᵥ) (-u p)) μ μ :=
        (measure_preserving_vadd _ μ).quasi_measure_preserving,
      refine (h_qmp.vadd_ae_eq_of_ae_eq (u p) hE₂).trans (ae_eq_trans _ hE₂.symm),
      rw hC, },
    exact ae_empty_or_univ_of_forall_vadd_ae_eq_self hE₀ h hu, },
  { right,
    simp only [not_forall, not_and_distrib] at h,
    obtain ⟨p, hp⟩ := h,
    rw hE₁ p,
    cases hp,
    { cases hA p, { contradiction, },
      simp only [h, union_ae_eq_univ_of_ae_eq_univ_left], },
    { cases hB p, { contradiction, },
      simp only [h, union_ae_eq_univ_of_ae_eq_univ_left, union_ae_eq_univ_of_ae_eq_univ_right], } },
end

end add_circle
